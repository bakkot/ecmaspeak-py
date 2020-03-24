#!/usr/bin/python3

# LR_Parser.py:
# Defines a class (LR_Parser) that, given a context-free grammar,
# constructs an LR(1) or SLR(1) parser (possibly with conflicts),
# which can then be used to parse input,
# either 'canonically' or in a GLR style.
#
# Copyright (C) 2016  J. Michael Dyck <jmdyck@ibiblio.org>

import re, pprint, sys, time, pdb
from collections import defaultdict, OrderedDict

class ParserConflict(Exception):
    pass

class ParsingError(Exception):
    def __init__(self, posn, expecting):
        self.posn = posn
        self.expecting = expecting

class TooManyHeadsError(Exception):
    def __init__(self, posn):
        self.posn = posn

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class LR_Parser:
    def __init__(self, style, productions, conflict_handling):
        t_start = time.time()
        assert style in ['LR(1)', 'SLR(1)']
        assert conflict_handling in ['exception', 'stderr', 'silent']

        self.style = style
        self.productions = productions
        self.conflict_handling = conflict_handling

        # `productions` is a sequence of (lhs, rhs) pairs,
        # where `lhs` is a symbol and `rhs` is a sequence of symbols.
        # 
        # The nonterminals of the grammar are those symbols
        # that appear as a `lhs` in some production,
        # and the terminals are any symbol that appears in a `rhs`
        # that isn't a nonterminal.
        # As far as the parser is concerned, symbols are opaque:
        # the only requirement is that they be hashable (and comparable?).
        #
        # The first production must be of the form:
        #     (Start, [Goal, End])
        # where:
        #     Start must not appear elsewhere in productions.
        #     Goal must be a nonterminal.
        #     End must be a terminal that does not appear elsewhere in productions.
        #         It will be used during parsing to signal end-of-input.
        #
        # (For those familiar with parser theory, the first production
        # is, in effect, the production that you would add to construct
        # the "augmented grammar".)

        self.nt_ = OrderedDict()
        for (i, production) in enumerate(productions):
            (lhs, rhs) = production
            if lhs not in self.nt_:
                self.nt_[lhs] = NonterminalInfo(lhs)
            self.nt_[lhs].prods_with_that_lhs.append( (i, rhs) )


        abort = False
        for (lhs, rhs) in productions:
            for symbol in rhs:
                if not hashable(symbol):
                    print("symbol is not hashable:", symbol, file=sys.stderr)
                    abort = True
        if abort:
            print("aborting due to above errors")
            sys.exit()

        # Identify the terminals
        self.terminals = OrderedDict()
        for (lhs, rhs) in productions:
            for symbol in rhs:
                hash(symbol)
                if symbol not in self.nt_:
                    # it's a terminal
                    if symbol not in self.terminals:
                        self.terminals[symbol] = 0
                    self.terminals[symbol] += 1

        # Enforce the requirements on the first production:
        aug_prodn = productions[0]
        (self.start_symbol, rhs) = aug_prodn
        assert len(rhs) == 2, aug_prodn
        (self.goal_symbol, self.eoi_symbol) = rhs
        #
        # Start must not appear elsewhere in productions:
        assert len(self.nt_[self.start_symbol].prods_with_that_lhs) == 1
        assert all(symbol != self.start_symbol for (lhs,rhs) in productions for symbol in rhs)
        #
        # Goal must be a nonterminal
        assert self.goal_symbol in self.nt_
        #
        # End must be a terminal that does not appear elsewhere.
        assert self.terminals[self.eoi_symbol] == 1

        self._calc_first_sets()
        if self.style == 'SLR(1)':
            self._calc_follow_sets()
        self._construct()

        t_end = time.time()
        # print("LR_Parser construction took %d seconds" % (t_end-t_start), file=sys.stderr)
        # it's usully zero, so don't bother

    # --------------------------------------------------------------------------

    def _is_a_nonterminal(self, X):
        return X in self.nt_

    def _is_a_terminal(self, X):
        return not self._is_a_nonterminal(X)

    # --------------------------------------------------------------------------

    def _calc_first_sets(self):
        while True:
            nothing_changed = True
            for (X, X_info) in self.nt_.items():
                for (_, rhs) in X_info.prods_with_that_lhs:
                    for f in list(self._first(rhs)):
                        if f not in X_info.first_set:
                            X_info.first_set.add(f)
                            nothing_changed = False
            if nothing_changed:
                break

        if 0:
            print("First:")
            for (X, X_info) in self.nt_.items():
                print(X, X_info.first_set)

    def _first(self, symbols):
        # if not isinstance(symbols, list): symbols = [symbols]
        result = set()
        for sym in symbols:
            fs = self._first_for_symbol(sym)
            if None not in fs:
                result |= fs
                return result
            else:
                result |= (fs - set([None]))
        result.add(None)
        return result

    def _first_for_symbol(self, X):
        if self._is_a_terminal(X):
            return set([X])
        else:
            return self.nt_[X].first_set

    # --------------------------------------------------------------------------

    def _calc_follow_sets(self):
        # self.nt_[self.start_symbol].follow_set.add(self.eoi_symbol)

        while True:
            nothing_changed = True
            for (A, A_info) in self.nt_.items():
                for (_, rhs) in A_info.prods_with_that_lhs:
                    for (i,B) in enumerate(rhs):
                        if self._is_a_nonterminal(B):
                            B_info = self.nt_[B]
                            beta = rhs[i+1:]
                            if beta == []:
                                follows_to_add = A_info.follow_set
                            else:
                                follows_to_add = self._first(beta)
                                if None in follows_to_add:
                                    follows_to_add.remove(None)
                                    follows_to_add.update(A_info.follow_set)

                            n_before = len(B_info.follow_set)
                            B_info.follow_set.update(follows_to_add)
                            n_after = len(B_info.follow_set)
                            if n_before != n_after:
                                nothing_changed = False

            if nothing_changed:
                break

        if 0:
            print("Follow:")
            for (X, X_info) in self.nt_.items():
                print(X, X_info.follow_set)

    # --------------------------------------------------------------------------

    def _construct(self):
        self._n_conflicts = 0
        self._state_for_kernel_ = OrderedDict()
        self._open_states = []

        if self.style == 'SLR(1)':
            # Lookaheads aren't part of items,
            # they're calculated after the sets-of-items construction.
            i_lookahead = None
        else:
            i_lookahead = None # self.eoi_symbol

        start_rhs = tuple(self.productions[0][1])
        start_item = (0, self.start_symbol, start_rhs, 0, i_lookahead)
        self.start_state = self._ensure_state_for_kernel( [start_item], [] )

        while self._open_states:
            state = self._open_states.pop(0)
            state.close()
        
        print("%s machine constructed with %d states and %d conflicts" %
            (self.style, len(self._state_for_kernel_), self._n_conflicts),
            file=sys.stderr)

    def _ensure_state_for_kernel(self, kernel, accessor):
        kernel = tuple(sorted(kernel)) # or frozenset(kernel) ?
        if kernel in self._state_for_kernel_:
            state = self._state_for_kernel_[kernel]
        else:
            state_number = len(self._state_for_kernel_)
            state = State(self, kernel, accessor, state_number)
            self._state_for_kernel_[kernel] = state
            self._open_states.append(state)
        return state

    # --------------------------------------------------------------------------

    def print(self):
        print("Parser:")
        for state in self._state_for_kernel_.values():
            state.print()

    def print_table(self):
        # Print a table that approximates the format
        # of the parsing tables in the dragon book.
        symbols_ = {
            'terminal': list(self.terminals.keys()),
            'nonterminal': list(self.nt_.keys())
        }

        print("       ", end='')
        for which in ['terminal', 'nonterminal']:
            for symbol in symbols_[which]:
                print(" %-3s" % symbol, end='')
            print(" |", end='')
        print()
        for state in self._state_for_kernel_.values():
            print("  %2d | " % state.number, end='')
            for which in ['terminal', 'nonterminal']:
                for symbol in symbols_[which]:
                    if symbol in state.actions_[which]:
                        actions = state.actions_[which][symbol]
                        assert len(actions) >= 1
                        if len(actions) == 1:
                            [action] = actions
                            if action[0] == 'accept':
                                print(" acc", end='')
                            elif action[0] == 'shift_and_go_to':
                                print(" s%-2d" % action[1].number, end='')
                            elif action[0] == 'reduce':
                                (_, pi, rhs_len, lhs_nt) = action
                                print(" r%-2d" % pi, end='')
                            else:
                                assert 0
                        else:
                            print(" !!!", end='')
                    else:
                        print("    ", end='')
                print(" |", end='')
            print()

    # --------------------------------------------------------------------------

    def parse(self, terminal_matcher, reducer, start_posn=None, trace=False):
        # (Caveat: I haven't used this function in a while.)
        #
        # `terminal_matcher` must be a callable that takes 2 parameters:
        #   - a position in the source, and
        #   - a terminal symbol from self.productions.
        # and operates as follows:
        #     If, at the given position in the source,
        #     an instance of the given terminal symbol exists,
        #     then return a tuple/list consisting of:
        #       - the position at which the instance ends, and
        #       - a token object representing that instance.
        #
        #     If an instance of the given terminal symbol is not present,
        #     then return a falsy value (e.g. None).
        #
        # Note that this allows for the parser state to 'drive' the lexer,
        # unlike the conventional situation where the lexer
        # can generate a token-stream independent of the parser.
        # (Though it can handle that too.)
        #
        # ---------
        # `reducer` must be a callable that returns a new parent node,
        # given 3 parameters:
        #   - the index of the production by which to reduce,
        #   - a sequence of tokens or trees, one for each child, and
        #   - a start-position in the source.

        if start_posn is None: start_posn = 0

        stack = [ self.start_state ]
        curr_posn = start_posn
        while True:
            state = stack[-1]
            matches = []
            for T in state.actions_['terminal'].keys():
                match_result = terminal_matcher(curr_posn, T)
                if match_result:
                    (token_end_posn, token) = match_result
                    assert curr_posn <= token_end_posn
                    matches.append( (T, token_end_posn) )
            if matches == []:
                expecteds = sorted(state.actions_['terminal'].keys())

                raise ParsingError(curr_posn, expecteds)
            elif len(matches) == 1:
                [match] = matches
                (T, token_end_posn) = match
            else:
                # multiple matches.
                # XXX Should we complain, or pick the longest?
                max_tep = max( token_end_posn for (T,token_end_posn) in matches )
                Xs_with_max_tep = [ T for (T,token_end_posn) in matches if token_end_posn == max_tep ]
                assert len(Xs_with_max_tep) == 1, Xs_with_max_tep
                [T] = Xs_with_max_tep
                token_end_posn = max_tep

            # print(T, 'matches', repr(token))
            [action] = state.actions_['terminal'][T]
            if action[0] == 'accept':
                assert len(stack) == 3
                (_, node, _) = stack
                return node

            elif action[0] == 'shift_and_go_to':
                # print("shift %r and go to %s" % (token, action[1]))
                next_state = action[1]
                curr_posn = token_end_posn
                stack.append(token)
                stack.append(next_state)

            elif action[0] == 'reduce':
                (_, pi, rhs_len, lhs_nt) = action
                # print("reduce %d symbols to %s" % (rhs_len, lhs_nt))
                children = []
                for i in range(rhs_len):
                    _state = stack.pop()
                    _child = stack.pop()
                    children.insert(0, _child)
                new_tree = reducer(pi, children, curr_posn)

                back_state = stack[-1]
                [back_action] = back_state.actions_['nonterminal'][lhs_nt]
                assert back_action[0] == 'shift_and_go_to'
                # So we shift the instance of lhs_nt.
                # print("  ... and go to %s" % back_action[1])
                stack.append(new_tree)
                stack.append(back_action[1])
                # but curr_posn doesn't change!

            else:
                assert 0, action

    # --------------------------------------------------------------------------

    def gparse(self, terminal_matcher, reducer, start_posn):
        # `terminal_matcher` must be a callable that takes 2 parameters:
        #   - a position in the source, and
        #   - an iterable of terminal symbols.
        # and returns an iterable of items as follows:
        #
        #     For each of the given terminal symbols,
        #     if an instance of the given terminal symbol exists
        #     at the given position in the source,
        #     yield/return a tuple/list consisting of:
        #         - the terminal symbol,
        #         - the position at which the instance ends, and
        #         - a token object representing that instance.
        #
        # ---------
        # `reducer` must be a callable that returns a new parent node, given 4 parameters:
        #   - the index of the production by which to reduce,
        #   - a sequence of tokens or trees, one for each child,
        #   - a start-position in the source, and
        #   - an end-position in the source
        #
        # ---------
        # The gparse function doesn't care about the implementation of tokens or trees,
        # so the caller can 'implement' them as None if it's not interested in
        # building a parse tree.

        class PNode:
            def __init__(self, back_pnode, down_pnode, down_len, symbol, tree, posn, state):
                # From back_pnode, on shifting symbol, transit to state.
                self.back_pnode = back_pnode
                self.down_pnode = down_pnode
                self.down_len = down_len
                self.symbol = symbol
                self.tree = tree
                self.posn = posn
                self.state = state

            def go_back(self, n):
                trees = []
                pnode = self
                for i in range(n):
                    trees.insert(0, pnode.tree)
                    pnode = pnode.back_pnode
                return (pnode, pnode.posn, self.posn, trees)

            def show_trace(self):
                print()

                def recurse(level, pnode, n):
                    if pnode is None: return
                    if n == 0: return
                    recurse(level,   pnode.back_pnode, n-1)
                    recurse(level+1, pnode.down_pnode, pnode.down_len)
                    indent = ' '*20*level
                    print("%s    %r" % (indent, pnode.symbol))
                    print("%s->pnode %x (posn=%d, state=%d)" % (indent, id(pnode), pnode.posn, pnode.state.number))
                recurse(0, self, sys.maxsize)

        heads_at_posn_ = defaultdict(list)

        start_pnode = PNode(None, None, None, None, None, start_posn, self.start_state)
        heads_at_posn_[start_posn].append(start_pnode)

        # use_the_cache = False
        # if use_the_cache:
        #     terminal_match_cache = {}
        #     def something(X, curr_posn):
        #         key = (X, curr_posn)
        #         if key in terminal_match_cache:
        #             return terminal_match_cache[key]
        #         else:
        #             match_result = None
        #             if self._is_a_terminal(X):
        #                 match_result = terminal_matcher(curr_posn, X)
        #             terminal_match_cache[key] = match_result
        #             return match_result
        #
        # 182-186 sec to not use the cache at all
        # 209-211 sec using cache with if-in
        #     224 sec using cache with terminal_match_cache.get(key, 'not yet')
        #     244 sec using cache with try-except

        results = []
        while True:
            curr_posn = min(heads_at_posn_.keys())
            heads = heads_at_posn_.pop(curr_posn)
            if self.style == 'SLR(1)':
                limit = 8
            else:
                limit = 4
            if len(heads) > limit: # or curr_posn == 2022487:
                for head in heads:
                    head.show_trace()
                raise TooManyHeadsError(curr_posn)
                
            for head in heads:
                reduce_actions = set()
                terminals = head.state.actions_['terminal'].keys()
                matching_terminals = terminal_matcher(curr_posn, terminals)

                for (T, token_end_posn, token) in matching_terminals:
                    assert token_end_posn >= curr_posn
                    actions = head.state.actions_['terminal'][T]

                    for action in actions:
                        if action[0] == 'accept':
                            results.append(head.tree)

                        elif action[0] == 'shift_and_go_to':
                            next_state = action[1]
                            next_head = PNode(head, None, None, T, token, token_end_posn, next_state)
                            heads_at_posn_[token_end_posn].append(next_head)

                        elif action[0] == 'reduce':
                            reduce_actions.add(action)

                        else:
                            assert 0, action

                for reduce_action in list(reduce_actions):
                    (_, pi, rhs_len, lhs_nt) = reduce_action
                    # (lhs_nt, rhs) = self.productions[pi]
                    # rhs_len = len(rhs)

                    (back_pnode, start_posn, end_posn, trees) = head.go_back(rhs_len)
                    new_tree = reducer(pi, trees, start_posn, end_posn)

                    # Conceptually, push an instance of lhs_nt into the input stream.
                    [back_action] = back_pnode.state.actions_['nonterminal'][lhs_nt]
                    assert back_action[0] == 'shift_and_go_to'
                    # Conceptually shift the instance of lhs_nt.
                    # print("  ... and go to %s" % back_action[1])
                    new_state = back_action[1]
                    new_head = PNode(back_pnode, head, rhs_len, lhs_nt, new_tree, curr_posn, new_state)
                    heads_at_posn_[curr_posn].append(new_head)

            if not heads_at_posn_:
                # No remaining heads, so can't continue.
                if results:
                    return results
                else:
                    expecteds = set()
                    for head in heads:
                        for T in head.state.actions_['terminal'].keys():
                            expecteds.add(T)
                    raise ParsingError(curr_posn, sorted(list(expecteds)))
                break

# ==============================================================================

class NonterminalInfo:
    def __init__(self, name):
        self.name = name
        self.prods_with_that_lhs = []
        self.first_set = set()
        self.follow_set = set()

# ==============================================================================

class State:
    def __init__(self, parser, kernel, accessor, number):
        self.parser = parser
        self.kernel = kernel
        self.accessor = accessor
        self.number = number
        # if self.number % 100 == 0: print(self.number, file=sys.stderr)

    def __repr__(self):
        return "State #%d" % self.number

    def close(self):

        self.actions_ = {
            'terminal': defaultdict(list),
            'nonterminal': defaultdict(list),
        }

        self.transitions = OrderedDict()

        self.items = OrderedDict()
        self.unprocessed_items = []
        for item in self.kernel:
            self.items[item] = True
            self.unprocessed_items.append(item)

        while self.unprocessed_items:
            item = self.unprocessed_items.pop(0)
            (i_pi, i_lhs, i_rhs, i_dot_posn, i_lookahead) = item
            if i_dot_posn == len(i_rhs):
                # dot is at end of RHS
                if self.parser.style == 'SLR(1)':
                    assert i_lookahead is None
                    for f in sorted(list(self.parser.nt_[i_lhs].follow_set)):
                        assert self.parser._is_a_terminal(f)
                        self.actions_['terminal'][f].append( ('reduce', i_pi, i_dot_posn, i_lhs) )
                else:
                    assert self.parser._is_a_terminal(i_lookahead)
                    self.actions_['terminal'][i_lookahead].append( ('reduce', i_pi, i_dot_posn, i_lhs) )

            else:
                # dot is not at end of RHS
                X = i_rhs[i_dot_posn]

                # generate new items by epsilon
                if self.parser._is_a_nonterminal(X):
                    if self.parser.style == 'SLR(1)':
                        lookaheads = [None]
                    else:
                        beta = i_rhs[i_dot_posn+1:]
                        lookaheads = self.parser._first(list(beta) + [i_lookahead])
                    for (pi, gamma) in self.parser.nt_[X].prods_with_that_lhs:
                        for b in lookaheads:
                            new_item = (pi, X, tuple(gamma), 0, b)
                            if new_item not in self.items:
                                self.items[new_item] = True
                                self.unprocessed_items.append(new_item)

                # generate new item by transition
                next_item = (i_pi, i_lhs, i_rhs, i_dot_posn+1, i_lookahead)
                # `item` transits to `next_item` on symbol `X`
                if X not in self.transitions: self.transitions[X] = []
                self.transitions[X].append(next_item)

        for (X, next_items) in self.transitions.items():
            if X == self.parser.eoi_symbol:
                action = ('accept',)
                which = 'terminal'
            else:
                next_state = self.parser._ensure_state_for_kernel(next_items, self.accessor + [X])
                action = ('shift_and_go_to', next_state)
                if self.parser._is_a_nonterminal(X):
                    which = 'nonterminal'
                else:
                    which = 'terminal'
            self.actions_[which][X].append(action)

        if 0:
            self.print()


        for which in ['terminal', 'nonterminal']:
            for (X, actions) in self.actions_[which].items():
                if len(actions) > 1:
                    self.parser._n_conflicts += 1

                    msg = "\nIn state %d,\n  on example input of:\n    %s\n  and with next symbol: %s\n  there is a conflict between:" % (
                        self.number, ' '.join(map(str,self.accessor)), X)
                    for action in actions:
                        msg += '\n      ' + repr(action)

                    if self.parser.conflict_handling == 'silent':
                        pass
                    elif self.parser.conflict_handling == 'stderr':
                        print(msg, file=sys.stderr)
                    elif self.parser.conflict_handling == 'exception':
                        raise ParserConflict(msg) # , self.accessor, X, actions)
                    else:
                        assert 0

    def print(self):

        def stringify_item(item):
            (i_pi, i_lhs, i_rhs, i_dot_posn, i_lookahead) = item
            rhs_with_dot = (
                ' '.join(map(str,i_rhs[0:i_dot_posn]))
                +
                ' ### ' 
                +
                ' '.join(map(str,i_rhs[i_dot_posn:]))
            )
            return "%s -> %s    %s" % (i_lhs, rhs_with_dot, i_lookahead)

        print()
        print("  State %d:" % self.number)
        print()
        print("    accessor:", self.accessor)
        print()
        print("    items:")
        for item in self.items:
            print("      " + stringify_item(item))
        print()
        print("    transitions:")
        for (X, next_items) in self.transitions.items():
            print("      %s :"  % str(X))
            for next_item in next_items:
                print("        ", stringify_item(next_item))
        print()
        print("    actions:")
        for which in ['terminal', 'nonterminal']:
            print("      %s:" % which)
            for (X, actions) in self.actions_[which].items():
                print("        %s :" % str(X))
                for action in actions:
                    print("          ", action)
                if len(actions) > 1:
                    print("        CONFLICT!")

def hashable(v):
    """Determine whether `v` can be hashed."""
    try:
        hash(v)
    except TypeError:
        return False
    return True

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

if __name__ == '__main__':
    # Example grammars from the Dragon Book
    if 1:
        # Grammar 5.2 from Example 5.2 on p 151
        # ambiguous
        grammar = [
            ('G', ["E", '$']),
            ('E', ['E', '+', 'E']),
            ('E', ['E', '*', 'E']),
            ('E', ['(', 'E', ')']),
            ('E', ['id']),
        ]
        input_string = 'id + id * id'.split()
    elif 0:
        # Grammar 5.9 from Example 5.13 on p 178
        # = Example 5.19, p 189
        grammar = [
            ('G',  ["E", '$']),
            ('E',  ['T', "E'"]),
            ("E'", ['+', 'T', "E'"]),
            ("E'", []),
            ("T",  ["F", "T'"]),
            ("T'", ['*', "F", "T'"]),
            ("T'", []),
            ("F",  ['(', "E", ')']),
            ("F",  ['id']),
        ]
        input_string = 'id + id * ( id )'.split()
    elif 0:
        # Example 6.1, p 200 = Example 6.3, p206 = Example 6.7, p212
        grammar = [
            ('G', ['E', '$']),
            ('E', ['E', '+', 'T']),
            ('E', ['T']),
            ('T', ['T', '*', 'F']),
            ('T', ['F']),
            ('F', ['(', 'E', ')']),
            ('F', ['id']),
        ]
        input_string = ['id', '*', 'id', '+', 'id']
    elif 0:
        # Example 6.8, p 212
        # (an unambiguous grammar that is not SLR(1))
        grammar = [
            ('G', ['S', '$']),
            ('S', ['L', '=', 'R']),
            ('S', ['R']),
            ('L', ['*', 'R']),
            ('L', ['id']),
            ('R', ['L']),
        ]
        input_string = ['*', '*', 'id', '=', 'id']
    elif 0:
        # Example 6.10, p 215
        # (A grammar for c*dc*d.)
        grammar = [
            ('G', ['S', '$']),
            ('S', ['C', 'C']),
            ('C', ['c', 'C']),
            ('C', ['d']),
        ]
        input_string = ['c', 'c', 'd', 'd']

    my_eoi_symbol = '$'

    def simple_matcher_1(curr_posn, X):
        if curr_posn < len(input_string):
            if input_string[curr_posn] == X:
                print('symbol', X, 'matches input', input_string[curr_posn])
                return (curr_posn+1, None)
        elif curr_posn == len(input_string):
            if X is my_eoi_symbol:
                print('symbol', X, 'matches end-of-input')
                return (curr_posn, None)
        else:
            assert 0
        return None

    def simple_matcher_2(curr_posn, Xs):
        for X in Xs:
            r = simple_matcher_1(curr_posn, X)
            if r:
                (end_posn, token) = r
                yield (X, end_posn, token)

    def simple_reducer(pi, child_trees, start_posn, end_posn):
        return None

    test_parser = LR_Parser('SLR(1)', grammar, 'stderr')
    test_parser.print()
    test_parser.print_table()
    test_parser.gparse(simple_matcher_2, simple_reducer, 0)

# vim: sw=4 ts=4 expandtab
