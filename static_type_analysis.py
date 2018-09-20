#!/usr/bin/python3

# ecmaspeak-py/static_type_analysis.py:
# Perform static type analysis/inference on the spec's pseudocode.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import re, atexit, time, sys, pdb
from operator import itemgetter
from collections import OrderedDict, defaultdict
from itertools import zip_longest

import shared, HTML
from shared import stderr, spec
from Pseudocode_Parser import ANode
from Graph import Graph

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def main():
    outdir = sys.argv[1]
    shared.register_output_dir(outdir)
    spec.restore()
    #
    gather_nonterminals()
    levels = compute_dependency_levels()
    do_static_type_analysis(levels)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def gather_nonterminals():
    # This is a kludge because grammar info doesn't get passed through pickling yet.

    global nonterminals
    nonterminals = set()

    stderr("gather_nonterminals...")

    def recurse_h(hnode):
        if hasattr(hnode, '_syntax_tree'):
            recurse_a(hnode._syntax_tree)

        else:
            for child in hnode.children:
                recurse_h(child)

    def recurse_a(anode):
        if isinstance(anode, str): return
        assert isinstance(anode, ANode)
#        if anode.prod.lhs_s == '{CONDITION_1}':
#            print(anode.source_text())
        if anode.prod.lhs_s == '{NONTERMINAL}':
            [nonterminal_name] = anode.children
            if '[' in nonterminal_name: # or '_opt' in nonterminal_name:
                return
            nonterminals.add(nonterminal_name)
        else:
            for child in anode.children:
                recurse_a(child)

    recurse_h(spec.doc_node)
#    sys.exit(1)

    for nonterminal_name in sorted(list(nonterminals)):
        # print(nonterminal_name)
        t = ptn_type_for(nonterminal_name)
        if t not in tnode_for_type_:
            parent_type = T_Parse_Node
            TNode(t, tnode_for_type_[parent_type])
            # which has the side-effect of adding it to tnode_for_type_

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

# Handle built-in operations?
built_in_ops = [
    # true built-ins:
    'abs',
    'floor',
    'min',

    # defined as shorthands:
    'Completion',
    'NormalCompletion',
    'ThrowCompletion',
    # 'IfAbruptRejectPromise',

    # not built-in at all,
    # but defined by <emu-eqn>,
    # which I don't want to deal with just yet:
    'DateFromTime',
    'MonthFromTime',
    'YearFromTime',
    'WeekDay',
]

def compute_dependency_levels():
    stderr()
    stderr('analyzing dependencies...')

    # Get the headers for SDOs:
    for c in spec.doc_node.section_children:
        if c.section_title == 'Headers for Syntax-Directed Operations':
            for eoh in c.block_children:
                if eoh.element_name == 'p': continue
                assert eoh.element_name == 'emu-operation-header'
                header = Header(eoh)
            break
    else:
        assert 0

    global f_skipped
    f_skipped = shared.open_for_output('skipped_sections_with_alg')

    for s in spec.doc_node.each_descendant_that_is_a_section():

        # SDO sections need to be handled specially,
        # because they typically have one eoh followed by multiple grammar+emu-algs pairs.
        # Everywhere else, you normally get eoh + emu-alg as a pair.

        if s.section_title == 'Headers for Syntax-Directed Operations':
            # already handled above
            pass
        elif s.section_kind == 'syntax_directed_operation':
            define_ops_from_sdo_section(s)
        else:
            define_ops_from_other_section(s)

    f_skipped.close()

    for op in operation_named_.values():
        op.summarize_headers()

    # Analyze the definition(s) of each named operation to find its dependencies.
    dep_graph = Graph()
    for (op_name, op) in sorted(operation_named_.items()):
        op.find_dependencies(dep_graph)

    f = shared.open_for_output('deps')
    dep_graph.print_arcs(file=f)

    for vertex in sorted(list(dep_graph.vertices)):
        if vertex not in operation_named_ and vertex not in built_in_ops:
            print("unknown operation:", vertex)

    # Based on all that dependency info, compute the dep levels.
    levels = dep_graph.compute_dependency_levels()

    # Print levels
    for (L, clusters_on_level_L) in enumerate(levels):
        print(file=f)
        print("level %d (%d clusters):" % (L, len(clusters_on_level_L)), file=f)
        for cluster in clusters_on_level_L:
            print("    cluster #___ (%d members, %d direct prerequisite clusters):" % (
                # cluster.number,
                len(cluster.members), len(cluster.direct_prereqs)),
                file=f
            )
            for vertex in cluster.members:
                print("       ", vertex, file=f)

    f.close()
    # sys.exit(0)
    return levels

operation_named_ = {}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def define_ops_from_sdo_section(s):
    assert s.section_kind == 'syntax_directed_operation'

    if s.section_title == 'Static Semantics: TV and TRV':
        # defines two sdo's in the same section, hrm
        op_name = None
    elif s.parent.section_title == 'Pattern Semantics':
        op_name = 'regexp-Evaluate'
    else:
        mo = re.match(r'^(Static|Runtime) Semantics: (\w+)$', s.section_title)
        assert mo, s.section_title
        op_name = mo.group(2)

    if s.section_title == 'Static Semantics: HasCallInTailPosition':
        [stmt_rules, expr_rules] = s.section_children
        assert stmt_rules.section_title == 'Statement Rules'
        assert expr_rules.section_title == 'Expression Rules'
        add_defns_from_sdo_section(stmt_rules, op_name)
        add_defns_from_sdo_section(expr_rules, op_name)
    else:
        add_defns_from_sdo_section(s, op_name)

def add_defns_from_sdo_section(s, op_name):
    # There are 3 ways to contribute to a syntax-directed operation:
    #
    # - <emu-grammar> + <emu-alg> pair
    #   (The most common way)
    #
    # - <p> + <emu-alg> pair,
    #   where the <p> says "The production <emu-grammar>A : B C</emu-grammar>
    #   evaluates as follows:"
    #   21.2.2.*
    #
    # - <li>:
    #   E.g., "The Foo of <emu-grammar>A : B C</emu-grammar> is ..."
    #
    #  We catch the first 2 by scanning for <emu-alg> elements,
    #  catch the 3rd by scanning for <ul>.

    # Forms 1-2:
    for (c,child) in enumerate(s.block_children):
        if child.element_name == 'emu-alg':
            prev = s.block_children[c-1]
            assert prev.element_name in ['emu-grammar', 'p']
            discriminator = prev
            if prev.element_name == 'emu-grammar':
                # form 1
                pass
            elif prev.element_name == 'p':
                # form 2
                prev_children = prev.children
                if (
                    len(prev_children) == 3
                    and
                    prev_children[0].source_text() == 'The production '
                    and
                    prev_children[1].element_name == 'emu-grammar'
                    and
                    prev_children[2].source_text() == ' evaluates as follows:'
                ):
                    # form 2 (~52 occurrences)
                    discriminator = prev_children[1]
                else:
                    assert prev.source_text() == '<p>The production <emu-grammar type="example">A : A @ B</emu-grammar>, where @ is one of the bitwise operators in the productions above, is evaluated as follows:</p>'
                    # ignore it.
            operation_named_[op_name].add_defn( discriminator, child._syntax_tree )
            prev._used = True
            child._used = True

    # form 3:
    for ul in s.block_children:
        if ul.element_name == 'ul':
            if re.match(r'^<li>\n +it is not `0`; or\n +</li>$', ul.children[1].source_text()):
                continue

            for li in ul.children:
                if li.element_name == '#LITERAL': continue
                assert li.element_name == 'li'
                LI = li._syntax_tree
                assert LI.prod.lhs_s == '{LI}'
                [ISDO_RULE] = LI.children
                assert ISDO_RULE.prod.lhs_s == '{ISDO_RULE}'

                rule_op_names = []
                grammars = []
                defn_expr = None
                for gchild in ISDO_RULE.children:
                    gl = gchild.prod.lhs_s
                    if gl == '{ISDO_NAME}':
                        [rule_op_name] = gchild.children
                        assert rule_op_name == op_name or op_name is None
                        rule_op_names.append(rule_op_name)
                    elif gl in ['{EMU_GRAMMAR}','{NONTERMINAL}']:
                        grammars.append(gchild)
                    elif gl == '{EXPR}':
                        assert defn_expr is None
                        defn_expr = gchild
                    elif gl == '{NAMED_OPERATION_INVOCATION}':
                        if 'Note that if {NAMED_OPERATION_INVOCATION}' in ISDO_RULE.prod.rhs_s:
                            # skip it
                            pass
                        else:
                            assert defn_expr is None
                            defn_expr = gchild
                    else:
                        assert 0, gl

                assert 0 < len(rule_op_names) <= 2
                assert 0 < len(grammars) <= 5
                for rule_op_name in rule_op_names:
                    for grammar in grammars:
                        operation_named_[rule_op_name].add_defn(grammar, defn_expr)

            ul._used = True

    if 0:
        for child in s.block_children:
            if not hasattr(child, '_used'):
                if child.element_name in ['emu-note', 'emu-see-also-para']:
                    pass
                else:
                    print(s.section_num, s.section_title)
                    print('    ', repr(child.source_text()[:120]))

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def define_ops_from_other_section(s):

    # number of children with element_name...
    ncwen_ = defaultdict(int)
    for child in s.block_children:
        ncwen_[child.element_name] += 1

    n_eoh = ncwen_['emu-operation-header']
    n_emu_alg = ncwen_['emu-alg']

    def skip_msg(line):
        print(f"\n{s.section_num} {s.section_title}\n{line}", file=f_skipped)

    if n_eoh == 0:
        # Without an eoh, there's no involvement in STA,
        # so we'll be skipping this section.
        # However, we might or might not want to record that fact
        # (... because I manufacture <eoh> elements,
        # so the message might tell me of something I've missed.
    
        if n_emu_alg == 0:
            if s.section_kind in [
                'properties_of_an_intrinsic_object',
                'catchall',
                'other_property',
                'shorthand',
                #
                'Call_and_Construct_ims_of_an_intrinsic_object',
                'abstract_operations',
                'early_errors',
                'group_of_properties1',
                'group_of_properties2',
                'loop',
                'properties_of_instances',
                'function_property_xref',
                'other_property_xref',
            ]:
                # There's no expectation that such a section would have an eoh
                pass
            elif s.section_title == 'Object.prototype.__proto__':
                # It's an accessor property,
                # but the section is just a holder for subsections
                # that define the 'get' and 'set' functions.
                pass
            else:
                skip_msg(f"skipping because no eoh, despite section_kind is {s.section_kind}")
        
        else:
            if s.section_kind == 'shorthand':
                pass
            elif s.section_title in [
                'Algorithm Conventions',
                'Syntax-Directed Operations',
                # just examples

                'Statement Rules',
                'Expression Rules',
                # we actually don't skip them, we just get to them in a different way

                'Array.prototype [ @@unscopables ]',
                # <emu-alg> specifies the initial value of the data property
                # XXX could treat it as a "hidden" abstract op.
            ]:
                pass
            else:
                skip_msg(f"skpping because no eoh, despite {n_emu_alg} <emu-alg> [{s.section_kind}]")

        return

    # So at this point, we're guaranteed at least one (and usually only one) eoh.
    assert n_eoh >= 1

    if n_emu_alg == 0:
        # Not having any <emu-alg> isn't an automatic disqualification.
        # because some algorithms are defined via an <emu-table>.
        # So it might make more sense to defer this to "didn't find a definition" below.
        # But if we don't exclude (some of) these now, we'll create a Header,
        # which could cause complaints later on. XXX

        # Generally, don't bother calling skip_msg,
        # because I can't do anything (much?) about an absent <emu-alg>.

        if s.section_title == '%TypedArray%.prototype.set ( _overloaded_ [ , _offset_ ] )':
            # This section is (mostly) just a holder for the two subsections
            # that define the overloads
            # skip_msg("skipping because no <emu-alg>, despite {n_eoh} <eoh>, because it's mostly just a container for two subsections")
            return

        # The spec typically doesn't provide algorithmic specifications
        # in a bunch of cases:
        if (
            s.section_title.startswith('Math.')
            or
            s.section_title.startswith('%TypedArray%.prototype.')
            # A lot of these just say it implements the same algorithm
            # as the corresponding Array.prototype.foo function.
            # or
            # 'Host' in s.section_title
            or
            '.prototype.toLocale' in s.section_title
            or
            '.prototype [ @@iterator ]' in s.section_title
        ):
            # Don't bother printing a skip-msg.
            return
        elif s.section_title in [
            # same function object as something else:
            'Number.parseFloat ( _string_ )',
            'Number.parseInt ( _string_, _radix_ )',
            'Set.prototype.keys ( )',
            'Date.prototype.toGMTString ( )',

            # similar alg to something else:
            'String.prototype.toUpperCase ( )',

            # implementation-defined/dependent:
            # 'LocalTZA ( _t_, _isUTC_ )',
            'Date.now ( )',
            'Date.parse ( _string_ )',
            'Date.prototype.toISOString ( )',
        ]:
            # skip_msg(f"skipping because no <emu-alg>, despite {n_eoh} <eoh>")
            return

    if 0 and s.section_title.endswith('.prototype.sort ( _comparefn_ )'):
        assert n_emu_alg in [2,3]
        skip_msg(f"skipping because <emu-alg>s are incomplete, don't really define the function")
        return

    if s.section_title.startswith('String.prototype.localeCompare'):
        # The emu-alg in the section isn't the (full) alg for the function,
        # so don't connect them.
        skip_msg(f"skipping because <emu-alg> is only a small part of behavior")
        return

    # --------------------------------------------------------------------------

    # Look for an <emu-operation-header> element,
    # and then look for an algorithm-defining element immediately or shortly thereafter.

    i = 0
    while i < len(s.block_children):
        child_a = s.block_children[i]
        if child_a.element_name == 'emu-operation-header':
            header = Header(child_a)

            if s.section_kind in ['internal_method', 'env_rec_method', 'module_rec_method']:
                discriminator = header.for_param_type
            else:
                discriminator = None

            if header.name == 'CreateImmutableBinding' and header.for_param_type == T_object_Environment_Record:
                assert len(s.block_children) == 1
                # i.e., nothing here but the header, no <emu-alg> to collect
                return

            for j in range(i+1, len(s.block_children)):

                child_b = s.block_children[j]
                cben = child_b.element_name

                if cben == 'emu-alg':
                    if header.name == 'DeleteBinding' and header.for_param_type == T_module_Environment_Record:
                        # There *is* an <emu-alg> here, but I'd rather there weren't.
                        assert child_b.source_text() == '<emu-alg>\n            1. Assert: This method is never invoked. See <emu-xref href="#sec-delete-operator-static-semantics-early-errors"></emu-xref>.\n          </emu-alg>'
                        # Don't add this emu-alg to the header.
                        return

                    header.add_defn(discriminator, child_b._syntax_tree)
                    break

                elif cben == 'emu-table':
                    assert header.name.startswith('To') or header.name == 'RequireObjectCoercible', header.name
                    # header.add_defn(discriminator, child_b._syntax_tree)
                    # skip_msg(f"skipping because <emu-alg> specifies the initial value of the data property")
                    # NOT YET IMPLEMENTED
                    break

                elif cben in ['p', 'emu-note', 'ul', 'pre']:
                    pass

                else:
                    assert 0, cben

            else:
                # Got to the end of s.block_children
                # without finding a definition (emu-alg or emu-table) for the eoh.
                if header.name.startswith('Host') or header.name == 'LocalTZA':
                    # That's to be expected
                    pass
                else:
                    skip_msg("Made a Header, but didn't find a definition of the op")
                return

            i = j

        elif child_a.element_name == 'emu-alg':
            skip_msg("got an extra <emu-alg>!")

        else:
            pass

        i += 1

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Operation:
    def __init__(self, name, kind):
        self.name = name
        self.kind = kind
        self.headers = []
        self.parameter_types = None
        self.return_type = None

    def add_defn(self, discriminator, tree):
        assert len(self.headers) == 1
        self.headers[0].add_defn(discriminator, tree)

    def summarize_headers(self):
        assert len(self.headers) > 0
        if len(self.headers) == 1:
            [header] = self.headers
            self.parameters = header.parameters.items()
            self.return_type = header.return_type

        elif self.kind in ['CallConstruct_overload', 'function_property_overload']:
            pass

        else:
            assert self.kind in ['concrete method', 'internal method']
            n_params = len(self.headers[0].parameters)
            assert all(len(header.parameters) == n_params for header in self.headers)

            param_names_ = [set() for i in range(n_params)]
            param_types_ = [set() for i in range(n_params)]
            return_types = set()
            for header in self.headers:
                for (i, (param_name, param_type)) in enumerate(header.parameters.items()):
                    param_names_[i].add(param_name)
                    param_types_[i].add(param_type)
                return_types.add(header.return_type)

            self.parameters = [
                (
                    '|'.join(sorted(list(param_names_[i])))
                ,
                    union_of_types(param_types_[i])
                )
                for i in range(n_params)
            ]
            self.return_type = union_of_types(return_types)

    def find_dependencies(self, dep_graph):
        for header in self.headers:
            header.find_dependencies(dep_graph)

# ------------------------------------------------------------------------------

class Header:

    def __init__(self, eoh):
        (parsed_eoh, second_level_spans) = parse_eoh(eoh)

        self.fake_node_for_ = {}
        for (name, (start_posn, end_posn)) in second_level_spans.items():
            self.fake_node_for_[name] = ANode(None, None, start_posn, end_posn)
            if name == 'abrupt':
                self.fake_node_for_['*return*'] = ANode(None, None, start_posn, end_posn)
                # In spec_w_errors, we don't bother decomposing 
                # the return-type into normal and abrupt.
                # During analysis, changes in return-type are associated with
                # self.fake_node_for_['*return*'],
                # which is co-located  with the fake node for 'abrupt',
                # so that in spec_w_errors,
                # they appear under the whole 'returns' section.

        # -------------------------
        # name:

        self.name = parsed_eoh['name']

        # -----
        # op kind:

        self.kind = parsed_eoh['op kind']
        assert self.kind in [
            'abstract operation',
            'syntax-directed operation',
            'concrete method',
            'internal method',
            'function_property',
            'function_property_overload',
            'accessor property',
            'CallConstruct',
            'CallConstruct_overload',
            'anonymous_built_in_function',
        ]

        # -------------
        # for:

        if 'for' in parsed_eoh:
            fr = parsed_eoh['for']
            mo = re.match(r'^(.+) (_\w+_)$', fr)
            if mo:
                # The 'for' line introduces a metavariable.
                (nature_s, var_name) = mo.groups()
                t = {
                    'ECMAScript function object'        : T_function_object_,
                    'built-in function object'          : T_function_object_,
                    'Proxy exotic object'               : T_Proxy_exotic_object_,
                    'Integer-Indexed exotic object'     : T_Integer_Indexed_object_,
                    'String exotic object'              : T_Object,
                    'arguments exotic object'           : T_Object,
                    'immutable prototype exotic object' : T_Object,
                    'module namespace exotic object'    : T_Object,
                    'ordinary object'                   : T_Object,

                    'bound function exotic object'      : T_bound_function_exotic_object_,
                    'Array exotic object'               : T_Array_object_,
                }[nature_s]
                self.for_param_type = t
                self.for_param_name = var_name
            else:   
                # There's a 'for' line, but it doesn't introduce a metavariable
                # (the 'concrete methods' for env records and module records).
                # todo: Change the spec to introduce a metavariable?
                # (instead of an ad hoc first step)
                self.for_param_type = parse_type_string(fr)
                self.for_param_name = None
        else:
            # No 'for' line
            self.for_param_type = None
            self.for_param_name = None

        # -------------
        # parameters:

        self.parameters = OrderedDict(
            (pn, parse_type_string(pt))
            for (pn, pt) in parsed_eoh['parameters'].items()
        )
        assert '' not in self.parameters

        # -------------
        # also has access to:

        self.alsos = dict(
            (pn, parse_type_string(ahat_[(pn, pt)]))
            for (pn, pt) in parsed_eoh.get('also has access to', {}).items()
        )

        # -------------
        # returns:

        r = parsed_eoh['returns']
        if r['normal'] == 'TBD' and r['abrupt'] == 'TBD':
            rt = 'TBD'
        elif r['abrupt'] == 'TBD':
            rt = r['normal']
        elif r['normal'] == 'TBD':
            rt = r['abrupt']
        else:
            rt = r['normal'] + " | " + r['abrupt']

        self.return_type = parse_type_string(rt)

        # -------------
        # description: (skip)

        # -------------------------

        # tweak some parameter/return types:
        # Theoretically, the STA would figure all this out,
        # but (a) it's not that smart, and (b) this saves some churn.
        for (ton, tpn, tot, tnt) in type_tweaks:
            # NUMBER=INTEGER?
            if tot == T_Number and tnt == T_Number: continue
            if ton == self.name:
                try:
                    old_type = self.return_type if tpn == '*return*' else self.parameters[tpn]
                except KeyError:
                    print("%s does not have param named %s" % (ton, tpn))
                    sys.exit(1)
                if tot != old_type:
                    # This can happen when you've read tweaks from the cheater file,
                    # because return-type is split in spec,
                    # and fake_node only points to the abrupt part.
                    # "warning: tweak %s fails old-type check: In %s, existing type of %s is %s, not %s" % (
                    # (ton, tpn, tot, tnt), self.name, tpn, old_type, tot)
                    assert 0, (ton, tpn, tot, tnt, old_type)
                self.change_declared_type(tpn, tnt, tweak=True)

        # -------------------------

        self.defns = []

        # -------------------------

        if self.name == 'Set' and self.kind == 'CallConstruct':
            self.name = 'built-in Set'
            # so that it doesn't collide with the abstract operation 'Set'

        if self.name in operation_named_:
            # We've already seen a header for an operation with this name.
            op = operation_named_[self.name]
            assert self.kind != 'abstract operation'
            assert op.kind == self.kind
        else:
            # First header for an operation with this name.
            op = Operation(self.name, self.kind)
            operation_named_[self.name] = op

        op.headers.append(self)

    # ------------------------------------------------------

    def add_defn(self, discriminator, tree):
        if self.kind == 'syntax-directed operation':
            assert (
                isinstance(discriminator, HTML.HNode)
                    and discriminator.element_name in ['emu-grammar', 'p']
                or
                isinstance(discriminator, ANode)
                    and discriminator.prod.lhs_s in ['{EMU_GRAMMAR}', '{NONTERMINAL}']
            )
        elif self.kind in ['concrete method', 'internal method']:
            assert isinstance(discriminator, Type)
        elif self.kind == 'abstract operation':
            assert discriminator is None
        elif self.kind in [
            'function_property',
            'function_property_overload',
            'accessor property',
            'CallConstruct',
            'CallConstruct_overload',
            'anonymous_built_in_function',
        ]:
            assert discriminator is None
        else:
            assert 0

        assert isinstance(tree, ANode)
        assert tree.prod.lhs_s in [
            '{EMU_ALG_BODY}',
            '{IAO_BODY}',
            '{EXPR}',
            '{NAMED_OPERATION_INVOCATION}',
        ], tree.prod.lhs_s

        self.defns.append((discriminator,tree))

    # ------------------------------------------------------

    def find_dependencies(self, dep_graph):

        if len(self.defns) == 0:
            if self.name.startswith('Host') or self.name == 'LocalTZA':
                # makes sense that there's no defns
                pass
            elif self.name in [
                'ToBoolean',
                'ToNumber',
                'ToObject',
                'ToPrimitive',
                'ToString',
                'RequireObjectCoercible',
            ]:
                # defined by table, not handling that yet XXX
                pass
            elif self.name == 'CreateImmutableBinding' and self.for_param_type == T_object_Environment_Record:
                # no alg
                pass
            elif self.name == 'DeleteBinding' and self.for_param_type == T_module_Environment_Record:
                # pointless alg
                pass
            else:
                assert 0, self.name
                # HasCallInTailPosition

        dep_graph.add_vertex(self.name)

        def recurse(x):
            if isinstance(x, ANode):
                if x.prod.lhs_s == '{NOI}':
                    if x.prod.rhs_s == 'Abstract Equality Comparison {VAR} == {VAR}':
                        depend_on('Abstract Equality Comparison')
                    elif x.prod.rhs_s in [
                        'Abstract Relational Comparison {VAR} &lt; {VAR}',
                        'Abstract Relational Comparison {VAR} &lt; {VAR} with {VAR} equal to {LITERAL}',
                    ]:
                        depend_on('Abstract Relational Comparison')
                    elif x.prod.rhs_s == 'EvaluateBody of the parsed code that is {DOTTING} {WITH_ARGS}':
                        depend_on('EvaluateBody')
                    elif x.prod.rhs_s == 'Strict Equality Comparison {VAR} === {EX}':
                        depend_on('Strict Equality Comparison')
                    elif x.prod.rhs_s in [
                        'a sign-extending right shift of {VAR} by {VAR} bits. The most significant bit is propagated. The result is a signed 32-bit integer',
                        'a zero-filling right shift of {VAR} by {VAR} bits. Vacated bits are filled with zero. The result is an unsigned 32-bit integer',
                        'the abstract operation named by {DOTTING} using the elements of {DOTTING} as its arguments',
                    ]:
                        pass
                    elif x.prod.rhs_s in [
                        'the UTF16Encoding of the code points of {VAR}',
                        'the UTF16Encoding of each code point of {NAMED_OPERATION_INVOCATION}',
                    ]:
                        depend_on('UTF16Encoding')
                    elif x.prod.rhs_s in [
                        '{LOCAL_REF} Contains {NONTERMINAL}',
                        '{LOCAL_REF} Contains {VAR}',
                    ]:
                        depend_on('Contains')
                    elif x.prod.rhs_s in [
                        '{OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF}',
                       r'{OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF} \(see {EMU_XREF}\)',
                        '{OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF} {WITH_ARGS}',
                        '{OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF} as defined in {EMU_XREF}',
                        '{OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF}; if {LOCAL_REF} is not present, use the numeric value zero',
                        '{PREFIX_PAREN}',
                    ]:
                        pass # handle deeper
                    else:
                        assert 0, x.prod

                elif x.prod.lhs_s == '{OPN_BEFORE_FOROF}':
                    depend_on(x.children[0])

                elif x.prod.lhs_s == '{OPN_BEFORE_PAREN}':
                    if x.prod.rhs_s == r'(ForIn/Of(?:Head|Body)Evaluation|(?!Type\b)[A-Za-z]\w+)':
                        depend_on(x.children[0])
                    elif x.prod.rhs_s == 'Atomics\\.load':
                        depend_on('Atomics.load')
#                    elif x.prod.rhs_s == '{SAB_FUNCTION}':
#                        depend_on('reads-bytes-from')
                    elif x.prod.rhs_s == '(HasPrimitiveBase)':
                        depend_on(x.children[0])
                    elif x.prod.rhs_s == '{VAR}\.([A-Z][A-Za-z0-9]+)':
                        depend_on(x.children[1])
                    elif x.prod.rhs_s == '{DOTTING}':
                        [dotting] = x.children
                        assert dotting.prod.lhs_s == '{DOTTING}'
                        [base, dsbn] = dotting.children
                        assert dsbn.prod.lhs_s == '{DSBN}'
                        [dsbn_name] = dsbn.children
                        depend_on('[[%s]]' % dsbn_name)
                    elif x.prod.rhs_s == '{VAR}':
                        # Difficult to make a specific dependency.
                        pass
                    else:
                        print(x.prod.rhs_s, x.source_text())
                        assert 0

                elif x.prod.lhs_s == '{ISDO_NAME}':
                    depend_on(x.children[0])

                elif x.prod.lhs_s == '{EXPR}':
                    if x.prod.rhs_s.startswith('the result of evaluating'):
                        depend_on('Evaluation')
                        pass

                for child in x.children:
                    recurse(child)

            elif isinstance(x, str):
                pass

            else:
                assert 0, x

        def depend_on(called_op):
            caller_op_name = self.name
            dep_graph.add_arc(caller_op_name, called_op)

        for (discriminator,tree) in self.defns:
            recurse(tree)

    # ----------------------------------------------------------------

    def make_env(self):
        e = Env()

        if self.for_param_name is not None:
            assert self.for_param_type is not None
            e.vars[self.for_param_name] = self.for_param_type

        for (pn, pt) in self.parameters.items():
            assert isinstance(pt, Type)
            e.vars[pn] = pt

        for (vn, vt) in self.alsos.items():
            assert isinstance(vt, Type)
            e.vars[vn] = vt

        e.vars['*return*'] = self.return_type

        return e

    # ----------------------------------------------------------------

    def change_declared_type(self, pname, new_t, tweak=False):
        if pname == '*return*':
            # if new_t == T_Reference: pdb.set_trace()
            old_t = self.return_type
            self.return_type = new_t
        else:
            old_t = self.parameters[pname]
            self.parameters[pname] = new_t

        assert old_t != new_t

        verb = 'tweak' if tweak else 'change'
        change = "%s%s type of `%s` from `%s` to `%s`" % (
            g_level_prefix, verb, pname, old_t, new_t)
        node = self.fake_node_for_[pname]
        node._new_t = new_t
        all_errors.append((node, change))

        #!!! print("EDIT: In a header for `%s`: %s" % (self.name, change))
        # if self.name == 'LabelledEvaluation' and pname == '_labelSet_': pdb.set_trace()

# ------------------------------------------------------------------------------

def parse_eoh(eoh):
    assert eoh.element_name == 'emu-operation-header'

    # Quick and dirty parser.
    # Doesn't care about indentation.
    # (Doesn't have to, because there's only two levels.)
    # (Properly, we would use a yaml parser.)

    parsed_eoh = OrderedDict()
    second_level_spans = {}

    current_prop_name = None
    for line_mo in re.compile('.+').finditer(spec.text, eoh.inner_start_posn, eoh.inner_end_posn):
        (line_start, line_end) = line_mo.span(0)

        mo = re.compile(r' +$').match(spec.text, line_start, line_end)
        if mo:
            assert line_end == eoh.inner_end_posn
            # It's the last line in the eoh content
            continue

        # first level:

        mo = re.compile(r' +(\w+|op kind|overload selected when called with): ([^ ].*)$').match(spec.text, line_start, line_end)
        if mo:
            (name, value) = mo.groups()
            assert name not in parsed_eoh
            if value == 'none':
                assert name == 'parameters'
                value = OrderedDict()
            parsed_eoh[name] = value
            continue

        mo = re.compile(r' +(\w+|also has access to):$').match(spec.text, line_start, line_end)
        if mo:
            current_prop_name = mo.group(1)
            parsed_eoh[current_prop_name] = OrderedDict()
            continue

        # second level:

        mo = re.compile(r' +- (\w+) +: ([^ ].*)$').match(spec.text, line_start, line_end)
        if mo:
            (name, value) = mo.groups()
            assert current_prop_name is not None
            parsed_eoh[current_prop_name][name] = value
            second_level_spans[name] = mo.span(2)
            continue

        stderr('>> parse_eoh could not parse line:', repr(line_mo.group(0)))

    return (parsed_eoh, second_level_spans)

# ------------------------------------------------------

# "also has access to" type info
ahat_ = {
    ('_comparefn_', 'the _comparefn_ argument passed to the current invocation of the `sort` method'):
        'Undefined | function_object_',
    ('_reviver_', 'the value of _reviver_ that was originally passed to the above parse function'):
        'function_object_',
    ('_ReplacerFunction_', 'from the invocation of the `stringify` method'):
        'function_object_ | Undefined',
    ('_stack_'       , 'from the current invocation of the `stringify` method'): 'List of Object',
    ('_indent_'      , 'from the current invocation of the `stringify` method'): 'String',
    ('_gap_'         , 'from the current invocation of the `stringify` method'): 'String',
    ('_PropertyList_', 'from the current invocation of the `stringify` method'): 'Undefined | List',
    ('_IgnoreCase_', 'Boolean'): 'Boolean',

    ('_Input_'           , 'from somewhere'): 'List of character_',
    ('_InputLength_'     , 'from somewhere'): 'Integer_',
    ('_NcapturingParens_', 'from somewhere'): 'Integer_',
    ('_DotAll_'          , 'from somewhere'): 'Boolean',
    ('_IgnoreCase_'      , 'from somewhere'): 'Boolean',
    ('_Multiline_'       , 'from somewhere'): 'Boolean',
    ('_Unicode_'         , 'from somewhere'): 'Boolean',

    ('_comparefn_' , 'from the `sort` method'): 'function_object_ | Undefined',
    ('_buffer_'    , 'from the `sort` method'): 'ArrayBuffer_object_ | SharedArrayBuffer_object_',
}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

#eohs = []
#
#def gather_eohs():
#    def recurse(hnode):
#        assert isinstance(hnode, HTML.HNode)
#        if hnode.element_name == 'emu-operation-header':
#            eohs.append(hnode)
#        else:
#            for child in hnode.children:
#                recurse(child)
#
#    recurse(spec.doc_node)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

subtype_memo = {}
split_memo = {}

class Type(tuple):

    def set_of_types(self):
        return self.member_types if isinstance(self, UnionType) else frozenset([self])

    def __or__(A, B):
        if A == B: return A
        # check subtyping?
        A_members = A.set_of_types()
        B_members = B.set_of_types()
        u = maybe_UnionType(A_members | B_members)
        # print(A, '|', B, '=', u)
        return u

    # -----------------------------------------------------

    # @memoize()
    def is_a_subtype_of_or_equal_to(A, B):

        if (A,B) in subtype_memo:
            return subtype_memo[(A,B)]
        # No speed-up? 

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if T_TBD in A_members or T_TBD in B_members:
            result = False

        elif A_members <= B_members:
            result = True
        elif A_members > B_members:
            result = False

        else:
            # A is a subtype of B iff every A_member is a subtype of B.
            result = all(
                # and an A_member is a subtype of B
                # iff it is a subtype of some B_member
                any(
                    member_is_a_subtype_or_equal(A_member, B_member)
                    for B_member in B_members
                )
                for A_member in A_members
            )

        if 0:
            print(
                "SUBTYPING:",
                A,
                "is" if result else "is not",
                "a subtype of",
                B
            )

        subtype_memo[(A,B)] = result

        return result

    # -----------------------------------------------------

    def split_by(A, B):
        # Return a pair of types that partition A
        # (i.e., two disjoint types whose union is A):
        # one that is a subtype of (or equal to) B,
        # and one that is outside of B.
        # (Either can be T_0.)

        # if A == T_TBD and B == ListType(T_String): pdb.set_trace()

        if 0:
            (outside_B, inside_B, _) = compare_types(A, B)
            return (inside_B, outside_B)

        A_members = A.set_of_types()
        B_members = B.set_of_types()

        if (A,B) in split_memo:
            return split_memo[(A,B)]

        A_memtypes = A.set_of_types()
        B_memtypes = B.set_of_types()

        # A few cases that can be handled quickly:
        if A_memtypes == B_memtypes:
            inside_B  = A # or B
            outside_B = T_0

        elif A_memtypes <= B_memtypes:
            inside_B  = A
            outside_B = T_0

        elif B_memtypes <= A_memtypes:
            inside_B  = B
            outside_B = maybe_UnionType(A_memtypes - B_memtypes)

        else:
            # The general case:
            inside_B = set()
            outside_B = set()

            def recurse(A_subtypes, B_subtypes):
                for a in A_subtypes:
                    assert isinstance(a, Type)

                    # Treat T_TBD like Top
                    if a == T_TBD: a = T_Top_ # assert 0

                    if a.is_a_subtype_of_or_equal_to(B):
                        inside_B.add(a)
                    else:
                        # get a list of the B_subtypes that are subtypes of a
                        bs_within_a = [
                            b
                            for b in B_subtypes
                            if b.is_a_subtype_of_or_equal_to(a)
                        ]
                        if bs_within_a:
                            # break down `a`
                            if a == T_List:
                                if bs_within_a == [ListType(T_String)]:
                                    inside_B.add(ListType(T_String))
                                    outside_B.add(ListType(T_other_))
                                elif bs_within_a == [ListType(T_Symbol|T_String)]:
                                    inside_B.add(ListType(T_Symbol|T_String))
                                    outside_B.add(ListType(T_other_))
                                elif bs_within_a == [ListType(T_Tangible_)]:
                                    inside_B.add(ListType(T_Tangible_))
                                    outside_B.add(ListType(T_other_))
                                else:
                                    assert 0
                            elif isinstance(a, ListType):
                                if a == ListType(T_character_) and bs_within_a == [ListType(T_code_point_)]:
                                    inside_B.add(ListType(T_code_point_))
                                    outside_B.add(ListType(T_code_unit_))
                                elif a == ListType(T_character_) and bs_within_a == [ListType(T_code_unit_)]:
                                    inside_B.add(ListType(T_code_unit_))
                                    outside_B.add(ListType(T_code_point_))
                                elif a == ListType(T_Tangible_) and bs_within_a == [ListType(T_Number)]:
                                    inside_B.add(ListType(T_Number))
                                    outside_B.add(ListType(T_Tangible_)) # XXX T_Tangible_ - T_Number (TypedArrayCreate)
                                else:
                                    assert 0
                            else:
                                tnode = tnode_for_type_[a]
                                a_imm_subtypes = [child.type for child in tnode.children]
                                recurse(a_imm_subtypes, bs_within_a)
                        else:
                            # no B_subtype is within `a`
                            # so `a` must be disjoint from B
                            outside_B.add(a)

            recurse(A_memtypes, B_memtypes)

            inside_B  = maybe_UnionType(inside_B)
            outside_B = maybe_UnionType(outside_B)

        print("%s :: %s  ===>  %s  ///  %s" %
            (A, B, outside_B, inside_B),
            file=split_types_f)

        result = (inside_B, outside_B)
        split_memo[(A,B)] = result
        return result


def member_is_a_subtype_or_equal(A, B):
    assert not isinstance(A, UnionType); assert A != T_TBD
    assert not isinstance(B, UnionType); assert B != T_TBD

    if A == B: return True

    if isinstance(A, NamedType):
        if isinstance(B, NamedType):
            A_tnode = tnode_for_type_[A]
            B_tnode = tnode_for_type_[B]
            if A_tnode.level < B_tnode.level:
                # A is higher in the hierarchy than B
                # (not necessarily an ancestor of B, but at a higher level).
                return False
            elif A_tnode.level == B_tnode.level:
                # They're at the same level in the hierarchy.
                # But we've already tested them for equality,
                # so they must be siblings/cousins.
                return False
            elif A_tnode.level > B_tnode.level:
                # A is at a lower level than B in the hierarchy.
                # So it might be a subtype.
                n_levels_diff = A_tnode.level - B_tnode.level
                tnode = A_tnode
                for i in range(n_levels_diff): tnode = tnode.parent
                assert tnode.level == B_tnode.level
                return (tnode is B_tnode)
            else:
                assert 0, "can't happen"
        else:
            # e.g., is Foo a subtype of List of Foo?
            # I don't think there's much need to say it is.
            return False

    elif isinstance(A, ListType):
        if isinstance(B, ListType):
            return (A.element_type.is_a_subtype_of_or_equal_to(B.element_type))
        elif isinstance(B, NamedType):
            return (T_List.is_a_subtype_of_or_equal_to(B))
        else:
            assert 0, (A, B)

    elif isinstance(A, ThrowType):
        if isinstance(B, ThrowType):
            return (A.error_type.is_a_subtype_of_or_equal_to(B.error_type))
        elif isinstance(B, NamedType):
            return (T_throw_.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ListType):
            return False
        else:
            assert 0, (A, B)

    elif isinstance(A, ProcType):
        if isinstance(B, ProcType):
            assert 0, (A, B)
        elif isinstance(B, NamedType):
            return (T_proc_.is_a_subtype_of_or_equal_to(B))
        elif isinstance(B, ListType):
            return False
        else:
            assert 0, (A, B)

    else:
        assert 0, (A, B)


    # --------------------------------------------------------------------------

class TBDType(Type):
    __slots__ = ()
    def __new__(cls):
        return tuple.__new__(cls, ('TBDType',))
    def __repr__(self): return "%s()" % self
    def __str__(self): return 'TBD'
    def unparse(self, parenthesuze=False): return 'TBD'

class NamedType(Type):
    __slots__ = ()
    def __new__(cls, name):
        assert isinstance(name, str)
        return tuple.__new__(cls, ('NamedType', name))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return self.name
    def unparse(self, parenthesize=False):
        if self.name.startswith('PTN_'):
            x = 'Parse Node for |%s|' % self.name.replace('PTN_','')
            if parenthesize: x = '(%s)' % x
            return x
        else:
            return self.name
    name = property(itemgetter(1))

class ListType(Type):
    __slots__ = ()
    def __new__(cls, element_type):
        return tuple.__new__(cls, ('ListType', element_type))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "List of %s" % str(self.element_type)
    def unparse(self, _=False): return "List of %s" % self.element_type.unparse(True)
    element_type = property(itemgetter(1))

class TupleType(Type):
    __slots__ = ()
    def __new__(cls, component_types):
        return tuple.__new__(cls, ('TupleType', component_types))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "(%s)" % str(self.component_types)
    def unparse(self, _=False): return "(%s)" % self.component_types.unparse(True)
    component_types = property(itemgetter(1))

class ThrowType(Type):
    __slots__ = ()
    def __new__(cls, error_type):
        return tuple.__new__(cls, ('ThrowType', error_type))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "throw_(%s)" % str(self.error_type)
    def unparse(self, _=False): return "throw_ *%s*" % self.error_type.unparse(True)
    error_type = property(itemgetter(1))

class ProcType(Type):
    __slots__ = ()
    def __new__(cls, param_types, return_type):
        return tuple.__new__(cls, ('ProcType', tuple(param_types), return_type))
    def __repr__(self): return "%s(%r, %r)" % self
    def __str__(self):
        if self == T_Continuation:
            return "Continuation"
        elif self == T_Matcher:
            return "Matcher"
        elif self == T_AssertionTester:
            return "AssertionTester"
        elif self == T_bytes_combining_op_:
            return "bytes_combining_op_"
        elif self == T_RegExpMatcher_:
            return "RegExpMatcher_"
        else:
            return "(%s -> %s)" % (self.param_types, self.return_type)
    def unparse(self, _=False): return str(self)

    param_types = property(itemgetter(1))
    return_type = property(itemgetter(2))

class UnionType(Type):
    # A union of (non-union) types.
    # Must satisfy the constraint that no member-type
    # is a subtype or supertype of any other member-type.
    # (XXX: Should check that in __new__.)

    __slots__ = ()
    def __new__(cls, member_types):
        assert len(member_types) != 1
        for type in member_types:
            assert not isinstance(type, UnionType)
        return tuple.__new__(cls, ('UnionType', frozenset(member_types)))
    def __repr__(self): return "%s(%r)" % self
    def __str__(self): return "(%s)" % ' | '.join(sorted(map(str, self.member_types)))

    def unparse(self, parenthesize=False):
        if T_not_passed in self.member_types:
            # This only makes sense for a top-level type,
            # but I don't think it'll occur anywhere else.
            prefix = '(optional) '
            member_types = set(self.member_types)
            member_types.remove(T_not_passed)
        else:
            prefix = ''
            member_types = self.member_types

        x = ' | '.join(sorted(
            member_type.unparse()
            for member_type in member_types
        ))
        if parenthesize: x = '(' + x + ')'
        return prefix + x

    member_types = property(itemgetter(1))

T_0 = UnionType([])

def maybe_UnionType(member_types):
    assert not isinstance(member_types, Type)
    if len(member_types) == 1:
        return list(member_types)[0]
    else:
        return UnionType(member_types)

# ------------------------------------------------------------------------------

def parse_type_string(text):
    assert text != ''

    mo = re.match(r'^\(optional\) (.+)$', text)
    if mo:
        is_optional = True
        text = mo.group(1)
    else:
        is_optional = False

    t = ptsr(text)

    if is_optional:
        t = t | T_not_passed

    return t

def ptsr(text):
    assert text != ''
    for (pattern, lam) in [
        (r'\(([^()]*)\) -> (.+)', text_to_proc_type),
        (r'(List of \([^()]+\)) \| ([\w ]+)', lambda mo: UnionType([ptsr(mo.group(1)), ptsr(mo.group(2))])),
        (r'List of \(([^()]+)\)', lambda mo: ListType(ptsr(mo.group(1)))),
        (r'List of ([\w ]+)',     lambda mo: ListType(ptsr(mo.group(1)))),
        (r'Parse Node for \|(\w+)\|', lambda mo: ptn_type_for(mo.group(1))),
        (r'.+ \| .+',         lambda mo: UnionType([ptsr(alt) for alt in text.split(' | ')])),
        (r'throw_ \*(\w+)\*', lambda mo: ThrowType(ptsr(mo.group(1)))),
        (r'\w+( \w+)*',       lambda mo: maybe_NamedType(mo.group(0))),
    ]:
        mo = re.match('^' + pattern + '$', text)
        if mo:
            memtype = lam(mo)
            # assert memtype in tnode_for_type_, memtype
            return memtype
    assert 0, repr(text)

def text_to_proc_type(mo):
    (param_text, return_text) = mo.groups()

    if re.match('^ *$', param_text):
        param_types = []
    else:
        param_types = [parse_type_string(tx) for tx in param_text.split(', ')]

    if re.match(r'^\([^()]+\)$', return_text):
        return_text = return_text[1:-1]
    return_type = parse_type_string(return_text)

    return ProcType(param_types, return_type)

def ptn_type_for(nonterminal):
    if isinstance(nonterminal, str):
        nont_basename = nonterminal
        optionality = ''
    elif isinstance(nonterminal, ANode):
        assert nonterminal.prod.lhs_s == '{NONTERMINAL}'
        [nonterminal_ref] = nonterminal.children
        mo = re.match(r'^(\w+)((?:\[[^][]+\])?)((?:_opt)?)$', nonterminal_ref)
        assert mo
        [nont_basename, params, optionality] = mo.groups()
    else:
        assert 0
    type_name = 'PTN_' + nont_basename + optionality
    type = NamedType(type_name)
    return type

def type_for_TYPE_NAME(type_name):
    assert isinstance(type_name, ANode)
    assert type_name.prod.lhs_s == '{TYPE_NAME}'
    return NamedType(type_name.source_text())

# ------------------------------------------------------------------------------

named_type_hierarchy = {
    'Top_': {
        'Abrupt' : {
            'continue_': {},
            'break_': {},
            'return_': {},
            'throw_': {},
        },
        'Normal': {
            'Absent': { # not sure this is at the right place in the hierarchy.
                'not_passed': {},    # for an optional parameter
                'not_in_record': {}, # for an optional field of a record
                'not_in_node': {},   # for an optional child of a node
                'not_set': {},       # for a metavariable that might not be initialized
                'not_returned': {},  # for when control falls off the end of an operation
            },
            'Tangible_': {
                'Primitive': {
                    'Undefined': {},
                    'Null': {},
                    'Boolean': {},
                    'String': {},
                    'Symbol': {},
                    'Number': {
                        'Integer_': {},
                        #? 'NonNegativeInteger_': {}
                        'OtherNumber_': {},
                    },
                },
                'Object': {
                    'Error': {
                        'ReferenceError': {},
                        'SyntaxError': {},
                        'TypeError': {},
                        'other_Error_': {},
                    },
                    # 'Proxy': {},
                    # 'RegExp': {},
                    'ArrayBuffer_object_': {},
                    'Array_object_': {},
                    'AsyncGenerator_object_': {},
                    'Integer_Indexed_object_': {},
                    'Iterator_object_': {},
                    'IteratorResult_object_': {},
                    'Promise_object_': {},
                    'SharedArrayBuffer_object_': {},
                    'String_exotic_object_': {},
                    'TypedArray_object_': {},
                    'function_object_': {
                        'constructor_object_': {},
                        'Proxy_exotic_object_': {},
                        'bound_function_exotic_object_': {},
                        'other_function_object_': {},
                    },
                    'other_Object_': {},
                },
            },
            'Intangible_': {
                'AssignmentTargetType_': {},
                'CharSet': {},
                'Data Block': {},
                'FunctionKind1_': {},
                'IEEE_binary32_': {},
                'IEEE_binary64_': {},
                'Infinity_': {},
                'IterationKind_': {},
                'IteratorKind_': {},
                'LangTypeName_': {},
                'Lexical Environment': {},
                'LhsKind_': {},
                'List': {},
                'MatchResult': {
                    'State': {},
                    'match_failure_': {},
                },
                'MathReal_': {
                    'MathInteger_': {},
                    'MathOther_': {},
                },
                'pair_': {},
                'Parse Node' : {
                    'PTN_ForBinding': {},
                    'PTN_Script': {},
                },
                'Record': {
                    'Agent Record': {},
                    'Agent Events Record': {},
                    'AsyncGeneratorRequest Record': {},
                    'Chosen Value Record': {},
                    'Environment Record': {
                        'declarative Environment Record': {
                            'function Environment Record': {},
                            'module Environment Record': {},
                        },
                        'object Environment Record': {},
                        'global Environment Record': {},
                    },
                    'ExportEntry Record': {},
                    'ExportResolveSet_Record_': {},
                    'GlobalSymbolRegistry Record': {},
                    'ImportEntry Record': {},
                    'Intrinsics Record': {},
                    'MapData_record_': {},
                    'Module Record': {
                        'Source Text Module Record': {},
                        'other Module Record': {},
                    },
                    'PendingJob': {},
                    'PromiseCapability Record': {},
                    'PromiseReaction Record': {},
                    'Property Descriptor': {
                        # subtypes data and accessor and generic?
                    },
                    'Realm Record': {},
                    'ResolvedBinding Record': {},
                    'ResolvingFunctions_record_': {},
                    'Script Record': {},
                    'boolean_value_record_': {},
                    'candidate execution': {},
                    'event_': {
                        'Shared Data Block event': {
                            'ReadModifyWriteSharedMemory event': {},
                            'ReadSharedMemory event': {},
                            'WriteSharedMemory event': {},
                        },
                        'Synchronize event': {},
                        'host-specific event': {},
                    },
                    'iterator_record_': {},
                    'methodDef_record_': {},
                    'integer_value_record_': {},
                    'templateMap_entry_': {},
                },
                'Reference': {},
                'Relation': {},
                'Set': {},
                'Shared Data Block': {},
                'SlotName_': {},
                'Unicode_code_points_': {},
                'WaiterList' : {},
                'agent_signifier_' : {},
                'alg_steps': {},
                'character_': {
                    'code_unit_': {},
                    'code_point_': {},
                },
                'completion_kind_': {},
                'empty_': {},
                'execution context': {},
                'grammar_symbol_': {},
                'host_defined_': {},
                #
                'proc_': {},
                'property_': {
                    'data_property_': {},
                    'accessor_property_': {},
                },
                'this_mode': {},
                'tuple_': {},
                'other_': {},
            },
        },
    }
}

tnode_for_type_ = {}

class TNode:
    def __init__(self, type, parent):
        self.type = type
        self.parent = parent

        self.children = []

        if parent is None:
            self.level = 0
        else:
            self.level = parent.level + 1
            parent.children.append(self)

        tnode_for_type_[type] = self

def traverse(typesdict, p):
    for (type_name, subtypesdict) in typesdict.items():
    # sorted(typesdict.items(), key=lambda tup: 1 if tup[0] == 'List' else 0):
        assert isinstance(type_name, str)
        t = NamedType(type_name)
        #
        variable_name = 'T_' + type_name.replace(' ', '_')
        globals()[variable_name] = t
        #
        tnode = TNode(t, p)
        traverse(subtypesdict, tnode)

stderr("initializing the type hierarchy...")
traverse(named_type_hierarchy, None)

troot = tnode_for_type_[T_Top_]

def ensure_tnode_for(type):
    assert isinstance(type, Type)
    if type in tnode_for_type_:
        return tnode_for_type_[type]
    else:
        if isinstance(type, NamedType):
            assert 0, type
        elif isinstance(type, ThrowType):
            parent_type = T_throw_
        elif isinstance(type, ListType):
            parent_type = T_List # XXX but this fails to capture subtypes within
        elif isinstance(type, ProcType):
            parent_type = T_proc_
        elif isinstance(type, TupleType):
            parent_type = T_tuple_
        else:
            assert 0, type
        return TNode(type, tnode_for_type_[parent_type])
        # which has the side-effect of adding it to tnode_for_type_

ensure_tnode_for( ListType(T_other_) )
ensure_tnode_for( ProcType((), T_other_) )
ensure_tnode_for( ThrowType(T_other_) )

# ------------------------------------------------------------------------------

T_TBD = TBDType()

T_Continuation    = ProcType([T_State                ], T_MatchResult)
T_Matcher         = ProcType([T_State, T_Continuation], T_MatchResult)
T_AssertionTester = ProcType([T_State                ], T_Boolean)
T_RegExpMatcher_  = ProcType([T_String, T_Integer_   ], T_MatchResult)

T_bytes_combining_op_ = ProcType([ListType(T_Integer_), ListType(T_Integer_)], ListType(T_Integer_))

T_captures_entry_ = ListType(T_character_) | T_Undefined
T_captures_list_  = ListType(T_captures_entry_)

T_numeric_        = T_Number | T_code_unit_ | T_MathReal_

T_transitioning_from_Number_to_MathReal = T_Number # T_MathReal_

def maybe_NamedType(name):
    if name == 'TBD':
        return T_TBD
    elif name == 'Continuation':
        return T_Continuation
    elif name == 'Matcher':
        return T_Matcher
    elif name == 'AssertionTester':
        return T_AssertionTester
    elif name == 'RegExpMatcher_':
        return T_RegExpMatcher_
    elif name == 'bytes_combining_op_':
        return T_bytes_combining_op_
    elif name == 'NonNegativeInteger_':
        # There are 5 places where structify yields this parameter type.
        # But as far as STA is concerned, it's just an alias for Integer_.
        return T_Integer_
    else:
        return NamedType(name)

type_tweaks_filename = '_type_tweaks.txt'
# type_tweaks_filename = '_operation_headers/cheater_type_tweaks'
type_tweaks = []
for line in open(type_tweaks_filename, 'r'):
    [op_name, p_name, old_t_str, new_t_str] = re.split(' *; *', line.rstrip())
    type_tweaks.append( (
        op_name,
        p_name,
        parse_type_string(old_t_str),
        parse_type_string(new_t_str),
    ))

# UpdateEmpty: _completionRecord_, *return

# InitializeReferencedBinding: _V_ and _W_ can be Abrupt
# InitializeBoundName return?
# ToPrimitive _PreferredType_
# OrdinaryHasInstance: _C_, _O_
# IteratorNext: _value_
# IteratorStep: return
# LoopContinues: _completion_
# PerformEval: _x_ + return
# RegExpInitialize: _pattern_, _flags_
# RegExpCreate: _P_, _F_
# IteratorDestructuringAssignmentEvaluation: return
# KeyedDestructuringAssignmentEvaluation: return
# LabelledEvaluation: return
# ForBodyEvaluation: return
# ForIn/OfBodyEvaluation: return
# BoundNames: return


# ------------------------------------------------------------------------------

# memoize
def union_of_types(types):
    if len(types) == 0: return T_0

    types1 = set(types)

    # Treat T_TBD like T_0,
    # i.e. the union-type with no member-types.
    # i.e., It has no effect on a union of types.
    types1.discard(T_TBD)

    if len(types1) == 0:
        # It must be that all types were T_TBD
        return T_TBD
    elif len(types1) == 1:
        return types1.pop()

    # ----------------------------

    memtypes = set()
    for t in types1:
        if isinstance(t, UnionType):
            for mt in t.member_types:
                assert not isinstance(mt, UnionType)
                memtypes.add(mt)
        else:
            memtypes.add(t)

    memtypes.discard(T_TBD)
    assert len(memtypes) > 0

    list_memtypes = []
    other_memtypes = []
    for mt in memtypes:
        if mt == T_List or isinstance(mt, ListType):
            list_memtypes.append(mt)
        else:
            other_memtypes.append(mt)

    result_memtypes = union_of_list_memtypes(list_memtypes) + union_of_other_memtypes(other_memtypes)

    assert result_memtypes

    if len(result_memtypes) == 1:
        result = result_memtypes.pop()
    else:
        result = UnionType(result_memtypes)

    # print("union of", ', '.join(str(t) for t in types), " = ", result)

    return result

# ------------------------------------------------------------------------------

def union_of_list_memtypes(list_memtypes):

    if len(list_memtypes) <= 1:
        return list_memtypes

    if T_List in list_memtypes:
        # For the purposes of type-union,
        # T_List is basically "List of TBD",
        # and because len(list_memtypes) >= 2,
        # there must be a more specfic list-type in the set,
        # so ignore T_List.
        list_memtypes.remove(T_List)

    if len(list_memtypes) == 1:
        return list_memtypes

    t = ListType(
        union_of_types([
            mt.element_type
            for mt in list_memtypes
        ])
    )

    return [t]

# ------------------------------------------------------------------------------

def union_of_other_memtypes(memtypes):

    if len(memtypes) <= 1:
        return memtypes

    tnodes = []
    for mt in memtypes:
        assert isinstance(mt, Type), mt
        assert not isinstance(mt, UnionType), mt
        assert not isinstance(mt, ListType), mt
        tnodes.append(ensure_tnode_for(mt))

    assert tnodes

    for tnode in tnodes:
        tnode._include_all = True

    result_members = []

    def recurse(tnode):
        # Return True iff all of tnode is included in the union.

        if hasattr(tnode, '_include_all'): return True

        if tnode.children:

            children_included = [
                recurse(child)
                for child in tnode.children
            ]

            if False and trace_this_op:
                print(tnode.type, "children_included = ", children_included)

            if all(children_included):
                tnode._include_all = True
                return True
            else:
                for child in tnode.children:
                    if hasattr(child, '_include_all'):
                        result_members.append(child.type)
                return False

        else:
            return False

    if recurse(troot):
        result_members.append(troot.type)

    for tnode in tnodes:
        anc = tnode
        while anc is not None:
            if hasattr(anc, '_include_all'): del anc._include_all
            anc = anc.parent

    return result_members

# ------------------------------------------------------------------------------

#    global compare_types_f
#    compare_types_f = shared.open_for_output('compare_types')
#
#compare_types_memo = {}
#
#def compare_types(A, B):
#    assert isinstance(A, Type)
#    assert isinstance(B, Type)
#
#    # if A == T_TBD: return (T_TBD, B, T_TBD)
#    # assert B != T_TBD
#
#    if (A,B) in compare_types_memo:
#        return compare_types_memo[(A,B)]
#
#    A_memtypes = A.set_of_types()
#    B_memtypes = B.set_of_types()
#
#    # A few cases that can be handled quickly:
#    if A_memtypes == B_memtypes:
#        A_intersect_B = A # or B
#        A_minus_B     = T_0
#        B_minus_A     = T_0
#
#    elif A_memtypes <= B_memtypes:
#        A_intersect_B = A
#        A_minus_B     = T_0
#        B_minus_A     = maybe_UnionType(B_memtypes - A_memtypes)
#
#    elif B_memtypes <= A_memtypes:
#        A_intersect_B = B
#        A_minus_B     = maybe_UnionType(A_memtypes - B_memtypes)
#        B_minus_A     = T_0
#
#    else:
#        # The general case:
#
#        for (nm, t) in [('A', A_memtypes), ('B', B_memtypes)]:
#            attr_name = 'amount_in_' + nm
#
#            for memtype in t:
#                # Treat T_TBD like Top
#                if memtype == T_TBD: memtype = T_Top_ # assert 0
#                start_tnode = ensure_tnode_for(memtype)
#                start_tnode.__setattr__(attr_name, 'all')
#                tnode = start_tnode.parent
#                while tnode is not None:
#                    if hasattr(tnode, attr_name):
#                        assert tnode.__getattribute__(attr_name) == 'some'
#                        break
#                    tnode.__setattr__(attr_name, 'some')
#                    tnode = tnode.parent
#
#        A_minus_B_memtypes = []
#        A_intersect_B_memtypes = []
#        B_minus_A_memtypes = []
#
#        def recurse(tnode, an_ancestor_is_all_in_A=False, an_ancestor_is_all_in_B=False):
#            assert not (an_ancestor_is_all_in_A and an_ancestor_is_all_in_B)
#
#            if an_ancestor_is_all_in_A:
#                amount_of_this_in_A = 'all'
#            elif hasattr(tnode, 'amount_in_A'):
#                amount_of_this_in_A = tnode.amount_in_A
#                del tnode.amount_in_A
#            else:
#                amount_of_this_in_A = 'none'
#
#            if an_ancestor_is_all_in_B:
#                amount_of_this_in_B = 'all'
#            elif hasattr(tnode, 'amount_in_B'):
#                amount_of_this_in_B = tnode.amount_in_B
#                del tnode.amount_in_B
#            else:
#                amount_of_this_in_B = 'none'
#
#            if amount_of_this_in_A == 'all' and amount_of_this_in_B == 'all':
#                A_intersect_B_memtypes.append(tnode.type)
#
#            elif amount_of_this_in_A == 'all':
#                if amount_of_this_in_B == 'some':
#                    for child in tnode.children:
#                        recurse(child, an_ancestor_is_all_in_A=True)
#                elif amount_of_this_in_B == 'none':
#                    A_minus_B_memtypes.append(tnode.type)
#                else:
#                    assert 0 # can't happen
#
#            elif amount_of_this_in_B == 'all':
#                if amount_of_this_in_A == 'some':
#                    for child in tnode.children:
#                        recurse(child, an_ancestor_is_all_in_B=True)
#                elif amount_of_this_in_A == 'none':
#                    B_minus_A_memtypes.append(tnode.type)
#                else:
#                    assert 0 # can't happen
#
#            elif amount_of_this_in_A == 'some' or amount_of_this_in_B == 'some':
#                for child in tnode.children:
#                    recurse(child)
#
#            elif amount_of_this_in_A == 'none' and amount_of_this_in_B == 'none':
#                # (Neither tnode nor any of its subtypes
#                # is in either A_memtypes or B_memtypes.)
#                pass
#
#            else:
#                assert 0 # can't happen
#
#        recurse(troot)
#
#        A_minus_B     = maybe_UnionType(A_minus_B_memtypes)
#        A_intersect_B = maybe_UnionType(A_intersect_B_memtypes)
#        B_minus_A     = maybe_UnionType(B_minus_A_memtypes)
#
#    assert isinstance(A_minus_B,     Type)
#    assert isinstance(A_intersect_B, Type)
#    assert isinstance(B_minus_A,     Type)
#
#    print("%s :: %s  ===>  %s  ///  %s  ///  %s" %
#        (A, B, A_minus_B, A_intersect_B, B_minus_A),
#        file=compare_types_f)
#
#    result = (A_minus_B, A_intersect_B, B_minus_A)
#    compare_types_memo[(A,B)] = result
#    return result

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

class Env:
    def __init__(self):
        self.vars = {}

    def __str__(self):
        return str(self.vars)

    def copy(self):
        e = Env()
        e.vars = self.vars.copy()
        return e

    def equals(self, other):
        return self.vars == other.vars

    def lookup(self, ex):
        return self.vars[ex.source_text()]

    def diff(self, other):
        # Show the difference between two envs. (For debugging.)
        self_keys = set(self.vars.keys())
        other_keys = set(other.vars.keys())

        cats_ = defaultdict(list)

        for key in self.vars.keys() | other.vars.keys():
            if key in self.vars and key in other.vars:
                if self.vars[key] == other.vars[key]:
                    cat = 'entries in both, with same value'
                    line = "`%s`: `%s`" % (key, self.vars[key])
                else:
                    cat = 'entries in both, with different value'
                    line = "`%s`: `%s`  vs  `%s`" % (key, self.vars[key], other.vars[key])
            elif key in self.vars:
                cat = 'entries only in L'
                line = "`%s`: `%s`" % (key, self.vars[key])
            elif key in other.vars:
                cat = 'entries only in R'
                line = "`%s`: `%s`" % (key, other.vars[key])
            else:
                assert 0
            cats_[cat].append(line)

        def show_cat(cat):
            print(cat)
            if cat in cats_:
                for line in cats_[cat]:
                    print("    " + line)
            else:
                print("    (none)")
            print()

        show_cat('entries in both, with same value')
        show_cat('entries in both, with different value')
        show_cat('entries only in L')
        show_cat('entries only in R')

    # ----------------------------------------------------------------

    def plus_new_entry(self, var, t):
        if isinstance(var, str):
            var_name = var
        elif isinstance(var, ANode):
            [var_name] = var.children
        else:
            assert 0

        # assert var_name not in self.vars, var_name
        # disabled assertion dur to _f_ in Number.prototype.toExponential
        if var_name in self.vars:
            add_pass_error(
                var,
                f"plus_new_entry for `{var_name}` when it's already in the env!"
            )

        assert isinstance(t, Type)
        e = self.copy()
        e.vars[var_name] = t
        return e

    def with_var_removed(self, var):
        [var_name] = var.children
        assert var_name in self.vars
        e = self.copy()
        del e.vars[var_name]
        return e

    def augmented_with_return_type(self, return_type):
        e = self.copy()
        e.vars['*return*'] = return_type
        return e

    # ----------------------------------------------------------------

    def assert_expr_is_of_type(self, expr, expected_t):
        assert expected_t != T_TBD

        (expr_t, expr_env) = tc_expr(expr, self); assert expr_env is self

        if expected_t == T_numeric_:
            print(expr_t, ':', expr.prod, '<>', expr.source_text(), file=sta_misc_f)

        if expr_t == T_TBD:
            add_pass_error(
                expr,
                "type of `%s` is TBD, asserted to be of type `%s`"
                % (expr.source_text(), expected_t)
            )
        elif expr_t.is_a_subtype_of_or_equal_to(expected_t):
            return expr_t
        elif expected_t == T_not_returned and expr_t in [T_Undefined, T_empty_]:
            # todo: why does EnqueueJob return ~empty~ ?
            return expr_t
        else:
            stderr()
            stderr("assert_expr_is_of_type()")
            stderr("expr      :", expr.source_text())
            stderr("expr_t    :", expr_t)
            stderr("expected_t:", expected_t)
            assert 0
            sys.exit(0)

    # --------

    def ensure_expr_is_of_type(self, expr, expected_t):
        assert expected_t != T_TBD

        (expr_type, expr_env) = tc_expr(expr, self)

        if expr_type == T_TBD:
            result_env = expr_env.with_expr_type_replaced(expr, expected_t)

        elif expr_type.is_a_subtype_of_or_equal_to(expected_t):
            # great!
            result_env = expr_env

        else:
            expr_text = expr.source_text()
            add_pass_error(
                expr,
                "%s has type %s, but this context expects that it be of type %s"
                % (expr_text, expr_type, expected_t)
            )
            if expr_text == '*null*':
                # Don't try to change the type of *null*!
                result_env = expr_env
            elif expr_text == '_len_' and expr_type == T_Integer_ and expected_t == T_Tangible_:
                # skip this for now
                result_env = expr_env
            else:
                result_env = expr_env.with_expr_type_replaced(expr, expected_t)
        return result_env

    def ensure_A_can_be_element_of_list_B(self, item_ex, list_ex):
        (list_type, list_env) = tc_expr(list_ex, self); assert list_env is self
        (item_type, item_env) = tc_expr(item_ex, self)

        if (list_type == T_List or list_type == ListType(T_TBD)) and item_type == T_TBD:
            # shrug
            result = item_env

        # ----------------------------------------
        # cases where we change the ST of list_ex:

        elif list_type == T_List or list_type == ListType(T_TBD) or list_type == T_TBD:
            result = item_env.with_expr_type_replaced( list_ex, ListType(item_type))

        elif list_type == ListType(T_String) and item_type == T_Symbol:
            result = item_env.with_expr_type_replaced( list_ex, ListType(T_String | T_Symbol))

        elif list_type == ListType(T_PromiseReaction_Record) | T_Undefined and item_type == T_PromiseReaction_Record:
            result = item_env.with_expr_type_narrowed(list_ex, ListType(T_PromiseReaction_Record))

        # ----------------------------------------
        # cases where we change the ST of item_ex:

        elif item_type == T_TBD:
            result = item_env.with_expr_type_replaced(item_ex, list_type.element_type)

        elif list_type == ListType(T_String) and item_type == ListType(T_code_unit_):
            # TemplateStrings
            result = item_env.with_expr_type_replaced(item_ex, T_String)

        elif list_type == ListType(T_String) and item_type == T_String | T_Null:
            # ParseModule
            result = item_env.with_expr_type_replaced(item_ex, T_String)

        # ----------------------------------------
        # cases where we don't change either ST:

        elif list_type == ListType(T_String) and item_type == T_String | T_Symbol:
            # [[Delete]] for module namespace exotic object _O_:
            # If _P_ is an element of _exports_
            # (if _P_ is a Symbol, it just won't be an element of _exports_)
            result = item_env

#        elif list_type == T_Normal and item_type == T_0:
#            # ArgumentListEvaluation
#            env1 = item_env.with_expr_type_narrowed(list_ex, ListType(T_Tangible_))
#            element_type = T_Tangible_
#            assert item_type.is_a_subtype_of_or_equal_to(element_type)
#            result = env1

        elif list_type == ListType(T_String) and item_type == ListType(T_code_unit_) | T_code_unit_ | T_Undefined:
            # TemplateStrings
            # The "Undefined" alternative can't actially happen,
            # but STA can't see that.
            result = item_env

        else:
            # use list_type to check type of item_ex
            assert list_type.is_a_subtype_of_or_equal_to(T_List)
            element_type = list_type.element_type
            assert item_type.is_a_subtype_of_or_equal_to(element_type)
            result = item_env
        return result

    def with_expr_type_replaced(self, expr, new_t):
        assert isinstance(new_t, Type)
        #
        expr_text = expr.source_text()
        if expr_text in self.vars:
            old_t = self.vars[expr_text]
            assert new_t != old_t

            if (
                old_t == T_TBD and new_t != T_TBD
                or
                old_t == T_not_passed and new_t != T_not_passed
                or
                old_t == T_Top_ and new_t == T_Null | T_String
                # ExportEntriesForModule
                or
                old_t == T_Top_ and new_t == T_Object
                # AtomicLoad
                or
                old_t == T_Top_ and new_t == T_Tangible_
                # GeneratorResumeAbrupt
                or
                old_t == T_List and isinstance(new_t, ListType)
                or
                old_t == T_Tangible_ and new_t in [T_String, T_Boolean, T_Symbol, T_Object] # SameValueNonNumber
                or
                old_t == T_Tangible_ and new_t == T_Number # SameValue, co-ordinated types
                or
                old_t == ListType(T_String) and new_t == ListType(T_String | T_Symbol) # OrdinaryOwnPropertyKeys, maybe others
                #or
                #old_t == T_0 and new_t == T_ResolvedBinding_Record
                ## ResolveExport
                or
                old_t == T_Data_Block | T_Shared_Data_Block and new_t == T_Shared_Data_Block and expr_text == '_toBlock_' # CopyDataBlockBytes, because I can't handle co-ordinated types
                or
                old_t == T_Data_Block | T_Shared_Data_Block | T_Null and (
                    new_t == T_Shared_Data_Block
                        # GetModifySetValueInBuffer, because I can't represent the effect of IsSharedArrayBuffer
                    or
                    new_t == T_Data_Block
                        # SetValueInBuffer, ditto
                )
                or
                old_t == T_Number and new_t == T_Integer_
                    # e.g. ReadModifyWriteSharedMemory{ ... [[ElementSize]]: _elementSize_. ...}
                    # in GetModifySetValueInBuffer
                or
                old_t == ListType(T_PTN_ForBinding) and old_t.is_a_subtype_of_or_equal_to(new_t) # VarScopedDeclarations
                or
                old_t == T_Boolean | T_not_set and new_t == T_Boolean
                # ContainsDuplicateLabels, because of re-use of _hasDuplicates_
                or
                old_t == ListType(ListType(T_code_unit_) | T_String) and new_t == ListType(T_String)
                # TemplateStrings
                or
                old_t == T_Tangible_ | T_not_set and new_t == T_Tangible_
                # CaseBlockEvaluation, will go away with refactoring
                or
                old_t == T_empty_ and new_t == ptn_type_for('MethodDefinition')
                # ClassDefinitionEvaluation
                or
                old_t == T_Normal and new_t == T_methodDef_record_
                # ClassDefinitionEvaluation
                or
                old_t == T_Property_Descriptor | T_Undefined and new_t == T_Property_Descriptor
                # CreateGlobalFunctionBinding
                or
                old_t == ptn_type_for('AssignmentPattern') | T_not_set and new_t == T_Parse_Node
                # ForIn/OfBodyEvaluation
                or
                old_t == T_Boolean | T_Environment_Record | T_Number | T_Object | T_String | T_Symbol | T_Undefined and new_t == T_Object
                # GetValue. (Fix by replacing T_Reference with ReferenceType(base_type)?)
                or
                old_t == T_Abrupt | T_Boolean | T_Intangible_ | T_Null | T_Number | T_Object | T_String | T_Symbol and new_t == T_Lexical_Environment
                # InitializeBoundName
                or
                old_t == T_Normal and new_t == T_Tangible_
                # PropertyDefinitionEvaluation
                or
                old_t == ListType(T_TBD) and new_t == ListType(T_Tangible_)
                # ArgumentListEvaluation
                or
                old_t | T_Abrupt == new_t
                or
                old_t | T_throw_ == new_t
                or
                old_t == T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation for TemplateLiteral
                or
                expr_text in ['_test_', '_increment_'] and new_t == T_Parse_Node
                or
                old_t == T_Lexical_Environment | T_Undefined and new_t == T_Lexical_Environment
                # IteratorBindingInitialization
                or
                old_t == T_String | T_Symbol | T_Undefined and new_t == T_String | T_Symbol
                # ValidateAndApplyPropertyDescriptor
                or
                old_t == ListType(T_code_unit_) and new_t == T_String
                # TemplateStrings
                or
                old_t == T_Tangible_ and new_t == T_function_object_
                # [[Construct]]
                or
                old_t == T_Null | T_Object and new_t == T_Object
                # [[Construct]]
                or
                old_t == T_Tangible_ | T_empty_ and new_t == T_Tangible_
                # ??
                or
                old_t == T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                or old_t == ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # Evaluation of TemplateLiteral : TemplateHead Expression TemplateSpans
                or
                old_t == ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation of TemplateMiddleList : TemplateMiddleList TemplateMiddle Expression
                or
                old_t == T_Tangible_ | T_empty_ and new_t == T_String | T_Symbol
                # DefineMethod
                or
                old_t == ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ and new_t == T_String | T_Symbol
                # DefineMethod
                or
                old_t == T_Tangible_ and new_t == T_numeric_
                # ArraySetLength
                or
                old_t == T_Integer_ | T_Tangible_ | T_code_unit_ and new_t == T_Integer_ | T_Number | T_code_unit_
                # [[DefineOwnProperty]]
                or
                old_t == T_Tangible_ | T_code_unit_ and new_t == T_Number | T_code_unit_
                or
                old_t == T_String | T_Undefined and new_t == T_String
                # GeneratorResume
                or
                old_t == T_CharSet | ThrowType(T_SyntaxError) and new_t == T_CharSet
                or
                old_t == ListType(T_Tangible_) and new_t == ListType(T_String)
                # InternalizeJSONProperty
                or
                old_t == T_Abrupt | T_Boolean | T_Intangible_ | T_Null | T_Number | T_Object | T_String | T_Symbol and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # SerializeJSONObject
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_)
                # TemplateStrings
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_) | T_String | T_code_unit_
                # Evaluation of SubstitutionTemplate
                or
                old_t == ListType(T_code_unit_) | T_Undefined | T_code_unit_ and new_t == ListType(T_code_unit_) | T_String
                # Evaluation of TemplateMiddleList
                or
                old_t == T_Abrupt | T_Tangible_ | T_empty_ and new_t == T_Abrupt | T_Tangible_
                # AsyncGeneratorResumeNext
                or
                old_t == T_Undefined and new_t == T_Object #???
                # Evaluation (YieldExpression)

            ):
                pass
            else:
                stderr()
                stderr("with_expr_type_replaced")
                stderr("expr :", expr_text)
                stderr("old_t:", old_t)
                stderr("new_t:", new_t)
                # assert 0
                # sys.exit(0)
        else:
            assert expr_text in [
                '? CaseClauseIsSelected(_C_, _input_)', # Evaluation (CaseBlock)
                '? Get(_obj_, `"length"`)',
                '? GetValue(_defaultValue_)', # DestructuringAssignmentEvaluation, bleah
                '? InnerModuleEvaluation(_requiredModule_, _stack_, _index_)', # InnerModuleEvaluation
                '? InnerModuleInstantiation(_requiredModule_, _stack_, _index_)', # InnerModuleInstantiation
                '? IteratorValue(_innerResult_)', # Evaluation of YieldExpression
                '? IteratorValue(_innerReturnResult_)', # Evaluation of YieldExpression
                'StringValue of |Identifier|',
                'ToInteger(_P_)', # [[OwnPropertyKeys]]
                'ToNumber(_x_)', # Abstract Equality Comparison
                'ToNumber(_y_)', # Abstract Equality Comparison
                'ToPrimitive(_x_)',
                'ToPrimitive(_y_)',
                'ToPropertyKey(_lval_)',
                '_cookedStrings_[_index_]', # because of TemplateStrings return type
                '_e_.[[LocalName]]', # ResolveExport
                '_ee_.[[LocalName]]',
                '_module_.[[DFSAncestorIndex]]', # InnerModuleEvaluation
                '_module_.[[DFSIndex]]', # InnerModuleEvaluation
                '_rawStrings_[_index_]', # ResolveExport
                '_requiredModule_.[[DFSAncestorIndex]]', # InnerModuleEvaluation
                '_scriptRecord_.[[Realm]]',
                '_throwawayCapability_.[[Promise]]', # AsyncFunctionAwait
                'the MV of |DecimalDigits|',
                'the MV of |StrUnsignedDecimalLiteral|',
                'the TV of |TemplateCharacter|',
                'the TV of |TemplateCharacters|',
                'the TV of |NoSubstitutionTemplate|',
                'the VarDeclaredNames of |Statement|',
                'the VarScopedDeclarations of |Statement|',
                'the result of evaluating _body_', # PerformEval
                'the result of evaluating |AtomEscape|',
                'the result of evaluating |AtomEscape| with argument _direction_',
                'the result of evaluating |Atom|',
                'the result of evaluating |Atom| with argument _direction_',
                'the result of evaluating |CharacterClassEscape|',
                'the result of evaluating |CharacterEscape|',
                'the result of evaluating |ClassAtom|',
                'the result of evaluating |ClassAtomNoDash|',
                'the result of evaluating |ClassEscape|',
                'the result of evaluating |Disjunction|',
                'the result of evaluating |Disjunction| with argument _direction_',
                'the result of evaluating |LeadSurrogate|',
                'the result of evaluating |NonSurrogate|',
                'the result of evaluating |NonemptyClassRanges|',
                'the result of evaluating |TrailSurrogate|',
                'the result of performing IteratorDestructuringAssignmentEvaluation of |AssignmentRestElement| with _iteratorRecord_ as the argument',
                'the result of performing IteratorDestructuringAssignmentEvaluation of |Elision| with _iteratorRecord_ as the argument', # hm
                '(16 times the MV of the first |HexDigit|) plus the MV of the second |HexDigit|',
                '(0x1000 times the MV of the first |HexDigit|) plus (0x100 times the MV of the second |HexDigit|) plus (0x10 times the MV of the third |HexDigit|) plus the MV of the fourth |HexDigit|',
                '_f_ + 1', # Number.prototype.toExponential
                '_f_ + 1 - _k_', # Number.prototype.toFixed
                '_k_ - _f_', # toFixed
                '_p_ - 1', # toPrecision
                '_p_ - (_e_ + 1)', # toPrecision
                '_srcBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
                '_targetBuffer_.[[ArrayBufferData]]', # %TypedArray%.prototype.set
            ], expr_text.encode('unicode_escape')
        #
        e = self.copy()
        e.vars[expr_text] = new_t
        return e

    def set_A_to_B(self, settable, expr):
        (settable_type, env1) = tc_expr(settable, self)
        (expr_type,     env2) = tc_expr(expr,     env1)

        if settable_type == T_TBD and expr_type == T_TBD:
            assert 0

        elif settable_type == T_TBD:
            # flow type info from expr to settable
            return self.with_expr_type_replaced(settable, expr_type)

        elif expr_type == T_TBD:
            # flow type info from settable to expr
            # this is questionable
            return self.with_expr_type_replaced(expr, settable_type)

        elif expr_type == settable_type:
            return env2

        elif expr_type == T_List and isinstance(settable_type, ListType):
            # E.g., expr is an empty List constructor
            # XXX Still need this?
            return env2

        else:
            # ??:
            # settable_type is mostly irrelevant,
            # unless we distinguish the type that a settable is *allowed* to have,
            # versus the type that it happens to have right now.
            #
            # parameters:
            #     - _iSL_ (optional) List of SlotName_
            #   1.If _iSL_ was not provided, set _iSL_ to a new empty List
            # Setting _iSL_ does change the type that it has after that command,
            # but it shouldn't change the declared type of the parameter.
            # But we use exit envs to infer changes to the parameter types.
            # (which makes sense when their declared type is TBD, or maybe just 'List',
            # but not so much otherwise.

            # XXX If the settable is a DOTTING, we should disallow
            # an expr_t that is outside the allowed type of the dotting

            settable_text = settable.source_text()
            if expr_type.is_a_subtype_of_or_equal_to(settable_type):
                # A change, but probably not worth mentioning
                pass
            elif settable_type == T_not_passed:
                # "If _foo_ was not passed, set _foo_ to X."
                # Not worth warning about type-change.
                pass
            else:
                add_pass_error(
                    settable,
                    "warning: Set `%s` changes type from `%s` to `%s`" %
                    (settable_text, settable_type, expr_type)
                )
            e = env2.copy()
            e.vars[settable_text] = expr_type
            return e

    # ----------------------------------------------------------------

    def with_expr_type_narrowed(self, expr, narrower_t):
        assert isinstance(narrower_t, Type)
        (expr_t, env1) = tc_expr(expr, self)

        if expr_t.is_a_subtype_of_or_equal_to(narrower_t):
            # expr is already narrower than required.
            return env1

        # Treat T_TBD like Top:
        if expr_t == T_TBD:
            pass
        elif narrower_t.is_a_subtype_of_or_equal_to(expr_t):
            pass
        elif expr_t == T_Number and narrower_t == T_Integer_:
            # `DateFromTime(_t_) is 1`
            pass
        else:
            stderr("expr type %s cannot be narrowed to %s" % (expr_t, narrower_t))
            assert 0
        #
        expr_text = expr.source_text()
        e = env1.copy()
        e.vars[expr_text] = narrower_t
        return e

    # ----------------------------------------------------------------

    def with_type_test(self, expr, copula, target_t, asserting):
        # Returns a pair of Envs:
        # one in which the the type-test is true, and one in which it's false.
        # i.e.,
        # - one in which the expr's currrent type is narrowed to be <: target_t; and
        # - one in which its type is narrowed to have no intersection with target_t
        # (either respectively or anti-respectively, depending on copula.)

        expr_text = expr.source_text()

        (expr_t, env1) = tc_expr(expr, self)

        # assert env1 is self
        # No, e.g. expr_text is '_R_.[[Value]]', where the out-env
        # has a narrower binding for _R_.

        assert target_t != T_TBD

        (part_inside_target_t, part_outside_target_t) = expr_t.split_by(target_t)

        assert isinstance(part_outside_target_t, Type)
        assert isinstance(part_inside_target_t, Type)

        if asserting:
            if copula == 'is a':
                # We are asserting that the value of `expr` is of the target type.
                # So it'd be nice if the static type of `expr` were a subtype of the target type.
                if part_inside_target_t == T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't be a `%s`"
                        % (expr_text, expr_t, target_t)
                    )

                if part_outside_target_t != T_0:
                    add_pass_error(
                        expr,
                        "STA fails to confirm that %s is a %s; could also be %s" %
                        (expr_text, target_t, part_outside_target_t)
                    )
                    # e.g. a parameter type starts as TBD.
                    # but because the Assert will only propagate the 'true' env,
                    # this error will probably disappear in a later pass.


            elif copula == 'isnt a':
                # We expect that the static type of the expr has no intersection with the target type.

                if part_inside_target_t != T_0:
                    add_pass_error(
                        expr,
                        "ST of `%s` is `%s`, so can't confirm the assertion -- value might be `%s`"
                        % (expr_text, expr_t, part_inside_target_t)
                    )
                assert part_outside_target_t != T_0
            else:
                assert 0, copula
        else:
            # Outside of an assertion,
            # you're presumably doing the type-test
            # with the expectation that either outcome is possible.
            if part_outside_target_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so must be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it must be" % (
                        expr_text, target_t)
                )
                # ResolveExport _starResolution_ loop thing

            if part_inside_target_t == T_0:
                add_pass_error(
                    expr,
                    # XXX "static type is X, so can't be Y"
                    "STA indicates that it's unnecessary to test whether `%s` is %s, because it can't be" % (
                        expr_text, target_t)
                )
                # Perhaps a parameter-type was too restrictive.

        intersect_env = env1.copy()
        nointersect_env = env1.copy()
        intersect_env.vars[expr_text] = part_inside_target_t
        nointersect_env.vars[expr_text] = part_outside_target_t
        # if expr_text == '_Input_' and part_inside_target_t == T_List: assert 0
        # if expr_text == '_Input_' and part_outside_target_t == T_List: assert 0

        if copula == 'is a':
            return (intersect_env, nointersect_env)
        else:
            return (nointersect_env, intersect_env)

    def reduce(self, header_names):
        e = Env()
        for (vn, vt) in self.vars.items():
            if vn in header_names:
                e.vars[vn] = vt
        return e

# ------------------------------------------------------------------------------

def env_and(env1, env2):
    # Return an Env that expresses that both env1 and env2 hold.
    return envs_and([env1, env2])

def envs_and(envs):
    if len(envs) == 0: assert 0
    if len(envs) == 1: return envs[0]

    # optimization:
    if len(envs) == 2 and envs[0].vars == envs[1].vars: return envs[0]

    e = Env()
    vars = set.intersection(*[ set(env.vars.keys()) for env in envs ])
    for expr_text in vars:
        ts = [ env.vars[expr_text] for env in envs ]
        ts = [ t for t in ts if t != T_TBD ]
        if ts == []:
            intersection_t = T_TBD
        else:
            intersection_t = ts[0]
            for t in ts[1:]:
                (intersection_t, _) = intersection_t.split_by(t)
        e.vars[expr_text] = intersection_t
    return e

def env_or(env1, env2):
    # Return an Env that expresses that either env1 or env2 (or both) hold.
    return envs_or([env1, env2])

def envs_or(envs):
    envs = [env for env in envs if env is not None]
    if len(envs) == 0: return None
    if len(envs) == 1: return envs[0]

    e = Env()

    all_vars = set()
    for env in envs:
        for var_name in env.vars.keys():
            all_vars.add(var_name)

    for var_name in sorted(all_vars):
        e.vars[var_name] = union_of_types([
            env.vars[var_name] if var_name in env.vars else T_not_set
            for env in envs
        ])

    return e

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def do_static_type_analysis(levels):

    atexit.register(print_spec_with_errors)

    global split_types_f
    split_types_f = shared.open_for_output('split_types')

    global sta_misc_f
    sta_misc_f = shared.open_for_output('sta_misc')

    global g_level_prefix
    for (L, clusters_on_level_L) in enumerate(levels):
        stderr()
        stderr("X" * 60)
        stderr("X" * 60)
        stderr("level", L)
        time.sleep(1)
        g_level_prefix = '[%d] ' % L
        n_clusters_this_level = len(clusters_on_level_L)
        for (c, cluster) in enumerate(clusters_on_level_L):
            stderr()
            stderr("X" * 50)
            stderr("level %d, cluster %d/%d (%d ops):" %
                (L, c, n_clusters_this_level, len(cluster.members))
            )
            stderr()

            pass_num = 0
            while True:
                pass_num += 1
                stderr()
                stderr("=" * 40)
                stderr("level %d : cluster %d/%d : pass #%d..."
                    % (L, c, n_clusters_this_level, pass_num))
                if pass_num == 5:
                    stderr("giving up")
                    sys.exit(1)
                global pass_errors
                pass_errors = []
                n_ops_changed = 0
                for op_name in cluster.members:
                    changed = tc_operation(op_name)
                    if changed: n_ops_changed += 1
                stderr("%d operations changed" % n_ops_changed)
                if n_ops_changed > 0:
                    # The cluster's static types haven't settled yet.
                    if pass_errors:
                        stderr("discarding %d errors" % len(pass_errors))
                else:
                    # The cluster's static types have hit a fixed point.
                    stderr("achieved fixed point after %d passes" % pass_num)
                    if pass_errors:
                        stderr("accepting %d errors" % len(pass_errors))
                        all_errors.extend(pass_errors)
                    break

        # if L == 1: break

    stderr()
    stderr("Finished static analysis!")
    stderr()

    print_spec_w_edits()

    # Analysis skips the following operations:
    #   SymbolDescriptiveString
    #   ToDateString
    #   GetSubstitution
    #   EscapeRegExpPattern
    # because each of them neither calls nor is called by
    # any other operation, so they don't particpate in any dependency arcs,
    # so they don't appear in the dependency graph.
    # (They're only called by built-ins.)

    # Type-check loops better.

    # Drop the warning for when 'Set' changes the type?

    # For operations with multiple defns (SDOs and CMs),
    # need to remember the return type of each individual defn,
    # then use knowledge of the type of the 'thing'
    # to get the set of defns that might be invoked,
    # and thus a narrower result type than currently.

    # So need to know the grammar.
    # (a) to find that set of defns (note chain rules), and
    # (b) to check {PROD_REF}s like "the second |Expression|".

    # Get rid of Normal?
    # Get rid of Intangible?
    # Introduce Present/Absent dichotomy?
    # Introduce more subtypes?

    # Algorithms for built-ins?

    # Distinguish the declared type (or maximum type) of a variable
    # versus its current type.

# ------------------------------------------------------------------------------

g_level_prefix = '[-] '
pass_errors = []

def add_pass_error(anode, msg):
    global pass_errors
    assert isinstance(anode, ANode)
    print("??:", msg.encode('unicode_escape'))
    pass_errors.append((anode, g_level_prefix + msg))

all_errors = []

def print_spec_with_errors():
    stderr("printing spec_w_errors...")

    things = []
    for (anode, error_msg) in all_errors:
        (sl, sc) = shared.convert_posn_to_linecol(anode.start_posn)
        (el, ec) = shared.convert_posn_to_linecol(anode.end_posn)
        if sl == el:
            thing = (el, sc, ec, error_msg)
        else:
            stderr("Node spans multiple lines: (%d,%d) to (%d,%d)" % (sl,sc,el,ec))
            thing = (el, 0, ec, error_msg)
        things.append(thing)
    things.sort(key=lambda t: (t[0], t[2]))
    # For things on the same line, secondary sort by *end*-column.

    f = shared.open_for_output('spec_w_errors')

    prev_posn = 0
    for (sl, sc, ec, error_msg) in things:
        # print the spec up to and including the newline at the end of line `sl`
        new_posn = shared._newline_posns[sl]+1
        f.write(spec.text[prev_posn:new_posn])
        caret_line = '-' * (sc-1) + '^' * (ec-sc) + '\n'
        f.write(caret_line)
        f.write('>>> ' + error_msg + '\n')
        f.write('\n')
        prev_posn = new_posn

    f.write(spec.text[prev_posn:])
    f.close()

# ------------------------------------------------------------------------------

def print_spec_w_edits():
    stderr('printing spec_w_edits...')

    edits = []

    for (op_name, op) in sorted(operation_named_.items()):
        for header in op.headers:

            def add(pname, ptype):
                node = header.fake_node_for_[pname]
                if ptype != T_0:
                    edit = (node.start_posn, node.end_posn, ptype.unparse())
                else:
                    # delete the line
                    (ln, _) = shared.convert_posn_to_linecol(node.start_posn)
                    edit = (
                        shared._newline_posns[ln-1],
                        shared._newline_posns[ln],
                        ''
                    )
                edits.append(edit)

            for (pname, ptype) in header.parameters.items():
                add(pname, ptype)

            (abrupt_part, normal_part) = header.return_type.split_by(T_Abrupt)
            add('normal', normal_part)
            add('abrupt', abrupt_part)

    edits.sort()

    f = shared.open_for_output('spec_w_edits')
    prev_posn = 0
    for (e_start_posn, e_end_posn, replacement) in edits:
        f.write(spec.text[prev_posn:e_start_posn])
        f.write(replacement)
        prev_posn = e_end_posn
    f.write(spec.text[prev_posn:])
    f.close()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def mytrace(env):
    if env is None:
        print("resulting env is None")
    else:
        # print("resulting env:", env)
        for var_name in [ '_chosenValueRecord_', '_chosenValue_']:
            print("---> %s : %s" % (var_name, env.vars.get(var_name, "(not set)")))
            # assert 'LhsKind' not in str(env.vars.get(var_name, "(not set)"))

def tc_operation(op_name):
    stderr()
    stderr('-' * 30)
    stderr(op_name)

    if op_name in built_in_ops:
        stderr('skipping built-in')
        return False # no change

    if op_name not in operation_named_:
        stderr("skipping for some other reason?")
        return False

    global trace_this_op
    trace_this_op = False
    # trace_this_op = (op_name == 'Tear Free Reads') # and you may want to tweak mytrace just above

    op = operation_named_[op_name]

    any_change = False
    for header in op.headers:
        c = tc_header(header)
        if c: any_change = True
    
    if any_change:
        op.summarize_headers()

    if trace_this_op:
        stderr("ABORTING BECAUSE trace_this_op IS SET.")
        sys.exit(1)

    return any_change

# --------------------------------

def tc_header(header):

    init_env = header.make_env()

    if header.defns == []:
        return False

    final_env = tc_proc(header.name, header.defns, init_env)

    assert final_env is not None

    for (pn, final_t) in final_env.vars.items():
        if final_t == T_TBD:
            add_pass_error(
                header.fake_node_for_[pn],
                "after STA, the type of `%s` is still TBD" % pn
            )

    if init_env.vars == final_env.vars:
        # no change
        return False
    else:
        # Something is different between init_env and final_env,
        # but that doesn't necessarily mean that we're going to change header types
        changed_op_info = False
        for pn in sorted(init_env.vars.keys()):
            init_t = init_env.vars[pn]
            final_t = final_env.vars[pn]

            # if final_t == T_Top_: final_t = T_TBD

            # if init_t == T_TBD and final_t == T_TBD:
            #     add_pass_error(
            #         header.fake_node_for_[pn],
            #         'param %r is still TBD' % (pn,)
            #     )

            # if isinstance(final_t, UnionType) and len(final_t.member_types) >= 12:
            #     print("%s : %s : # member_types = %d" % (header.name, pn, len(final_t.member_types)))

            if init_t == final_t: continue

            # if header.name == 'ToLength': pdb.set_trace()
            # if header.name == 'ArrayCreate': pdb.set_trace()
            if (
                # cases in which we don't want to change header types:
                init_t == ListType(T_code_unit_) and final_t == T_code_unit_ | ListType(T_code_unit_)
                or
                final_t not in [T_TBD, T_0] and init_t == final_t | T_not_passed
                # ObjectCreate's _internalSlotsList_
                # Call's _argumentsList_
                or
                init_t == T_String | T_Symbol and final_t == T_String
                # SetFunctionName
                or
                init_t == T_Abrupt | T_Tangible_ | T_empty_ and final_t == ListType(T_code_unit_) | T_Top_
                # Evaluation
                or
                header.name == 'GetMethod'
                or
                header.name == 'SetRealmGlobalObject' and pn == '_thisValue_' and init_t == T_Tangible_
                or
                header.name == 'SetRealmGlobalObject' and pn == '_globalObj_' and init_t == T_Object | T_Undefined
                or
                header.name == 'UTF16Encoding' and pn == '*return*' and init_t == ListType(T_code_unit_)
                or
                header.name == 'PerformPromiseThen' and pn in ['_onFulfilled_', '_onRejected_'] and init_t == T_Tangible_
                or
                header.name == 'TemplateStrings' and pn == '*return*' and init_t == ListType(T_String)
                or
                header.name == 'Construct' and pn == '_newTarget_' and init_t == T_Tangible_ | T_not_passed
                or
                header.name == 'OrdinaryHasInstance' and pn == '_O_'
                or
                header.name == 'GetIterator' and pn == '_method_'
                or
                header.name == 'ResolveBinding' and pn == '_env_'
                or
                header.name == 'ToLength' and pn == '*return*' and init_t == T_Integer_ | ThrowType(T_TypeError)
                # STA isn't smart enough to detect that the normal return is always integer,
                # wants to change it to Number
                or
                header.name == 'PerformPromiseThen' and pn == '_resultCapability_'
                # STA wants to add T_Undefined, which is in the body type, but not the param type
            ):
                # Don't change header types
                continue
            elif (
                # cases in which we *do* want to change header types:
                # ----
                init_t == T_TBD
                or
                init_t == T_TBD | T_not_passed
                or
                init_t == ListType(T_TBD)
                # ----
                or
                init_t == T_List and isinstance(final_t, ListType)
                or
                init_t.is_a_subtype_of_or_equal_to(final_t)
                # This pass just widened the type.
                # ------
                or
                # This pass just narrowed the type.
                final_t.is_a_subtype_of_or_equal_to(init_t) and (
                    header.name == 'InstantiateFunctionObject'
                    or
                    header.name == 'GetThisBinding' and init_t == T_Tangible_ | ThrowType(T_ReferenceError)
                    or
                    header.name == 'WithBaseObject' and init_t == T_Object | T_Undefined
                )
                # ----
                or
                init_t == T_Tangible_ and header.name == 'SameValueNonNumber'
                or
                init_t == T_Tangible_ and final_t == T_Object | T_Undefined and header.name == 'PrepareForOrdinaryCall'
                # eoh is just wrong
                or
                init_t == T_Tangible_ and final_t == T_Null | T_Object and header.name == 'OrdinarySetPrototypeOf'
                # eoh is just wrong
                or
                init_t == T_Normal and final_t == T_function_object_
                or
                header.name == 'BindingClassDeclarationEvaluation' and init_t == T_Object and final_t == T_function_object_ | T_Abrupt
                or
                header.name == 'MakeConstructor' and init_t == T_function_object_ and final_t == T_constructor_object_
                # or
                # header.name == 'CreatePerIterationEnvironment' and init_t == T_Undefined | T_throw_ and final_t == T_Undefined | ThrowType(T_ReferenceError)
                # # cheater artifact
                # or
                # header.name == 'InitializeReferencedBinding' and init_t == T_Boolean | T_empty_ | T_throw_ and final_t == T_empty_ | T_throw_
                # # cheater artifact
                # or
                # header.name == 'PutValue' and init_t == T_Boolean | T_Undefined | T_empty_ | T_throw_ and final_t == T_Boolean | T_Undefined | T_throw_
                # # cheater artifact
                # or
                # header.name == 'InitializeBoundName' and init_t == T_Boolean | T_Undefined | T_empty_ | T_throw_ and final_t == T_Boolean | T_Undefined | T_throw_
            ):
                # fall through to change the header types
                pass
            else:
                assert 0, (header.name, pn, str(init_t), str(final_t))

            header.change_declared_type(pn, final_t)

            changed_op_info = True

        return changed_op_info

# ------------------------------------------------------------------------------

proc_return_envs_stack = []

def tc_proc(op_name, defns, init_env):
    assert defns

    header_names = sorted(init_env.vars.keys())

    proc_return_envs_stack.append(set())

    for (i, (discriminator, body)) in enumerate(defns):
        if op_name is not None:
            stderr()
            stderr('-' * 20)
            stderr("%s : defn #%d/%d:" % (op_name, i+1, len(defns)))

        if discriminator:
            if isinstance(discriminator, Type):
                stderr(discriminator)
            elif hasattr(discriminator, 'source_text'):
                stderr(discriminator.source_text())
            else:
                assert 0
        else:
            stderr('(no discriminator)')
        stderr()

        if body.prod.lhs_s in ['{EMU_ALG_BODY}', '{IAO_BODY}', '{IND_COMMANDS}']:
            # kludge:
            if (
                discriminator is not None
                and
                isinstance(discriminator, HTML.HNode)
                and
                discriminator.element_name == 'p'
            ):
                assert discriminator.source_text().startswith('<p>The production <emu-grammar type="example">A : A @ B</emu-grammar>, where @ is ')
                init_env1 = init_env.plus_new_entry('_A_', T_Parse_Node).plus_new_entry('_B_', T_Parse_Node)
            else:
                init_env1 = init_env
            assert tc_nonvalue(body, init_env1) is None
        elif body.prod.lhs_s in ['{EXPR}', '{NAMED_OPERATION_INVOCATION}']:
            (out_t, out_env) = tc_expr(body, init_env)
            proc_add_return(out_env, out_t, body)
        else:
            assert 0, body.prod.lhs_s

    proc_return_envs = proc_return_envs_stack.pop()

    rr_envs = []
    for return_env in proc_return_envs:
        rr_envs.append(return_env.reduce(header_names))
    final_env = envs_or(rr_envs)

    assert final_env is not None

    if T_Top_.is_a_subtype_of_or_equal_to(final_env.vars['*return*']):
        print()
        for e in rr_envs:
            print(e.vars['*return*'])
        assert 0, final_env.vars['*return*']

    return final_env

def proc_add_return(env_at_return_point, type_of_returned_value, node):
    if trace_this_op:
        print("Type of returned value:", type_of_returned_value)
        input('hit return to continue ')

    # (or intersect Absent with type_of_returned_value)
#    rt_memtypes = type_of_returned_value.set_of_types()
#    for t in [T_not_set, T_not_passed, T_not_there]:
#        # if t.is_a_subtype_of_or_equal_to(type_of_returned_value):
#        if t in rt_memtypes:
#            add_pass_error(
#                ????,
#                "warning: static type of return value includes `%s`" % str(t)
#            )
    # or, eventually, check that the return value conforms to the proc's declared return

    if type_of_returned_value in [T_Top_, T_Normal]: # , T_TBD]:
        assert 0, str(type_of_returned_value)

    aug_env = env_at_return_point.augmented_with_return_type(type_of_returned_value)

    if 1:
        for (pn, ptype) in sorted(aug_env.vars.items()):
            # if isinstance(ptype, UnionType) and len(ptype.member_types) >= 14:
            #     print("`%s` : # member_types = %d" % (pn, len(ptype.member_types)))
            #     if len(ptype.member_types) == 41: assert 0

            if pn == '*return*' and T_not_returned.is_a_subtype_of_or_equal_to(ptype) and ptype != T_Abrupt | ListType(T_code_unit_) | T_Reference | T_Tangible_ | T_empty_ | T_not_returned:
                add_pass_error(
                    node,
                    "At exit, ST of `%s` is `%s`" % (pn, ptype)
                )

    proc_return_envs_stack[-1].add(aug_env)

# ------------------------------------------------------------------------------

end_the_rep_envs_kludge = None

def tc_nonvalue(anode, env0):
    # Return the env that this construct delivers to the 'next' thing
    # (i.e. when/if control leaves this construct 'normally')
    # If control never leaves this construct normally
    # (e.g., it's a Return command), return None.

    if trace_this_op:
        trace_line = anode.source_text()
        trace_line = re.sub(r'\n *', r'\\n ', trace_line)
        trace_line = trace_line[0:80]
        print()
        print("Entering nv:", anode.prod.lhs_s, trace_line)
        mytrace(env0)

    assert isinstance(anode, ANode)
    assert env0 is None or isinstance(env0, Env)
    # But if it's None, you're not going to be able to do much!

    # if anode.prod.lhs_s == '{COMMAND}': stderr('>>>', anode.source_text())

    p = str(anode.prod)
    children = anode.children

    if p in [
        r'{IND_COMMANDS} : {_INDENT}{COMMANDS}{_OUTDENT}',
        r'{COMMANDS} : {_NL_N} {COMMAND}',
        r'{COMMAND} : {IF_CLOSED}',
        r'{COMMAND} : {IF_OTHER}',
        r'{ELSE_PART} : Else, {SMALL_COMMAND}\.',
        r'{ELSE_PART} : Else,{IND_COMMANDS}',
        r'{ELSE_PART} : Otherwise,? {SMALL_COMMAND}\.',
    ]:
        [child] = children
        result = tc_nonvalue(child, env0)

    elif p == r'{EMU_ALG_BODY} : {IND_COMMANDS}{_NL} +':
        [ind_commands] = children
        env1 = tc_nonvalue(ind_commands, env0)
        if env1 is not None:
            # Control falls off the end of the algorithm.
            proc_add_return(env1, T_not_returned, ind_commands)
            # spec says we should assume Undefined (wait, does it?), but I don't feel like it.
            result = None
        else:
            # All control paths end with a 'Return'
            result = None

    elif p == r'{COMMANDS} : {COMMANDS}{_NL_N} {COMMAND}':
        [commands, command] = children
        env1 = tc_nonvalue(commands, env0)
        env2 = tc_nonvalue(command, env1)
        result = env2

    # ---------------------------------
    # constructs that create a metavariable

    # Let {VAR} be ...

    elif p in [
        r"{COMMAND} : Let {VAR} be {EXPR}\. Remove that record from {VAR}\.",
        r"{COMMAND} : Let {VAR} be {EXPR}\. This variable will be used throughout the algorithms in {EMU_XREF}\.",
        r"{COMMAND} : Let {VAR} be {EXPR}\. \(It may be evaluated repeatedly.\)",
        r"{COMMAND} : Let {VAR} be {EXPR}\.",
        r"{COMMAND} : Let {VAR} be {MULTILINE_EXPR}",
        r"{SMALL_COMMAND} : let {VAR} be {EXPR}",
        r"{SMALL_COMMAND} : let {VAR} be {EXPR}, indicating that an ordinary object should be created as the global object",
        r"{SMALL_COMMAND} : let {VAR} be {EXPR}, indicating that {VAR}'s global `this` binding should be the global object",
    ]:
        [var, expr] = children[0:2]
        [var_name] = var.children

        (expr_t, env1) = tc_expr(expr, env0)

        if var_name in env0.vars:
            add_pass_error(
                anode,
                "re-Let on existing var `%s`. Use Set?" % var_name
            )
            var_t = env0.vars[var_name]
            if expr_t == var_t:
                # but at least we're not changing the type
                result = env1
            elif expr_t == T_TBD:
                result = env1
                add_pass_error(
                    anode,
                    "... also, ignoring the attempt to change the type of var to %s" % str(expr_t)
                )
            elif var_name in ['_v_', '_value_'] and var_t in [T_Normal, T_Tangible_ | T_not_set] and expr_t == T_Undefined:
                # IteratorBindingInitialization, IteratorDestructuringAssignmentEvaluation, others?:
                # This isn't a re-Let,
                # because it's never the case that _v_ is already defined at this point,
                # but my STA isn't smart enough to know that.
                add_pass_error(
                    anode,
                    "... actually, it isn't, but STA isn't smart enough"
                )
                result = env1
            elif expr_t.is_a_subtype_of_or_equal_to(var_t):
                add_pass_error(
                    anode,
                    "... also, this narrows the type of var from %s to %s" % (var_t, expr_t)
                )
                result = env1.with_expr_type_narrowed(var, expr_t)
            else:
                add_pass_error(
                    anode,
                    "... also, this changes the type of var from %s to %s" % (var_t, expr_t)
                )
                result = env1.with_expr_type_replaced(var, expr_t)
        else:
            # The normal case.
            result = env1.plus_new_entry(var, expr_t)

    elif p in [
        r"{COMMAND} : Let {VAR} be {EXPR}\. Because {VAR} and {VAR} are primitive values evaluation order is not important\.",
        r"{COMMAND} : Let {VAR} be {EXPR}\. \(This is the same value as {EMU_XREF}'s {VAR}.\)",
    ]:
        [let_var, expr] = children[0:2]
        (t, env1) = tc_expr(expr, env0)
        result = env1.plus_new_entry(let_var, t)

    elif p in [
        r"{COMMAND} : Let {VAR} be equivalent to a function that throws {VAR}\.",
        r"{COMMAND} : Let {VAR} be equivalent to a function that returns {VAR}\.",
    ]:
        [let_var, rvar] = children
        env0.assert_expr_is_of_type(rvar, T_Tangible_)
        result = env0.plus_new_entry(let_var, T_function_object_)

    elif p == r"{COMMAND} : Let {VAR} be {EXPR}\. \(However, if {VAR} is 10 and {VAR} contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit, at the option of the implementation; and if {VAR} is not 2, 4, 8, 10, 16, or 32, then {VAR} may be an implementation-dependent approximation to the mathematical integer value that is represented by {VAR} in radix-{VAR} notation.\)":
        [let_var, expr, rvar, zvar, rvar2, let_var2, zvar2, rvar3] = children
        assert same_source_text(let_var, let_var2)
        assert same_source_text(rvar, rvar2)
        assert same_source_text(rvar, rvar3)
        assert same_source_text(zvar, zvar2)
        (t, env1) = tc_expr(expr, env0)
        result = env1.plus_new_entry(let_var, t)

    elif p == r'{COMMAND} : Let {VAR} be {EXPR}, and let {VAR} be {EXPR}\.':
        [let_var1, expr1, let_var2, expr2] = children
        (t1, env1) = tc_expr(expr1, env0) # ; assert env1 is env0 disable assert due to toFixed
        (t2, env2) = tc_expr(expr2, env1) # ; assert env2 is env0 disable assert due to toExponential
        result = env2.plus_new_entry(let_var1, t1).plus_new_entry(let_var2, t2)

    elif p == r"{COMMAND} : Let {VAR} be the smallest nonnegative integer such that {CONDITION}\.":
        [var, cond] = children
        env_for_cond = env0.plus_new_entry(var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, env_for_cond); assert t_env.equals(env_for_cond); assert f_env.equals(env_for_cond)
        result = t_env

    elif p in [
        r"{COMMAND} : Let {VAR} be the smallest nonnegative integer such that {CONDITION}\. \(There must be such a {VAR}, for neither String is a prefix of the other.\)",
    ]:
        [let_var, cond] = children[0:2]
        env_for_cond = env0.plus_new_entry(let_var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        result = t_env

    elif p == r"{COMMAND} : Let {VAR} be an integer for which {NUM_EXPR} is as close to zero as possible. If there are two such {VAR}, pick the larger {VAR}\.":
        [let_var, num_expr, var2, var3] = children
        assert same_source_text(var2, let_var)
        assert same_source_text(var3, let_var)
        new_env = env0.plus_new_entry(let_var, T_Integer_)
        (num_t, num_env) = tc_expr(num_expr, new_env)
        assert num_t.is_a_subtype_of_or_equal_to(T_transitioning_from_Number_to_MathReal)
        result = num_env


#    elif p == r'{COMMAND} : Let {SAB_FUNCTION} be {EX}\.':
#        [sab_fn, ex] = children
#        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
#        # result = env0.plus_new_entry(sab_fn, ex_t) # XXX doesn't work
#        result = env1

    # Let {VAR} and {VAR} ... be ...

    elif p == r"{COMMAND} : Let {VAR} and {VAR} be {LITERAL}\.":
        [alet, blet, lit] = children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        result = env0.plus_new_entry(alet, lit_type).plus_new_entry(blet, lit_type)

    elif p == r"{COMMAND} : Let {VAR} and {VAR} be new Synchronize events\.":
        [alet, blet] = children
        result = env0.plus_new_entry(alet, T_Synchronize_event).plus_new_entry(blet, T_Synchronize_event)

    elif p == r"{COMMAND} : Let {VAR} and {VAR} be the indirection values provided when this binding for {VAR} was created\.":
        [m_var, n2_var, n_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        result = env0.plus_new_entry(m_var, T_Module_Record).plus_new_entry(n2_var, T_String)

    elif p == r"{COMMAND} : Let {VAR} and {VAR} be integers such that {CONDITION} and for which {NUM_EXPR} is as close to zero as possible. If there are two such sets of {VAR} and {VAR}, pick the {VAR} and {VAR} for which {PRODUCT} is larger\.":
        [e_var, n_var, cond, num_expr, e_var2, n_var2, e_var3, n_var3, product] = children
        assert same_source_text(e_var2, e_var)
        assert same_source_text(e_var3, e_var)
        assert same_source_text(n_var2, n_var)
        assert same_source_text(n_var3, n_var)
        new_env = env0.plus_new_entry(e_var, T_Integer_).plus_new_entry(n_var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, new_env)
        t_env.assert_expr_is_of_type(num_expr, T_Number)
        t_env.assert_expr_is_of_type(product, T_Number)
        result = t_env

    elif p in [
        r"{SMALL_COMMAND} : let {VAR}, {VAR}, and {VAR} be integers such that {CONDITION}. Note that {VAR} is the number of digits in the decimal representation of {VAR}, that {VAR} is not divisible by 10, and that the least significant digit of {VAR} is not necessarily uniquely determined by these criteria",
        u"{SMALL_COMMAND} : let {VAR}, {VAR}, and {VAR} be integers such that {CONDITION}. Note that {VAR} is the number of digits in the decimal representation of {VAR}, that {VAR} is not divisible by 10<sub>\u211d</sub>, and that the least significant digit of {VAR} is not necessarily uniquely determined by these criteria",
        r"{COMMAND} : Let {VAR}, {VAR}, and {VAR} be integers such that {CONDITION}. Note that the decimal representation of {VAR} has {SUM} digits, {VAR} is not divisible by 10, and the least significant digit of {VAR} is not necessarily uniquely determined by these criteria\.",
    ]:
        [vara, varb, varc, cond] = children[0:4]
        env_for_cond = (
            env0.plus_new_entry(vara, T_Integer_)
                .plus_new_entry(varb, T_Integer_)
                .plus_new_entry(varc, T_Integer_)
        )
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        result = env_for_cond

    # ---

    elif p == r"{COMMAND} : Remove the first element from {VAR} and let {VAR} be the value of (that|the) element\.":
        [list_var, item_var, _] = children
        list_type = env0.assert_expr_is_of_type(list_var, T_List)
        result = env0.plus_new_entry(item_var, list_type.element_type)

    elif p == r"{COMMAND} : Let {VAR} be the first element of {VAR} and remove that element from {VAR}\.":
        [item_var, list_var, list_var2] = children
        assert same_source_text(list_var, list_var2)
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_Tangible_)) # XXX over-specific
        result = env1.plus_new_entry(item_var, T_Tangible_)

    elif p == r"{COMMAND} : Resume the suspended evaluation of {VAR}\. Let {VAR} be the (value|completion record) returned by the resumed computation\.":
        [ctx_var, b_var, _] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        result = env0.plus_new_entry(b_var, T_Tangible_ | T_Abrupt)

    elif p == r"{COMMAND} : Resume the suspended evaluation of {VAR} using {EX} as the result of the operation that suspended it. Let {VAR} be the (value|completion record) returned by the resumed computation\.":
        [ctx_var, resa_ex, resb_var, _] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env1 = env0.ensure_expr_is_of_type(resa_ex, T_Tangible_ | T_Abrupt)
        result = env1.plus_new_entry(resb_var, T_Tangible_)

    elif p == r"{COMMAND} : {VAR} is an index into the {VAR} character list, derived from {VAR}, matched by {VAR}. Let {VAR} be the smallest index into {VAR} that corresponds to the character at element {VAR} of {VAR}. If {VAR} is greater than or equal to the number of elements in {VAR}, then {VAR} is the number of code units in {VAR}\.":
        # Once, in RegExpBuiltinExec
        # This step is quite odd, because it refers to _Input_,
        # which you wouldn't think would still exist.
        # (It gets defined in the invocation of _matcher_, i.e. of _R_.[[RegExpMatcher]],
        # i.e., of the internal closure returned by the algorithm
        # associated with <emu-grammar>Pattern :: Disjunction</emu-grammar>)
        # todo: move this step to that closure.
        result = env0.plus_new_entry('_eUTF_', T_Integer_)

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain an? (\w+) {VAR}\.":
        [prod_ref, res_type_name, res_var] = children
        res_t = {
            'Matcher'         : T_Matcher,
            'AssertionTester' : T_AssertionTester,
            'CharSet'         : T_CharSet,
            'character'       : T_character_,
            'integer'         : T_Integer_,
        }[res_type_name]
        result = env0.plus_new_entry(res_var, res_t)

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain the three results: an integer {VAR}, an integer \(or &infin;\) {VAR}, and Boolean {VAR}\.":
        [prod_ref, i_var, ii_var, b_var] = children
        result = (env0
            .plus_new_entry(i_var, T_Integer_)
            .plus_new_entry(ii_var, T_Integer_)
            .plus_new_entry(b_var, T_Boolean)
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain the two results: an integer {VAR} and an integer \(or &infin;\) {VAR}\.":
        [prod_ref, i_var, ii_var] = children
        result = (env0
            .plus_new_entry(i_var, T_Integer_)
            .plus_new_entry(ii_var, T_Integer_)
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} to obtain an? (\w+) {VAR} and a Boolean {VAR}\.":
        [prod_ref, a_type, a_var, b_var] = children
        result = ( 
            env0
            .plus_new_entry(a_var, parse_type_string(a_type))
            .plus_new_entry(b_var, T_Boolean)
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} with {PRODUCT} as its {VAR} argument to obtain an? (\w+) {VAR}\.":
        [prod_ref, product, p, r_type, r_var] = children
        assert p.source_text() == '_direction_'
        env0.assert_expr_is_of_type(product, T_Integer_)
        result = (
            env0
            .plus_new_entry(r_var, parse_type_string(r_type))
        )

    elif p == r"{COMMAND} : Evaluate {PROD_REF} with argument {VAR} to obtain an? (\w+) {VAR}\.":
        [prod_ref, arg, r_type, r_var] = children
        assert arg.source_text() == '_direction_'
        env0.assert_expr_is_of_type(arg, T_Integer_)
        result = (
            env0
            .plus_new_entry(r_var, parse_type_string(r_type))
        )

    elif p == r"{COMMAND} : Find a value {VAR} such that {CONDITION}; but if this is not possible \(because some argument is out of range\), return {LITERAL}\.":
        [var, cond, literal] = children
        # once, in MakeDay
        env0.assert_expr_is_of_type(literal, T_Number)
        env1 = env0.plus_new_entry(var, T_Number)
        (t_env, f_env) = tc_cond(cond, env1)
        proc_add_return(env1, T_Number, literal)
        result = env1

    elif p == r'{COMMAND} : Call {PREFIX_PAREN} and let {VAR} be (its result|the resulting Boolean value|the Boolean result|the resulting CharSet)\.':
        [prefix_paren, let_var, result_descr] = children
        (t, env1) = tc_expr(prefix_paren, env0); assert env1 is env0
        # check that t matches result_descr
        result = env1.plus_new_entry(let_var, t)

    elif p == r"{COMMAND} : Search {VAR} for the first occurrence of {VAR} and let {VAR} be the index within {VAR} of the first code unit of the matched substring and let {VAR} be {VAR}. If no occurrences of {VAR} were found, return {VAR}\.":
        [s_var, needle, leta_var, s_var2, letb_var, needle2, needle3, s_var3] = children
        assert same_source_text(s_var, s_var2)
        assert same_source_text(s_var, s_var3)
        assert same_source_text(needle, needle2)
        assert same_source_text(needle, needle3)
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(needle, T_String)
        proc_add_return(env0, T_String, s_var3)
        result = env0.plus_new_entry(leta_var, T_Integer_).plus_new_entry(letb_var, T_String)

    elif p == r"{COMMAND} : Evaluate {NAMED_OPERATION_INVOCATION} \(see {EMU_XREF}\) to obtain a code unit {VAR}\.":
        [noi, _, v] = children
        env0.assert_expr_is_of_type(noi, ListType(T_code_unit_))
        result = env0.plus_new_entry(v, T_code_unit_)

    # ---
    # parse

    elif p == r'{COMMAND} : Parse {VAR} using {NONTERMINAL} as the goal symbol and analyse the parse result for any Early Error conditions. If the parse was successful and no early errors were found, let {VAR} be the resulting parse tree. Otherwise, let {VAR} be a List of one or more {ERROR_TYPE} or {ERROR_TYPE} objects representing the parsing errors and/or early errors. Parsing and early error detection may be interweaved in an implementation-dependent manner. If more than one parsing error or early error is present, the number and ordering of error objects in the list is implementation-dependent, but at least one must be present\.':
        [source_var, nonterminal, result_var1, result_var2, error_type1, error_type2] = children
        env1 = env0.ensure_expr_is_of_type(source_var, T_Unicode_code_points_)
        assert env1 is env0
        assert result_var1.children == result_var2.children
        [error_type1_name] = error_type1.children
        [error_type2_name] = error_type2.children
        result_type = ptn_type_for(nonterminal) | ListType(NamedType(error_type1_name) | NamedType(error_type2_name))
        result = env1.plus_new_entry(result_var1, result_type)

    elif p == r"{COMMAND} : Parse {VAR} using the grammars in {EMU_XREF} and interpreting each of its 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements. The goal symbol for the parse is {NONTERMINAL}. If the result of parsing contains a {NONTERMINAL}, reparse with the goal symbol {NONTERMINAL} and use this result instead. Throw a {ERROR_TYPE} exception if {VAR} did not conform to the grammar, if any elements of {VAR} were not matched by the parse, or if any Early Error conditions exist\.":
        [var, emu_xref, goal_nont, other_nont, goal_nont2, error_type, var2, var3] = children
        assert var.children == var2.children
        assert var.children == var3.children
        env0.assert_expr_is_of_type(var, T_String)
        [error_type_name] = error_type.children
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
        result = env0
        # but no result variable, hm.

    elif p == r"{COMMAND} : Parse {VAR} using the grammars in {EMU_XREF} and interpreting {VAR} as UTF-16 encoded Unicode code points \({EMU_XREF}\). The goal symbol for the parse is {NONTERMINAL}. Throw a {ERROR_TYPE} exception if {VAR} did not conform to the grammar, if any elements of {VAR} were not matched by the parse, or if any Early Error conditions exist\.":
        [var, emu_xref, var2, emu_xref2, goal_nont, error_type, var3, var4] = children
        assert var.children == var2.children
        assert var.children == var3.children
        assert var.children == var4.children
        env0.assert_expr_is_of_type(var, T_String)
        [error_type_name] = error_type.children
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
        result = env0
        # but no result variable, hm.

    # ----------------------------------
    # IF stuff

    elif p in [
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}[;,] (?:else|otherwise),? {SMALL_COMMAND}\.',
        r'{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}\. Otherwise,? {SMALL_COMMAND}\.',
        r"{IF_CLOSED} : If {CONDITION}&mdash;note that these mathematical values are both finite and not both zero&mdash;{SMALL_COMMAND}\. Otherwise, {SMALL_COMMAND}\.",
    ]:
        [cond, t_command, f_command] = children
        (t_env, f_env) = tc_cond(cond, env0)
        t_benv = tc_nonvalue(t_command, t_env)
        f_benv = tc_nonvalue(f_command, f_env)
        result = env_or(t_benv, f_benv)

    elif p == r"{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}; but if {CONDITION}, {SMALL_COMMAND}\.":
        [cond, t_command, cond2, f_command] = children
        assert cond2.source_text() == 'there is no such integer _k_'
        # so "but if {CONDITION}" = "else"
        (t_env, f_env) = tc_cond(cond, env0)
        t_benv = tc_nonvalue(t_command, t_env)
        f_benv = tc_nonvalue(f_command, f_env)
        result = env_or(t_benv, f_benv)

    elif p == r"{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}\. Otherwise,? {SMALL_COMMAND}\. {VAR} will be used throughout the algorithms in {EMU_XREF}. Each element of {VAR} is considered to be a character\.":
        [cond, t_command, f_command, _, _, _] = children
        (t_env, f_env) = tc_cond(cond, env0)
        t_env2 = tc_nonvalue(t_command, t_env)
        f_env2 = tc_nonvalue(f_command, f_env)
        result = env_or(t_env2, f_env2)

    elif p == r'{IF_OTHER} : {IF_OPEN}{IF_TAIL}':
        [if_open, if_tail] = children

        benvs = []

        if if_open.prod.rhs_s in [
            r'If {CONDITION}, {SMALL_COMMAND}\.',
            r'If {CONDITION}, then {SMALL_COMMAND}\.',
            r'If {CONDITION}, then{IND_COMMANDS}',
            r'If {CONDITION}, {MULTILINE_SMALL_COMMAND}',
            r'If {CONDITION}, {SMALL_COMMAND}\. \(A String value {VAR} is a prefix of String value {VAR} if {VAR} can be the string-concatenation of {VAR} and some other String {VAR}. Note that any String is a prefix of itself, because {VAR} may be the empty String.\)',
        ]:
            [condition, then_part] = if_open.children[0:2]
            (t_env, f_env) = tc_cond(condition, env0)
            benvs.append( tc_nonvalue(then_part, t_env) )
        else:
            assert 0, str(if_open.prod)

        while True:
            if if_tail.prod.rhs_s == '{_NL_N} {ELSEIF_PART}{IF_TAIL}':
                [elseif_part, next_if_tail] = if_tail.children
                [condition, then_part] = elseif_part.children
                (t_env, f_env) = tc_cond(condition, f_env)
                benvs.append( tc_nonvalue(then_part, t_env) )
                if_tail = next_if_tail

            elif if_tail.prod.rhs_s == '{_NL_N} {ELSE_PART}':
                [else_part] = if_tail.children
                benvs.append( tc_nonvalue(else_part, f_env) )
                break

            elif if_tail.prod.rhs_s == '{EPSILON}':
                [] = if_tail.children
                # This is like "Else, nothing"
                benvs.append( f_env )
                break

            else:
                assert 0

        result = envs_or(benvs)

        if if_open.source_text() == 'If |BooleanLiteral| is the token `true`, return *true*.':
            # After this step, the possibilities for BooleanLiteral have been exhausted,
            # but that's not obvious from the code.
            # todo: change "If" to "Else"?
            result = None

    elif p in [
        r'{ELSE_PART} : Else {CONDITION},{IND_COMMANDS}',
        r"{ELSE_PART} : Else {CONDITION}, {SMALL_COMMAND}\.",
    ]:
        [cond, commands] = children
        (t_env, f_env) = tc_cond(cond, env0, asserting=True)
        # throw away f_env
        result = tc_nonvalue(commands, t_env)

    # ----------------------------------
    # Returning (normally or abruptly)

    elif p in [
        r"{COMMAND} : Return {EXPR} \(see {EMU_XREF}\)\.",
        r"{COMMAND} : Return {EXPR}\. This call will always return \*true\*\.",
        r"{COMMAND} : Return {EXPR}\.",
        r"{COMMAND} : Return {MULTILINE_EXPR}",
        r"{MULTILINE_SMALL_COMMAND} : return {MULTILINE_EXPR}",
        r"{IAO_BODY} : Returns {EXPR}\.",
        r"{SMALL_COMMAND} : return {EXPR}",
    ]:
        expr = children[0]
        (t1, env1) = tc_expr(expr, env0)
        # assert env1 is env0
        if False and trace_this_op:
            print("Return command's expr has type", t1)
        proc_add_return(env1, t1, anode)
        result = None

    elif p == r"{COMMAND} : Return\.":
        [] = children
        # A "return" statement without a value in an algorithm step
        # means the same thing as: Return NormalCompletion(*undefined*).
        proc_add_return(env0, T_Undefined, anode)
        result = None


    elif p == r'{COMMAND} : Call {PREFIX_PAREN} and return its(?: Matcher)? result\.':
        [prefix_paren] = children
        (t, env1) = tc_expr(prefix_paren, env0); assert env1 is env0
        if anode.source_text().endswith('its Matcher result.'): assert t == T_Matcher
        proc_add_return(env1, t, anode)
        result = None

    elif p == r'{IAO_BODY} : Returns {LITERAL} if {CONDITION}; otherwise returns {LITERAL}\.':
        [t_lit, cond, f_lit] = children
        (t_env, f_env) = tc_cond(cond, env0)
        (t_lit_type, _) = tc_expr(t_lit, env0)
        (f_lit_type, _) = tc_expr(f_lit, env0)
        proc_add_return(t_env, t_lit_type, t_lit)
        proc_add_return(f_env, f_lit_type, f_lit)
        result = None

    elif p in [
        r"{COMMAND} : Throw a {ERROR_TYPE} exception\.",
        r"{SMALL_COMMAND} : throw a {ERROR_TYPE} exception because the structure is cyclical",
        r'{SMALL_COMMAND} : throw a {ERROR_TYPE} exception',
    ]:
        [error_type] = children
        [error_type_name] = error_type.children
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), anode)
        result = None

    # ----------------------------------
    # Iteration

    elif p in [
        r'{COMMAND} : Repeat,{IND_COMMANDS}',
        r"{MULTILINE_SMALL_COMMAND} : repeat:{IND_COMMANDS}",
    ]:
        [commands] = children

        # The only ways to leave a condition-less Repeat
        # are via a Return command or via an 'end the repetition' command.
        global end_the_rep_envs_kludge
        assert end_the_rep_envs_kludge is None
        end_the_rep_envs_kludge = []

        env_at_bottom = tc_nonvalue(commands, env0)

        if end_the_rep_envs_kludge == []:
            # When there's no "end the repetition" command,
            # the only way out is via Return,
            # so there can't be anything (except maybe a NOTE) after the loop.
            result = None
        else:
            # The loop body has (at least) one "end the repetition" command,
            # so the environment after the loop derives from the env at the point of that command.
            assert len(end_the_rep_envs_kludge) == 1
            [end_the_rep_env] = end_the_rep_envs_kludge
            result = end_the_rep_env.reduce(env0.vars.keys())

        end_the_rep_envs_kludge = None

        # XXX Should repeat the analysis, feeding the bottom env to the top,
        # XXX until no change.
        # XXX (and likewise with other loops)


    elif p == r"{SMALL_COMMAND} : end the repetition":
        [] = children
        assert end_the_rep_envs_kludge is not None
        end_the_rep_envs_kludge.append(env0)
        result = None

    elif p == r'{COMMAND} : Repeat, while {CONDITION},?{IND_COMMANDS}':
        [cond, commands] = children
        (t_env, f_env) = tc_cond(cond, env0)
        bottom_env = tc_nonvalue(commands, t_env)
        reduced_bottom_env = bottom_env.reduce(t_env.vars.keys())
        # assert reduced_bottom_env.equals(t_env)
        result = f_env

        # hack!:
        if cond.source_text() == '_matchSucceeded_ is *false*': # in RegExpBuiltinExec
            # This case requires that variable _r_, introduced within the loop,
            # survive the loop.
            # (It doesn't have to survive from one iteration to the next,
            # just from the last iteration to after.)
            result = result.plus_new_entry('_r_', T_State)

    elif p in [
        r'{COMMAND} : For each {EACH_THING}, do{IND_COMMANDS}',
        r'{COMMAND} : For each {EACH_THING}, {SMALL_COMMAND}\.',
        r"{COMMAND} : Repeat, for each {EACH_THING},?{IND_COMMANDS}",
    ]:
        [each_thing, commands] = children

        # generic list:
        if each_thing.prod.rhs_s in [
            r"element {VAR} in {DOTTING}",
            r"element {VAR} in {VAR}",
            r"element {VAR} of {EX}",
            r"element {VAR} of {VAR} in List order",
            r"element {VAR} of {VAR}, in ascending index order",
            r"{VAR} from {VAR} in list order",
            r"{VAR} in {VAR} in List order",
            r"{VAR} in {VAR}",
            r"{VAR} in {VAR}, in original insertion order",
            r"{VAR} in {VAR}, in reverse list order",
            r"{VAR} that is an element of {VAR}",
            r"{VAR} that is an element of {VAR}, in original insertion order",
        ]:
            [loop_var, collection_expr] = each_thing.children
            (list_type, env1) = tc_expr(collection_expr, env0); assert env1 is env0
            if list_type == T_List:
                # want to assert that this doesn't happen,
                # but _kept_ in %TypedArray%.prototype.filter
                element_type = T_TBD
            else:
                assert isinstance(list_type, ListType), list_type
                element_type = list_type.element_type
            env_for_commands = env1.plus_new_entry(loop_var, element_type)

        # ---------------------
        # list of specific type:

        elif each_thing.prod.rhs_s == r"Agent Events Record {VAR} in {DOTTING}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_Agent_Events_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_Agent_Events_Record)

        elif each_thing.prod.rhs_s == r"event {VAR} in {DOTTING}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_event_))
            env_for_commands = env1.plus_new_entry(loop_var, T_event_)

        elif each_thing.prod.rhs_s == r"ExportEntry Record {VAR} in {EX}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_ExportEntry_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_ExportEntry_Record)

        elif each_thing.prod.rhs_s == r"Record { {DSBN}, {DSBN} } {VAR} in {VAR}":
            [dsbn1, dsbn2, loop_var, collection_expr] = each_thing.children
            assert dsbn1.children == ['Module']
            assert dsbn2.children == ['ExportName']
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_ExportResolveSet_Record_))
            env_for_commands = env1.plus_new_entry(loop_var, T_ExportResolveSet_Record_)

        elif each_thing.prod.rhs_s in [
            r"Record { {DSBN}, {DSBN} } {VAR} that is an element of {VAR}",
            r"Record { {DSBN}, {DSBN} } {VAR} that is an element of {VAR}, in original key insertion order",
        ]:
            [dsbn1, dsbn2, loop_var, collection_expr] = each_thing.children
            assert dsbn1.children == ['Key']
            assert dsbn2.children == ['Value']
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_MapData_record_))
            env_for_commands = env1.plus_new_entry(loop_var, T_MapData_record_)

        elif each_thing.prod.rhs_s == 'ImportEntry Record {VAR} in {EX}':
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_ImportEntry_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_ImportEntry_Record)

        elif each_thing.prod.rhs_s == r"Parse Node {VAR} in {VAR}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_Parse_Node))
            env_for_commands = env1.plus_new_entry(loop_var, T_Parse_Node)

        elif each_thing.prod.rhs_s == r"String {VAR} that is an element of {EX}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_String))
            env_for_commands = env1.plus_new_entry(loop_var, T_String)

        elif each_thing.prod.rhs_s == r"module {VAR} in {VAR}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_Module_Record))
            env_for_commands = env1.plus_new_entry(loop_var, T_Module_Record)

        elif each_thing.prod.rhs_s in [
            r"{NONTERMINAL} {VAR} in {VAR}",
            r"{NONTERMINAL} {VAR} in {VAR} \(NOTE: this is another complete iteration of the second {NONTERMINAL}\)",
            r"{NONTERMINAL} {VAR} in order from {VAR}",
        ]:
            [nont, loop_var, collection_expr] = each_thing.children[0:3]
            env0.assert_expr_is_of_type(collection_expr, ListType(T_Parse_Node))
            env_for_commands = env0.plus_new_entry(loop_var, ptn_type_for(nont))

        elif each_thing.prod.rhs_s in [
            r"String {VAR} in {NAMED_OPERATION_INVOCATION}",
            r"String {VAR} in {VAR}, in list order",
            r"String {VAR} in {VAR}",
            r"string {VAR} in {VAR}",
        ]:
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, ListType(T_String))
            env_for_commands = env1.plus_new_entry(loop_var, T_String)

        # ------------------------
        # property keys of an object:

        elif each_thing.prod.rhs_s in [
            r"own property key {VAR} of {VAR} that is an integer index, in ascending numeric index order",
            r"own property key {VAR} of {VAR} that is a String but is not an integer index, in ascending chronological order of property creation",
        ]:
            [loop_var, obj_var] = each_thing.children
            env0.assert_expr_is_of_type(obj_var, T_Object)
            env_for_commands = env0.plus_new_entry(loop_var, T_String)

        elif each_thing.prod.rhs_s == r"own property key {VAR} of {VAR} that is a Symbol, in ascending chronological order of property creation":
            [loop_var, obj_var] = each_thing.children
            env0.assert_expr_is_of_type(obj_var, T_Object)
            env_for_commands = env0.plus_new_entry(loop_var, T_Symbol)

        elif each_thing.prod.rhs_s in [
            r"own property key {VAR} of {VAR} such that {CONDITION}, in ascending numeric index order",
            r"own property key {VAR} of {VAR} such that {CONDITION}, in ascending chronological order of property creation",
        ]:
            [loop_var, obj_var, condition] = each_thing.children
            env0.assert_expr_is_of_type(obj_var, T_Object)
            env1 = env0.plus_new_entry(loop_var, T_String | T_Symbol)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"property of the Global Object specified in clause {EMU_XREF}":
            [emu_xref] = each_thing.children
            # no loop_var!
            env_for_commands = env0

        # -----------------------
        # other collections:

        elif each_thing.prod.rhs_s == r"event {VAR} in {NAMED_OPERATION_INVOCATION}":
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, T_Set)
            env_for_commands = env1.plus_new_entry(loop_var, T_event_)

        elif each_thing.prod.rhs_s == 'code unit {VAR} in {VAR}':
            [loop_var, collection_expr] = each_thing.children
            env1 = env0.ensure_expr_is_of_type(collection_expr, T_String)
            env_for_commands = env1.plus_new_entry(loop_var, T_code_unit_)

        elif each_thing.prod.rhs_s == r"index {VAR} of {VAR}":
            [loop_var, collection_var] = each_thing.children
            env0.assert_expr_is_of_type(collection_var, T_Shared_Data_Block)
            env_for_commands = env0.plus_new_entry(loop_var, T_Integer_)

        elif each_thing.prod.rhs_s == r"ReadSharedMemory or ReadModifyWriteSharedMemory event {VAR} in SharedDataBlockEventSet\({VAR}\)":
            [loop_var, collection_var] = each_thing.children
            env0.assert_expr_is_of_type(collection_var, T_candidate_execution)
            env_for_commands = env0.plus_new_entry(loop_var, T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event)

        elif each_thing.prod.rhs_s == r"field of {VAR} that is present":
            [desc_var] = each_thing.children
            loop_var = None # todo: no loop variable!
            env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
            env_for_commands = env0

        # things from a large (possibly infinite) set, those that satisfy a condition:

        elif each_thing.prod.rhs_s in [
            r"integer {VAR} that satisfies {CONDITION}",
            r"integer {VAR} such that {CONDITION}",
        ]:
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_Integer_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"integer {VAR} starting with 0 such that {CONDITION}, in ascending order":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_Integer_)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"event {VAR} such that {CONDITION}":
            [loop_var, condition] = each_thing.children
            env1 = env0.plus_new_entry(loop_var, T_Shared_Data_Block_event)
            (tenv, fenv) = tc_cond(condition, env1)
            env_for_commands = tenv

        elif each_thing.prod.rhs_s == r"character {VAR} not in set {VAR} where {NAMED_OPERATION_INVOCATION} is in {VAR}":
            [loop_var, charset_var, noi, charset_var2] = each_thing.children
            assert charset_var.children == charset_var2.children
            env0.assert_expr_is_of_type(charset_var, T_CharSet)
            env1 = env0.plus_new_entry(loop_var, T_character_)
            env1.assert_expr_is_of_type(noi, T_character_)
            env_for_commands = env1

        # elif each_thing.prod.rhs_s == r"WriteSharedMemory or ReadModifyWriteSharedMemory event {VAR} in SharedDataBlockEventSet\({VAR}\)":
        # elif each_thing.prod.rhs_s == r"child node {VAR} of this Parse Node":
        # elif each_thing.prod.rhs_s == r"code point {VAR} in {VAR}":
        # elif each_thing.prod.rhs_s == r"code point {VAR} in {VAR}, in order":
        # elif each_thing.prod.rhs_s == r"element {VAR} in {NAMED_OPERATION_INVOCATION}":
        # elif each_thing.prod.rhs_s == r"event {VAR} in {VAR}":
        # elif each_thing.prod.rhs_s == r"integer {VAR} in the range 0&le;{VAR}&lt; {VAR}":
        # elif each_thing.prod.rhs_s == r"pair of events {VAR} and {VAR} in EventSet\({VAR}\)":
        # elif each_thing.prod.rhs_s == r"pair of events {VAR} and {VAR} in HostEventSet\({VAR}\)":
        # elif each_thing.prod.rhs_s == r"pair of events {VAR} and {VAR} in SharedDataBlockEventSet\({VAR}\)":
        # elif each_thing.prod.rhs_s == r"pair of events {VAR} and {VAR} in SharedDataBlockEventSet\({VAR}\) such that {CONDITION}":
        # elif each_thing.prod.rhs_s == r"record {VAR} in {VAR}":
        # elif each_thing.prod.rhs_s == r"{NONTERMINAL} {VAR} that is directly contained in the {NONTERMINAL} of a {NONTERMINAL}, {NONTERMINAL}, or {NONTERMINAL}":
        # elif each_thing.prod.rhs_s == r"{NONTERMINAL} {VAR} that is directly contained in the {NONTERMINAL} of a {NONTERMINAL}, {NONTERMINAL}, or {NONTERMINAL} Contained within {VAR}":

        else:
            stderr()
            stderr("each_thing:")
            stderr('        elif each_thing.prod.rhs_s == r"%s":' % each_thing.prod.rhs_s)
            sys.exit(0)

        env_after_commands = tc_nonvalue(commands, env_for_commands)
        # XXX do I need to feed this back somehow?

        # Assume the loop-var doesn't survive the loop
        # if loop_var:
        #     result = env_after_commands.with_var_removed(loop_var)
        # else:
        #     result = env_after_commands

        # The only variables that 'exit' the loop are those that existed beforehand.
        if env_after_commands is None:
            # happens in Coherent Reads
            result = None
        else:
            names = env0.vars.keys()
            result = env_after_commands.reduce(names)

    # ----------------------------------
    # Assert

    elif p in [
        r'{COMMAND} : Assert: {CONDITION}\.',
        r"{SMALL_COMMAND} : Assert: {CONDITION}",
    ]:
        [condition] = children
        (t_env, f_env) = tc_cond(condition, env0, asserting=True)
        # throw away f_env
        result = t_env

    elif p in [
        r"{COMMAND} : Assert: If {CONDITION}, then {CONDITION}\.",
        r"{COMMAND} : Assert: If {CONDITION}, {CONDITION}\.",
    ]:
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, t1_env, asserting=True)
        result = env_or(f1_env, t2_env)

    elif p == r"{COMMAND} : Assert: Unless {CONDITION}, {CONDITION}\.":
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, f1_env, asserting=True)
        result = env_or(t1_env, t2_env)

    elif p == r"{COMMAND} : Assert: {CONDITION_1} if and only if {CONDITION_1}\.":
        [cond1, cond2] = children
        (t1_env, f1_env) = tc_cond(cond1, env0)
        (t2_env, f2_env) = tc_cond(cond2, env0)
        result = env_or(
            env_and(t1_env, t2_env),
            env_and(f1_env, f2_env)
        )

    # ----------------------------------
    # execution context

    elif p == r'{COMMAND} : Pop {VAR} from the execution context stack. The execution context now on the top of the stack becomes the running execution context\.':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_execution_context)

    elif p == r'{COMMAND} : Push {VAR} on ?to the execution context stack; {VAR} is now the running execution context\.':
        [var1, var2] = children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_execution_context)
        result = env0

    elif p == r'{COMMAND} : Remove {VAR} from the execution context stack and restore the execution context that is at the top of the execution context stack as the running execution context\.':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r"{COMMAND} : Remove {VAR} from the execution context stack and restore {VAR} as the running execution context\.":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_execution_context)
        env0.assert_expr_is_of_type(bvar, T_execution_context)
        result = env0

    elif p == r"{COMMAND} : Resume the context that is now on the top of the execution context stack as the running execution context\.":
        [] = children
        result = env0

    elif p == r"{COMMAND} : Resume the suspended evaluation of {VAR} using {EX} as the result of the operation that suspended it\.":
        [ctx_var, res_ex] = children
        env0.assert_expr_is_of_type(ctx_var, T_execution_context)
        env0.assert_expr_is_of_type(res_ex, T_Tangible_ | T_Abrupt)
        result = env0

    elif p == r"{COMMAND} : Suspend {VAR} and remove it from the execution context stack\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p in [
        r"{COMMAND} : Suspend the currently running execution context\.",
        r"{COMMAND} : Suspend the running execution context and remove it from the execution context stack\.",
    ]:
        [] = children
        result = env0

    elif p == r'{SMALL_COMMAND} : suspend {VAR}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r'{COMMAND} : Suspend {VAR}\.':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_execution_context)

    elif p == r"{COMMAND} : Set the code evaluation state of {VAR} such that when evaluation is resumed for that execution context the following steps will be performed:{IND_COMMANDS}":
        [ec_var, commands] = children
        env0.assert_expr_is_of_type(ec_var, T_execution_context)
        defns = [(None, commands)]
        env_at_bottom = tc_proc(None, defns, env0)
        result = env0

    elif p == r'{COMMAND} : Set the code evaluation state of {VAR} such that when evaluation is resumed with a Completion {VAR} the following steps will be performed:{IND_COMMANDS}':
        [ec_var, comp_var, commands] = children
        env0.assert_expr_is_of_type(ec_var, T_execution_context)
        #
        env_for_commands = env0.plus_new_entry(comp_var, T_Tangible_ | T_throw_)
        defns = [(None, commands)]
        env_at_bottom = tc_proc(None, defns, env_for_commands)
        #
        result = env0

    elif p == r"{COMMAND} : Perform any necessary implementation-defined initialization of {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        result = env0

    elif p == r'{COMMAND} : Once a generator enters the `"completed"` state it never leaves it and its associated execution context is never resumed. Any execution state associated with {VAR} can be discarded at this point\.':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    # ----------------------------------

    elif p in [
        r'{COMMAND} : Set {SETTABLE} to {EXPR}\.',
        r'{COMMAND} : Set {SETTABLE} to {MULTILINE_EXPR}',
        r'{SMALL_COMMAND} : set {SETTABLE} to {EXPR}',
    ]:
        [settable, expr] = children
        result = env0.set_A_to_B(settable, expr)

    elif p == r'{COMMAND} : Set all of the bytes of {VAR} to 0\.':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block)
        result = env1

    elif p == r'{COMMAND} : Wait until no agent is in the critical section for {VAR}, then enter the critical section for {VAR} \(without allowing any other agent to enter\)\.':
        [var1, var2] = children
        [var_name1] = var1.children
        [var_name2] = var2.children
        assert var_name1 == var_name2
        env1 = env0.ensure_expr_is_of_type(var1, T_WaiterList)
        result = env1

    elif p in [
        r"{COMMAND} : Set {VAR}'s essential internal methods to the default ordinary object definitions specified in {EMU_XREF}\.",
        r"{COMMAND} : Set {VAR}'s essential internal methods to the definitions specified in {EMU_XREF}\.",
    ]:
        [var, emu_xref] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        result = env1

    elif p == r'{COMMAND} : Set {DOTTING} to the definition specified in {EMU_XREF}\.':
        [dotting, emu_xref] = children
        (t1, env1) = tc_expr(dotting, env0)
        # should check that the definition in emu_xref has the right signature
        result = env1

    elif p in [
        r"{COMMAND} : Add {EX} as the last element of {VAR}\.",
        r"{COMMAND} : Add {VAR} as an element of the list {VAR}\.",
        r"{COMMAND} : Append {EX} as an element of {VAR}\.",
        r"{COMMAND} : Append {EX} as the last element of the List that is {DOTTING}\.",
        r"{COMMAND} : Append {EX} as the last element of the List {VAR}\.",
        r"{COMMAND} : Append {EX} as the last element of {VAR}\.",
        r"{COMMAND} : Append {EX} to the end of the List {VAR}\.",
        r"{COMMAND} : Append {EX} to the end of {VAR}\.",
        r"{COMMAND} : Append {EX} to {EX}\.",
        r"{COMMAND} : Insert {VAR} as the first element of {VAR}\.",
        r"{SMALL_COMMAND} : append {LITERAL} to {VAR}",
        r"{SMALL_COMMAND} : append {VAR} to {VAR}",
    ]:
        [value_ex, list_ex] = children
        result = env0.ensure_A_can_be_element_of_list_B(value_ex, list_ex)

    elif p in [
        r'{COMMAND} : Append to {VAR} the elements of {EXPR}\.',
        r"{COMMAND} : Append to {VAR} {EXPR}\.",
        r"{COMMAND} : Append all the entries of {VAR} to the end of {VAR}\.",
        r"{COMMAND} : Append each item in {VAR} to the end of {VAR}\.",
    ]:
        [ex1, ex2] = children
        (t1, env1) = tc_expr(ex1,  env0); assert env1 is env0
        (t2, env2) = tc_expr(ex2, env0); assert env2 is env0
        if t1 == T_TBD and t2 == T_TBD:
            pass
        elif t1 == T_List and t2 == T_TBD:
            pass
        elif t1 == T_List and t2 == T_List:
            pass
        elif isinstance(t1, ListType) and t2 == T_TBD:
            env0 = env0.with_expr_type_replaced(ex2, t1)
        elif t1 == T_List and isinstance(t2, ListType):
            env0 = env0.with_expr_type_replaced(ex1, t2)
        elif isinstance(t1, ListType) and isinstance(t2, ListType):
            if t1 == t2:
                pass
            elif 'Append to' in p and t1.is_a_subtype_of_or_equal_to(t2):
                # widen ex1 to be able to accept ex2
                env0 = env0.with_expr_type_replaced(ex1, t2)
            elif ('Append all' in p or 'Append each' in p) and t2.is_a_subtype_of_or_equal_to(t1):
                env0 = env0.with_expr_type_replaced(ex2, t1)
            else:
                assert 0
        else:
            assert t1.is_a_subtype_of_or_equal_to(T_List)
            assert t2.is_a_subtype_of_or_equal_to(T_List)
            assert t1 == t2
        result = env0

    elif p == r"{COMMAND} : Append the pair \(a two element List\) consisting of {VAR} and {VAR} to the end of {VAR}\.":
        [avar, bvar, list_var] = children
        env0.assert_expr_is_of_type(avar, T_String | T_Symbol)
        env0.assert_expr_is_of_type(bvar, T_Property_Descriptor)
        (list_type, env1) = tc_expr(list_var, env0); assert env1 is env0
        assert list_type == T_List
        result = env0.with_expr_type_narrowed(list_var, ListType(ListType(T_TBD)))

    elif p == r'{COMMAND} : Append to {VAR} each element of {VAR} that is not already an element of {VAR}\.':
        [vara, varb, varc] = children
        (vara_type, enva) = tc_expr(vara, env0); assert enva is env0
        (varb_type, envb) = tc_expr(varb, env0); assert envb is env0
        (varc_type, envc) = tc_expr(varc, env0); assert envc is env0
        if vara_type == T_TBD and varb_type == T_TBD and varc_type == T_TBD:
            pass
        else:
            assert vara_type.is_a_subtype_of_or_equal_to(T_List)
            assert vara_type == varb_type
            assert varb_type == varc_type
        result = env0

    elif p == r'{COMMAND} : Set {SETTABLE} as (described|specified) in {EMU_XREF}\.':
        [settable, _, emu_xref] = children
        (t, env1) = tc_expr(settable, env0); assert env1 is env0
        # XXX: could check that emu_xref is sensible for t
        result = env1

    elif p == r'{COMMAND} : Leave the critical section for {VAR}\.':
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        result = env0

    elif p == r'{COMMAND} : Create own properties of {VAR} corresponding to the definitions in {EMU_XREF}\.':
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r'{SMALL_COMMAND} : reverse the order of the elements of {VAR}':
        [var] = children
        result = env0.ensure_expr_is_of_type(var, T_List)

    elif p in [
        r'{COMMAND} : Add {VAR} to {VAR}\.',
        r"{SMALL_COMMAND} : add {VAR} to {VAR}",
    ]:
        [item_var, collection_var] = children
        (item_type, env1) = tc_expr(item_var, env0); assert env1 is env0
        (collection_type, env2) = tc_expr(collection_var, env0); assert env2 is env0
        if item_type.is_a_subtype_of_or_equal_to(T_event_) and collection_type == T_Set:
            pass
        elif item_type == T_character_ and collection_type == T_CharSet:
            pass
        else:
            assert 0
        result = env0

    elif p == r"{COMMAND} : Increment {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        result = env0

    elif p in [
        r'{COMMAND} : Increment {VAR} by {NUM_LITERAL}\.',
        r'{COMMAND} : Decrement {VAR} by {NUM_LITERAL}\.',
        r'{COMMAND} : Increase {VAR} by {NUM_LITERAL}\.',
        r"{COMMAND} : Decrease {VAR} by {NUM_LITERAL}\.",
        r"{SMALL_COMMAND} : increase {VAR} by {NUM_LITERAL}",
    ]:
        [var, num_literal] = children
        env0.assert_expr_is_of_type(num_literal, T_Integer_)
        result = env0.ensure_expr_is_of_type(var, T_Integer_)

    elif p == r'{COMMAND} : Increment {VAR} and {VAR} each by {NUM_LITERAL}\.':
        [vara, varb, num_literal] = children
        env0.assert_expr_is_of_type(num_literal, T_Integer_)
        result = env0.ensure_expr_is_of_type(vara, T_Integer_).ensure_expr_is_of_type(varb, T_Integer_)

    elif p == r'{COMMAND} : NOTE:? .+(?=\.\n)\.':
        result = env0

    elif p == r'{COMMAND} : Create an immutable indirect binding in {VAR} for {VAR} that references {VAR} and {VAR} as its target binding and record that the binding is initialized\.':
        [er_var, n_var, m_var, n2_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(m_var, T_Module_Record)
        env0.assert_expr_is_of_type(n2_var, T_String)
        result = env0

    elif p == r'{COMMAND} : Perform any implementation or host environment defined processing of {VAR}. This may include modifying the {DSBN} field or any other field of {VAR}\.':
        [var1, dsbn, var2] = children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_PendingJob)
        result = env0

    elif p == r"{COMMAND} : Perform any implementation or host environment defined job initialization using {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_PendingJob)
        result = env0

    elif p == r'{COMMAND} : Add {VAR} at the back of the Job Queue named by {VAR}\.':
        [job_var, queue_var] = children
        env0.assert_expr_is_of_type(job_var, T_PendingJob)
        env0.assert_expr_is_of_type(queue_var, T_String)
        result = env0

    elif p == r"{COMMAND} : Set {VAR}'s essential internal methods \(except for {DSBN} and {DSBN}\) to the definitions specified in {EMU_XREF}\.":
        [var, dsbn1, dsbn2, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{SMALL_COMMAND} : store the individual bytes of {VAR} into {VAR}, in order, starting at {VAR}\[{VAR}\]":
        [var1, var2, var3, var4] = children
        env0.assert_expr_is_of_type(var1, ListType(T_Integer_))
        env1 = env0.ensure_expr_is_of_type(var2, T_Data_Block)
        assert var3.children == var2.children
        env0.assert_expr_is_of_type(var4, T_Integer_)
        result = env1

    elif p == r"{COMMAND} : Perform {NAMED_OPERATION_INVOCATION} and suspend {VAR} for up to {VAR} milliseconds, performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost\.  {VAR} can notify either because the timeout expired or because it was notified explicitly by another agent calling NotifyWaiter\({VAR}, {VAR}\), and not for any other reasons at all\.":
        [noi, w_var, t_var, *blah] = children
        env0.assert_expr_is_of_type(noi, T_not_returned)
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(t_var, T_Number)
        result = env0

    elif p in [
        r"{COMMAND} : Perform {NAMED_OPERATION_INVOCATION}\.",
        r"{SMALL_COMMAND} : perform {NAMED_OPERATION_INVOCATION}",
        r"{COMMAND} : Call {PREFIX_PAREN}\.",
    ]:
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded=True)
        if noi_t.is_a_subtype_of_or_equal_to(T_not_returned | T_Undefined | T_empty_):
            pass
        else:
            if 0:
                # disable because it's noisy for no benefit?
                add_pass_error(
                    anode,
                    "`Perform/Call` discards `%s` value"
                    % str(noi_t)
                )
        result = env1

    elif p == r"{COMMAND} : Add the characters in set {VAR} to set {VAR}\.":
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_CharSet)
        env0.assert_expr_is_of_type(var2, T_CharSet)
        result = env0

    elif p == r"{SMALL_COMMAND} : create an own (accessor|data) property named {VAR} of object {VAR} whose {DSBN}, {DSBN}, {DSBN} and {DSBN} attribute values are described by {VAR}. If the value of an attribute field of {VAR} is absent, the attribute of the newly created property is set to its default value":
        [_, name_var, obj_var, *dsbn_, desc_var, desc_var2] = children
        assert desc_var.children == desc_var2.children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(desc_var, T_Property_Descriptor)
        result = env0

    elif p == r"{SMALL_COMMAND} : no further validation is required":
        [] = children
        result = env0

    elif p in [
        r"{SMALL_COMMAND} : convert the property named {VAR} of object {VAR} from a data property to an accessor property. Preserve the existing values of the converted property's {DSBN} and {DSBN} attributes and set the rest of the property's attributes to their default values",
        r"{SMALL_COMMAND} : convert the property named {VAR} of object {VAR} from an accessor property to a data property. Preserve the existing values of the converted property's {DSBN} and {DSBN} attributes and set the rest of the property's attributes to their default values",
    ]:
        [name_var, obj_var, dsbn1, dsbn2] = children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p == r"{SMALL_COMMAND} : set the corresponding attribute of the property named {VAR} of object {VAR} to the value of the field":
        [name_var, obj_var] = children
        env0.ensure_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p in [
        r"{COMMAND} : ReturnIfAbrupt\({EX}\)\.",
        r"{SMALL_COMMAND} : ReturnIfAbrupt\({VAR}\)",
    ]:
        [ex] = children
        (ex_t, env1) = tc_expr(ex, env0); assert env1 is env0
        if ex_t == T_TBD:
            # Doesn't make sense to compare_types
            # And a proc_add_return(..., T_TBD) wouldn't help
            result = env1
        else:
            (normal_part_of_ex_t, abnormal_part_of_ex_t) = ex_t.split_by(T_Normal)
            if normal_part_of_ex_t == T_0:
                add_pass_error(
                    anode,
                    "ST of `%s` is `%s`, so could just Return, rather than ReturnIfAbrupt"
                    % (ex.source_text(), ex_t)
                )
            if abnormal_part_of_ex_t == T_0:
                add_pass_error(
                    anode,
                    "STA indicates that calling RIA is unnecessary, because `%s` can't be abrupt"
                    % ex.source_text()
                )

            proc_add_return(env1, abnormal_part_of_ex_t, anode)
            result = env1.with_expr_type_narrowed(ex, normal_part_of_ex_t)

    elif p == r"{COMMAND} : IfAbruptRejectPromise\({VAR}, {VAR}\)\.":
        [vara, varb] = children
        env0.assert_expr_is_of_type(varb, T_PromiseCapability_Record)
        (ta, tenv) = tc_expr(vara, env0); assert tenv is env0

        env0.assert_expr_is_of_type(vara, T_Normal | T_Abrupt)
        (normal_part_of_ta, abnormal_part_of_ta) = ta.split_by(T_Normal)

        proc_add_return(env0, T_Promise_object_, anode)
        result = env0.with_expr_type_narrowed(vara, normal_part_of_ta)

    elif p == r"{COMMAND} : Set {VAR}'s essential internal methods except for {DSBN} to the default ordinary object definitions specified in {EMU_XREF}\.":
        [var, dsbn, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{COMMAND} : Need to defer setting the {DSBN} attribute to {LITERAL} in case any elements cannot be deleted\.":
        [dsbn, literal] = children
        result = env0

    elif p == r"{COMMAND} : Record that the binding for {VAR} in {VAR} has been initialized\.":
        [key_var, oer_var] = children
        env0.assert_expr_is_of_type(key_var, T_String)
        env0.assert_expr_is_of_type(oer_var, T_Environment_Record)
        result = env0

    elif p in [
        r"{COMMAND} : Create an immutable binding in {VAR} for {VAR} and record that it is uninitialized\. If {VAR} is \*true\*, record that the newly created binding is a strict binding\.",
        r"{COMMAND} : Create a mutable binding in {VAR} for {VAR} and record that it is uninitialized\. If {VAR} is \*true\*, record that the newly created binding may be deleted by a subsequent DeleteBinding call\.",
    ]:
        [er_var, n_var, s_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        result = env0

    elif p == r"{COMMAND} : Set the remainder of {VAR}'s essential internal methods to the default ordinary object definitions specified in {EMU_XREF}\.":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{COMMAND} : Remove the binding for {VAR} from {VAR}\.":
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        result = env0

    elif p == r"{SMALL_COMMAND} : remove that element from the {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Remove the own property with name {VAR} from {VAR}\.":
        [name_var, obj_var] = children
        env0.assert_expr_is_of_type(name_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(obj_var, T_Object)
        result = env0

    elif p == r"{SMALL_COMMAND} : change its bound value to {VAR}":
        # once, in SetMutableBinding
        # elliptical
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        result = env0

    elif p == r"{COMMAND} : Perform an implementation-defined debugging action\.":
        [] = children
        result = env0

    elif p == r"{COMMAND} : Put {VAR} into {VAR} at index {EX}\.":
        [item_var, list_var, index_ex] = children
        list_type = env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        env0.assert_expr_is_of_type(index_ex, T_Integer_)
        result = env0

    elif p in [
        r"{COMMAND} : Remove all occurrences of {VAR} from {VAR}\.",
        r"{COMMAND} : Remove {VAR} from {VAR}\.",
    ]:
        [item_var, list_var] = children
        list_type = env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(item_var, list_type.element_type)
        result = env0

    elif p == r"{IF_CLOSED} : If any static semantics errors are detected for {VAR} or {VAR}, throw a {ERROR_TYPE} or a {ERROR_TYPE} exception, depending on the type of the error\. If {CONDITION}, the Early Error rules for {EMU_GRAMMAR} are applied. Parsing and early error detection may be interweaved in an implementation-dependent manner\.":
        [avar, bvar, error_type1, error_type2, cond, emu_grammar] = children
        env0.assert_expr_is_of_type(avar, T_Parse_Node)
        env0.assert_expr_is_of_type(bvar, T_Parse_Node)
        [error_type_name1] = error_type1.children
        [error_type_name2] = error_type2.children
        proc_add_return(env0, ThrowType(NamedType(error_type_name1)), error_type1)
        (t_env, f_env) = tc_cond(cond, env0); assert t_env.equals(env0); assert f_env.equals(env0)
        result = env0

    elif p == r"{COMMAND} : Order the elements of {VAR} so they are in the same relative order as would be produced by the Iterator that would be returned if the EnumerateObjectProperties internal method were invoked with {VAR}\.":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(bvar, T_Object)
        result = env0

    elif p == r"{COMMAND} : Set fields of {VAR} with the values listed in {EMU_XREF} .+(?=\.\n)\.":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Intrinsics_Record)
        result = env0

    elif p == r"{COMMAND} : Add 1 to {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        result = env0

    elif p == r"{COMMAND} : Remove the last element of {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Remove this element from {VAR}\.":
        # todo: less ellipsis
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        result = env0

    elif p == r"{COMMAND} : Search the enclosing {NONTERMINAL} for an instance of a {NONTERMINAL} for a {NONTERMINAL} which has a StringValue equal to the StringValue of the {NONTERMINAL} contained in {NONTERMINAL}\.":
        [nont1, nont2, nont3, nont4, nont5] = children
        result = env0

    elif p == r"{COMMAND} : Create any implementation-defined global object properties on {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Object)
        result = env0

    elif p == r"{COMMAND} : In an implementation-dependent manner, obtain the ECMAScript source texts \(see clause {EMU_XREF}\) and any associated host-defined values for zero or more ECMAScript scripts and/or ECMAScript modules. For each such {VAR} and {VAR}, do{IND_COMMANDS}":
        [emu_xref, avar, bvar, commands] = children
        env_for_commands = (
            env0
            .plus_new_entry(avar, T_Unicode_code_points_)
            .plus_new_entry(bvar, T_host_defined_)
        )
        result = tc_nonvalue(commands, env_for_commands)

    # -----

    elif p == r"{COMMAND} : Add {VAR} to the end of the list of waiters in {VAR}\.":
        [w, wl] = children
        env0.assert_expr_is_of_type(w, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        result = env0

    elif p == r"{COMMAND} : Remove {VAR} from the list of waiters in {VAR}\.":
        [sig, wl] = children
        env0.assert_expr_is_of_type(sig, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        result = env0

    elif p == r"{COMMAND} : Add {VAR} to the end of {VAR}\.":
        [el, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(el, list_var)
        result = env1

    elif p == r"{COMMAND} : Subtract {NUM_LITERAL} from {VAR}\.":
        [lit, var] = children
        env0.assert_expr_is_of_type(lit, T_Integer_)
        env0.assert_expr_is_of_type(var, T_Integer_)
        result = env0

    elif p == r"{COMMAND} : Notify the agent {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_agent_signifier_)
        result = env0

    elif p == r"{COMMAND} : Replace the element of {VAR} whose value is {VAR} with an element whose value is {LITERAL}\.":
        [list_var, elem_var, lit] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(elem_var, list_var)
        env2 = env1.ensure_A_can_be_element_of_list_B(lit, list_var)
        result = env2

    elif p == r"{COMMAND} : Append the elements of {NAMED_OPERATION_INVOCATION} to the end of {VAR}\.":
        [noi, var] = children
        # over-specific, but it only occurs once, in String.fromCodePoint:
        env0.assert_expr_is_of_type(noi, ListType(T_code_unit_))
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_code_unit_))
        result = env1

    elif p == r"{SMALL_COMMAND} : remove the first code unit from {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    elif p == r"{COMMAND} : Remove the first two code units from {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    elif p == r"{COMMAND} : Let `compareExchange` denote a semantic function of two List of byte values arguments that returns the second argument if the first argument is element-wise equal to {VAR}\.":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_Integer_))
        result = env0

    elif p == r"{COMMAND} : Remove {VAR} from the front of {VAR}\.":
        [el_var, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(el_var, list_var)
        result = env1

    elif p == r"{SMALL_COMMAND} : in left to right order, starting with the second argument, append each argument as the last element of {VAR}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Tangible_))
        result = env1

    elif p == r"{COMMAND} : Append in order the code unit elements of {VAR} to the end of {VAR}\.":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_String)
        env1 = env0.ensure_expr_is_of_type(b, ListType(T_code_unit_))
        result = env1

    elif p == r"{COMMAND} : Append in list order the elements of {VAR} to the end of the List {VAR}\.":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_List)
        env0.assert_expr_is_of_type(b, T_List)
        result = env0

    elif p == r"{COMMAND} : Append {EX} and {EX} to {VAR}\.":
        [pvar, svar, list_var] = children

        # only one occurrence, in RegExp.prototype [ @@replace ]
        assert list_var.source_text() == '_replacerArgs_'

        (list_type, list_env) = tc_expr(list_var, env0); assert list_env is env0
        assert list_type == ListType(T_String)
        # because it was created via: Let _replacerArgs_ be &laquo; _matched_ &raquo;.

        # so this is fine:
        env0.assert_expr_is_of_type(svar, T_String)
        # but this is not:
        env0.assert_expr_is_of_type(pvar, T_Integer_)

        # so generalize the list type:
        result = env0.with_expr_type_replaced(list_var, ListType(T_Tangible_))

    elif p == r"{COMMAND} : No action is required\.":
        [] = children
        result = env0

    elif p == r"{COMMAND} : Parse {VAR} interpreted as UTF-16 encoded Unicode points \({EMU_XREF}\) as a JSON text as specified in ECMA-404. Throw a {ERROR_TYPE} exception if {VAR} is not a valid JSON text as defined in that specification\.":
        [svar, emu_xref, error_type, svar2] = children
        assert same_source_text(svar, svar2)
        env0.assert_expr_is_of_type(svar, T_String)
        result = env0

    elif p == r"{COMMAND} : The code points `/` or any {NONTERMINAL} occurring in the pattern shall be escaped in {VAR} as necessary to ensure that the string-concatenation of {EX}, {EX}, {EX}, and {EX} can be parsed \(in an appropriate lexical context\) as a {NONTERMINAL} that behaves identically to the constructed regular expression. For example, if {VAR} is {STR_LITERAL}, then {VAR} could be {STR_LITERAL} or {STR_LITERAL}, among other possibilities, but not {STR_LITERAL}, because `///` followed by {VAR} would be parsed as a {NONTERMINAL} rather than a {NONTERMINAL}. If {VAR} is the empty String, this specification can be met by letting {VAR} be {STR_LITERAL}\.":
        # XXX
        result = env0

    elif p == r"{SMALL_COMMAND} : append {CU_LITERAL} as the last code unit of {VAR}":
        [cu_lit, var] = children
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        env0.assert_expr_is_of_type(var, T_String)
        result = env0

    # elif p == r"{COMMAND} : Append {EX} and {EX} as the last two elements of {VAR}\.":
    # elif p == r"{COMMAND} : For all {VAR}, {VAR}, and {VAR} in {VAR}'s domain:{IND_COMMANDS}":
    # elif p == r"{COMMAND} : For each {EACH_THING}, if {CONDITION}, then {SMALL_COMMAND}\.":
    # elif p == r"{COMMAND} : Let {SAB_RELATION} be {EX}\.":
    # elif p == r"{COMMAND} : Let {VAR} be {EXPR}\. If {CONDITION}, {VAR} will be the execution context that performed the direct eval. If {CONDITION}, {VAR} will be the execution context for the invocation of the `eval` function.":
    # elif p == r"{COMMAND} : Let {VAR}, {VAR}, and {VAR} be integers such that {CONDITION}. If there are multiple possibilities for {VAR}, choose the value of {VAR} for which {PRODUCT} is closest in value to {VAR}. If there are two such possible values of {VAR}, choose the one that is even\.":
    # elif p == r"{COMMAND} : Order the elements of {VAR} so they are in the same relative order as would be produced by the Iterator that would be returned if the EnumerateObjectProperties internal method was invoked with {VAR}\.":
    # elif p == r"{COMMAND} : Perform an implementation-dependent sequence of calls to the {DSBN} and {DSBN} internal methods of {VAR}, to the DeletePropertyOrThrow and HasOwnProperty abstract operation with {VAR} as the first argument, and to SortCompare \(described below\), such that:{I_BULLETS}":
    # elif p == r"{COMMAND} : Repeat, while {VAR} is less than the total number of elements of {VAR}. The number of elements must be redetermined each time this method is evaluated\.{IND_COMMANDS}":
    # elif p == r"{COMMAND} : Return {LITERAL},? if {CONDITION}\.":
    # elif p == r"{COMMAND} : Return {LITERAL},? if {CONDITION}\. Otherwise, return {LITERAL}\.":
    # elif p == r"{COMMAND} : Return {VAR} as the Completion Record of this abstract operation\.":
    # elif p == r"{COMMAND} : When the {NONTERMINAL} {VAR} is evaluated, perform the following steps in place of the {NONTERMINAL} Evaluation algorithm provided in {EMU_XREF}:{IND_COMMANDS}":
    # elif p == r"{COMMAND} : While {CONDITION} repeat,{IND_COMMANDS}":
    # elif p == r"{COMMAND} : While {CONDITION},{IND_COMMANDS}":
    # elif p == r"{COMMAND} : {CONDITION_AS_COMMAND}":
    # elif p == r"{SMALL_COMMAND} : append to {VAR} the elements of {NAMED_OPERATION_INVOCATION}":
    # elif p == r"{SMALL_COMMAND} : let {VAR}, {VAR}, and {VAR} be integers such that {CONDITION}. If there are multiple possibilities for {VAR}, choose the value of {VAR} for which {PRODUCT} is closest in value to {VAR}. If there are two such possible values of {VAR}, choose the one that is even. Note that {VAR} is the number of digits in the decimal representation of {VAR} and that {VAR} is not divisible by 10":
    # elif p == r"{SMALL_COMMAND} : pass its value as the {VAR} optional argument of FunctionCreate":
    # elif p == r"{SMALL_COMMAND} : replace {VAR} in {VAR} with that equivalent code point\(s\)":
    # elif p == r"{SMALL_COMMAND} : throw a {ERROR_TYPE} or a {ERROR_TYPE} exception, depending on the type of the error":
    # elif p == r"{SMALL_COMMAND} : {CONDITION_AS_SMALL_COMMAND}":

    else:
        stderr()
        stderr("tc_nonvalue:")
        stderr('    elif p == %s:' % escape(p))
        sys.exit(0)

    assert result is None or isinstance(result, Env)

    if trace_this_op:
        print()
        print("Leaving nv:", trace_line)
        mytrace(result)

    return result

# ------------------------------------------------------------------------------


def tc_cond(cond, env0, asserting=False):
    # returns a tuple of two envs, one for true and one for false

    p = str(cond.prod)

    if trace_this_op:
        print()
        print("Entering c:", p)
        print("           ", cond.source_text())
        mytrace(env0)

    result = tc_cond_(cond, env0, asserting)

    if trace_this_op:
        print()
        print("Leaving c:", p)
        print("          ", cond.source_text())
        mytrace(result[0])

    return result

def tc_cond_(cond, env0, asserting):
    p = str(cond.prod)
    children = cond.children

    #----------------
    # simple unit production

    if p in [
        r'{CONDITION} : {CONDITION_1}',
        r'{CONDITION_1} : {TYPE_TEST}',
        r'{CONDITION_1} : {NUM_COMPARISON}',
    ]:
        [child] = children
        return tc_cond(child, env0, asserting)

    # -------------
    # combining conditions

    elif p in [
        r"{CONDITION} : Either {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : either {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or if {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1} or {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, or if {CONDITION_1}",
    ]:
        t_envs = []
        f_envs = []
        for cond in children:
            (t_env, f_env) = tc_cond(cond, env0, False)
            t_envs.append(t_env)
            f_envs.append(f_env)
        return ( envs_or(t_envs), envs_and(f_envs) )

    elif p in [
        r"{CONDITION} : {CONDITION_1} and if {CONDITION_1}",
        r'{CONDITION} : {CONDITION_1} and {CONDITION_1}',
        r"{CONDITION} : {CONDITION_1} and {CONDITION_1} and {CONDITION_1}",
        r"{CONDITION} : {CONDITION_1}, and {CONDITION_1}",
        r'{CONDITION} : {CONDITION_1}, {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}',
    ]:
        t_env = env0
        f_envs = []
        for cond in children:
            # each cond is type-checked under the assumption that
            # all preceding conditions succeeded.
            (t_env, f_env) = tc_cond(cond, t_env, asserting)
            f_envs.append(f_env)

        return ( t_env, envs_or(f_envs) )

    elif p == r"{CONDITION} : {CONDITION_1} or {CONDITION_1} and {CONDITION_1}":
        [conda, condb, condc] = children
        (a_t_env, a_f_env) = tc_cond(conda, env0, asserting)
        (b_t_env, b_f_env) = tc_cond(condb, a_f_env, asserting)
        (c_t_env, c_f_env) = tc_cond(condc, a_f_env, asserting)
        return (env_or(a_t_env, env_and(b_t_env, c_t_env)), env_or(b_f_env, c_f_env))

    # elif p == r"{CONDITION} : {CONDITION_1}, when {CONDITION_1}":

    # ---------------
    # Type-conditions

    elif p in [
        r'{TYPE_TEST} : Type\({TYPE_ARG}\) is {TYPE_NAME}',
        r'{TYPE_TEST} : Type\({TYPE_ARG}\) is not {TYPE_NAME}',
    ]:
        [type_arg, type_name] = children
        t = type_for_TYPE_NAME(type_name)
        copula = 'is a' if ' is {' in p else 'isnt a'
        return env0.with_type_test(type_arg, copula, t, asserting)

    elif p in [
        r"{TYPE_TEST} : Type\({TYPE_ARG}\) is either {TYPE_NAME} or {TYPE_NAME}",
        r"{TYPE_TEST} : Type\({TYPE_ARG}\) is either {TYPE_NAME}, {TYPE_NAME}, or {TYPE_NAME}",
        r"{TYPE_TEST} : Type\({TYPE_ARG}\) is neither {TYPE_NAME} n?or {TYPE_NAME}",
        r"{TYPE_TEST} : Type\({TYPE_ARG}\) is {TYPE_NAME}, {TYPE_NAME}, {TYPE_NAME}, or {TYPE_NAME}",
        r'{TYPE_TEST} : Type\({TYPE_ARG}\) is {TYPE_NAME} or {TYPE_NAME}',
    ]:
        [type_arg, *type_name_] = children
        t = union_of_types([
            type_for_TYPE_NAME(tn)
            for tn in type_name_
        ])
        copula = 'isnt a' if 'neither' in p else 'is a'
        return env0.with_type_test(type_arg, copula, t, asserting)


    elif p == r"{TYPE_TEST} : Type\({TYPE_ARG}\) is an ECMAScript language type":
        [type_arg] = children
        return env0.with_type_test(type_arg, 'is a', T_Tangible_, asserting)

    elif p in [
        r'{TYPE_TEST} : Type\({TYPE_ARG}\) is Object and it has an {DSBN} internal slot',
        r'{TYPE_TEST} : Type\({TYPE_ARG}\) is Object and it has {DSBN}, {DSBN}, and {DSBN} internal slots',
    ]:
        [type_arg, *dsbn_] = children
        return env0.with_type_test(type_arg, 'is a', T_Object, asserting)
        # XXX ignore the part about the internal slot(s)?

    elif p == r"{TYPE_TEST} : Type\({TYPE_ARG}\) is Object and is either a built-in function object or has an {DSBN} internal slot":
        [type_arg, dsbn] = children
        assert dsbn.source_text() == '[[ECMAScriptCode]]'
        return env0.with_type_test(type_arg, 'is a', T_function_object_, asserting)

    elif p == r"{CONDITION_1} : {VAR} is an Object that has {DSBN}, {DSBN}, {DSBN}, and {DSBN} internal slots":
        [var, *dsbn_] = children
        assert [dsbn.children for dsbn in dsbn_] == [['ViewedArrayBuffer'],['ArrayLength'],['ByteOffset'],['TypedArrayName']]
        return env0.with_type_test(var, 'is a', T_Integer_Indexed_object_, asserting)
        # could be more specific?

    elif p == r"{CONDITION_1} : {VAR} has an? {DSBN} or {DSBN} internal slot":
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        assert dsbna.source_text() == '[[StringData]]'
        assert dsbnb.source_text() == '[[NumberData]]'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} has {DSBN} and {DSBN} internal slots":
        # XXX could be a type-test
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} does not have either a {DSBN} or an {DSBN} internal slot":
        [var, dsbna, dsbnb] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p in [
        r'{TYPE_TEST} : Type\({TYPE_ARG}\) is the same as Type\({TYPE_ARG}\)',
        r'{TYPE_TEST} : Type\({TYPE_ARG}\) is different from Type\({TYPE_ARG}\)',
    ]:
        # Env can't represent the effect of these.
        # If the incoming static types were different,
        # the 'true' env could at least narrow those to their intersection,
        # but the form only appears twice, and in both cases the static types are the same.
        return (env0, env0)

    # ---

    elif p in [
        r"{CONDITION_1} : {LOCAL_REF} is an? {NONTERMINAL} or an? {NONTERMINAL}",
        r"{CONDITION_1} : {LOCAL_REF} is an? {NONTERMINAL}, an? {NONTERMINAL}, or an? {NONTERMINAL}",
        r"{CONDITION_1} : {LOCAL_REF} is an? {NONTERMINAL}, an? {NONTERMINAL}, an? {NONTERMINAL}, or an? {NONTERMINAL}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {NONTERMINAL} or an? {NONTERMINAL}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {NONTERMINAL}, an? {NONTERMINAL}, or an? {NONTERMINAL}",
        r"{CONDITION_1} : {LOCAL_REF} is either an? {NONTERMINAL}, an? {NONTERMINAL}, an? {NONTERMINAL}, or an? {NONTERMINAL}",
        r"{CONDITION_1} : {LOCAL_REF} is neither an? {NONTERMINAL} n?or an? {NONTERMINAL}",
        r"{CONDITION_1} : {LOCAL_REF} is neither an? {NONTERMINAL} nor an? {NONTERMINAL} nor an? {NONTERMINAL}",
    ]:
        [local_ref, *nont_] = children
        types = []
        for nonterminal in nont_:
            types.append(ptn_type_for(nonterminal))
        target_t = union_of_types(types)
        copula = 'isnt a' if 'neither' in p else 'is a'
        return env0.with_type_test(local_ref, copula, target_t, asserting)
        # XXX at least some of these are using
        # a more complicated meaning for "is a".

    elif p == r'{CONDITION_1} : {VAR} is not a {NONTERMINAL}':
        [var, nonterminal] = children
        target_t = ptn_type_for(nonterminal)
        return env0.with_type_test(var, 'isnt a', target_t, asserting)

    elif p == r'{CONDITION_1} : {EX} and {EX} are distinct {TYPE_NAME} or {TYPE_NAME} values':
        # XXX This means that either they're both one, or else they're both the other,
        # but I can't handle co-ordinated types like that.
        [exa, exb, tnc, tnd] = children
        t = type_for_TYPE_NAME(tnc) | type_for_TYPE_NAME(tnd)
        (a_t_env, a_f_env) = env0.with_type_test(exa, 'is a', t, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(exb, 'is a', t, asserting)
        return (
            env_or(a_t_env, b_t_env),
            env_and(a_f_env, b_f_env)
        )

    # ---

    elif p == r"{CONDITION_1} : {VAR} is an abrupt completion":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Abrupt, asserting)

    elif p in [
        r"{CONDITION_1} : {VAR} is never an abrupt completion",
        r"{CONDITION_1} : {VAR} is not an abrupt completion",
        r"{CONDITION_1} : {VAR} is not an abrupt completion because of validation preceding step 12",
    ]:
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Abrupt, asserting)

    elif p == r'{CONDITION_1} : {VAR} is an accessor property':
        [var] = children
        return env0.with_type_test(var, 'is a', T_accessor_property_, asserting)

    elif p == r"{CONDITION_1} : {VAR} is either a set of algorithm steps or other definition of a function's behaviour provided in this specification":
        [var] = children
        return env0.with_type_test(var, 'is a', T_alg_steps, asserting)

    elif p == r'{CONDITION_1} : {VAR} is an Array exotic object':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Array_object_, asserting)

    elif p == r'{CONDITION_1} : {VAR} is an AsyncGeneratorRequest record':
        [var] = children
        return env0.with_type_test(var, 'is a', T_AsyncGeneratorRequest_Record, asserting)

    elif p == r'{CONDITION_1} : Type\({EXPR}\) is Boolean, String, Symbol, or Number':
        [expr] = children
        return env0.with_type_test(expr, 'is a', T_Boolean | T_String | T_Symbol | T_Number, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a Bound Function exotic object':
        [var] = children
        return env0.with_type_test(var, 'is a', T_bound_function_exotic_object_, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a UTF-16 code unit':
        [var] = children
        return env0.with_type_test(var, 'is a', T_code_unit_, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a constructor function":
        [var] = children
        return env0.with_type_test(var, 'is a', T_constructor_object_, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a Completion Record":
        # In a sense, this is a vacuous condition,
        # because any? value can be coerced into a Completion Record.
        [var] = children
        return env0.with_type_test(var, 'is a', T_Tangible_ | T_empty_ | T_Abrupt, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a Data Block':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Data_Block, asserting)

    elif p in [
        r"{CONDITION_1} : {VAR} is an Environment Record",
        r"{CONDITION_1} : {VAR} must be an Environment Record",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Environment_Record, asserting)

    elif p == r'{CONDITION_1} : {VAR} is the execution context of a generator':
        [var] = children
        return env0.with_type_test(var, 'is a', T_execution_context, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a callable object':
        [var] = children
        return env0.with_type_test(var, 'is a', T_function_object_, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a data property':
        [var] = children
        return env0.with_type_test(var, 'is a', T_data_property_, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a declarative Environment Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_declarative_Environment_Record, asserting)

    elif p in [
        r'{CONDITION_1} : {VAR} is an ECMAScript function',
        r'{CONDITION_1} : {VAR} is an ECMAScript function object',
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_function_object_, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a function Environment Record':
        [var] = children
        return env0.with_type_test(var, 'is a', T_function_Environment_Record, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a global Environment Record':
        [var] = children
        return env0.with_type_test(var, 'is a', T_global_Environment_Record, asserting)

    elif p == r'{CONDITION_1} : {VAR} is an integer value &ge; 0':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Integer_, asserting)

    elif p == r'{CONDITION_1} : {VAR}, {VAR}, and {VAR} are integer values &ge; 0':
        [vara, varb, varc] = children
        (a_t_env, a_f_env) = env0.with_type_test(vara, 'is a', T_Integer_, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(varb, 'is a', T_Integer_, asserting)
        (c_t_env, c_f_env) = env0.with_type_test(varc, 'is a', T_Integer_, asserting)
        return (
            envs_and([a_t_env, b_t_env, c_t_env]),
            envs_or([a_f_env, b_f_env, c_f_env])
        )

    elif p == r"{CONDITION_1} : {VAR} is a Lexical Environment":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Lexical_Environment, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a List":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', T_List, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a List whose elements are all ECMAScript language values":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_Tangible_), asserting)

    elif p == r"{CONDITION_1} : {VAR} is a List of code points":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_code_point_), asserting)

    elif p == r"{CONDITION_1} : {VAR} is a List of code units":
        [list_var] = children
        return env0.with_type_test(list_var, 'is a', ListType(T_code_unit_), asserting)

    elif p == r'{CONDITION_1} : {VAR} is a List of String values':
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_String), asserting)

    elif p == r"{CONDITION_1} : {VAR} is a List of property keys":
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_String | T_Symbol), asserting)

    elif p == r'{CONDITION_1} : {VAR} is a List of errors':
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_SyntaxError | T_ReferenceError), asserting)

    elif p == r'{CONDITION_1} : {VAR} is a List that has the same number of elements as the number of parameters required by {VAR}':
        [list_var, proc_var] = children
        env0.assert_expr_is_of_type(proc_var, T_proc_)
        return env0.with_type_test(list_var, 'is a', T_List, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a List of WriteSharedMemory or ReadModifyWriteSharedMemory events with length equal to {EX}':
        [var, ex] = children
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return env0.with_type_test(var, 'is a', ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event), asserting)

    elif p == r"{CONDITION_1} : {VAR} is a List of a single Number":
        [var] = children
        return env0.with_type_test(var, 'is a', ListType(T_Number), asserting)

    elif p == r"{CONDITION_1} : {VAR} is a List containing only String and Symbol values":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_String | T_Symbol))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a possibly empty List of Strings":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_String))
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {VAR} is an empty List",
        r"{CONDITION_1} : {VAR} is now an empty List",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a List of Unicode code points that is identical to a List of Unicode code points that is a Unicode property name or property alias listed in the &ldquo;Property name and aliases&rdquo; column of {EMU_XREF} or {EMU_XREF}":
        [v, emu_xref1, emu_xref2] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is not an empty List":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List | T_WaiterList)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {VAR} is a Module Record',
        r"{CONDITION_1} : {VAR} is an instance of a concrete subclass of Module Record",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Module_Record, asserting)

    elif p in [
        r"{CONDITION_1} : {VAR} is present as a parameter",
    ]:
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_not_passed, asserting)

    elif p in [
        r'{CONDITION_1} : {EX} is present',
        r'{CONDITION_1} : {EX} is not present',
    ]:
        [ex] = children
        if ex.is_a('{DOTTING}'):
            t = T_not_in_record
        elif ex.is_a('{PROD_REF}'):
            t = T_not_in_node
        elif ex.is_a('{VAR}'):
            # todo: get rid of this usage. (roll eyes at PR #953)
            t = T_not_passed # assuming it's a parameter
        else:
            assert 0, ex.source_text()
        copula = 'is a' if 'not present' in p else 'isnt a'
        return env0.with_type_test(ex, copula, t, asserting)

    elif p == r"{CONDITION_1} : {EX} is absent":
        # todo: eliminate?
        [ex] = children
        assert ex.is_a('{DOTTING}')
        return env0.with_type_test(ex, 'is a', T_not_in_record, asserting)

    elif p == r"{CONDITION_1} : {VAR} is an integer Number &ge; 0":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Integer_, asserting)

    elif p in [
        r'{CONDITION_1} : {EXPR} is an object',
        r"{CONDITION_1} : {EX} is an Object",
    ]:
        [expr] = children
        return env0.with_type_test(expr, 'is a', T_Object, asserting)

    elif p == r"{CONDITION_1} : {VAR} is not an object Environment Record":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_object_Environment_Record, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a Parse Node":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Parse_Node, asserting)

    elif p == r'{CONDITION_1} : {VAR} is the name of a Job':
        [var] = children
        return env0.with_type_test(var, 'is a', T_proc_, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a PromiseCapability Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_PromiseCapability_Record, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a PromiseReaction Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_PromiseReaction_Record, asserting)

    elif p in [
        r'{CONDITION_1} : {VAR} is a Property Descriptor',
        r"{CONDITION_1} : {VAR} must be an accessor Property Descriptor",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Property_Descriptor, asserting)

    elif p in [
        r'{CONDITION_1} : {VAR} is a Proxy exotic object',
        r"{CONDITION_1} : {VAR} is a Proxy object",
    ]:
        [var] = children
        return env0.with_type_test(var, 'is a', T_Proxy_exotic_object_, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_ReadModifyWriteSharedMemory_event, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a ReadSharedMemory or ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a Realm Record':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Realm_Record, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a ResolvedBinding Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_ResolvedBinding_Record, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a Shared Data Block':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Shared_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {VAR} is not a Shared Data Block':
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Shared_Data_Block, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a ReadSharedMemory, WriteSharedMemory, or ReadModifyWriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_Shared_Data_Block_event, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a Source Text Module Record":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Source_Text_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {VAR} is not a Source Text Module Record":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Source_Text_Module_Record, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a State":
        [var] = children
        return env0.with_type_test(var, 'is a', T_State, asserting)

    elif p == r'{CONDITION_1} : {EX} is a String value':
        [ex] = children
        if (
            ex.prod.rhs_s == '{LOCAL_REF}'
            and
            ex.children[0].prod.rhs_s == '{SETTABLE}'
            and
            ex.children[0].children[0].prod.rhs_s == '{VAR}'
        ):
            [var] = ex.children[0].children[0].children
            return env0.with_type_test(var, 'is a', T_String, asserting)
        elif (
            ex.prod.rhs_s == '{LOCAL_REF}'
            and
            ex.children[0].prod.rhs_s == '{SETTABLE}'
            and
            ex.children[0].children[0].prod.rhs_s == '{DOTTING}'
        ):
            [dotting] = ex.children[0].children[0].children
            # XXX
            return (env0, env0)
        else:
            assert 0

    elif p == r"{CONDITION_1} : both {VAR} and {VAR} are Strings":
        [a_var, b_var] = children
        (at_env, af_env) = env0.with_type_test(a_var, 'is a', T_String, asserting)
        (bt_env, bf_env) = env0.with_type_test(b_var, 'is a', T_String, asserting)
        return (
            env_and(at_env, bt_env),
            env_or(af_env, bf_env)
        )

    elif p == r"{TYPE_TEST} : Both Type\({TYPE_ARG}\) and Type\({TYPE_ARG}\) is {TYPE_NAME}":
        [type_arga, type_argb, type_name] = children
        t = type_for_TYPE_NAME(type_name)
        (a_t_env, a_f_env) = env0.with_type_test(type_arga, 'is a', t, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(type_argb, 'is a', t, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    elif p == r"{CONDITION_1} : {VAR} is a String exotic object":
        [var] = children
        return env0.with_type_test(var, 'is a', T_String_exotic_object_, asserting)

    elif p == r"{CONDITION_1} : {VAR} is an ECMAScript language value":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Tangible_, asserting)

    elif p == r"{CONDITION_1} : {VAR} will never be \*undefined\* or an accessor descriptor because Array objects are created with a length data property that cannot be deleted or reconfigured":
        [var] = children
        return env0.with_type_test(var, 'isnt a', T_Undefined, asserting)

    elif p in [
        r"{CONDITION_1} : {VAR} is a normal completion with a value of {LITERAL}\. The possible sources of completion values are AsyncFunctionAwait or, if the async function doesn't await anything, the step 3\.g above",
        r"{CONDITION_1} : {VAR} is a normal completion with a value of {LITERAL}\. The possible sources of completion values are Await or, if the async function doesn't await anything, the step 3\.g above",
    ]:
        [var, literal] = children
        env0.assert_expr_is_of_type(literal, T_Undefined)
        return env0.with_type_test(var, 'is a', T_Undefined, asserting)

    elif p == r'{CONDITION_1} : {VAR} is an ECMAScript source text \(see clause {EMU_XREF}\)':
        [var, emu_xref] = children
        return env0.with_type_test(var, 'is a', T_Unicode_code_points_, asserting)

    elif p == r'{CONDITION_1} : {VAR} is a WriteSharedMemory event':
        [var] = children
        return env0.with_type_test(var, 'is a', T_WriteSharedMemory_event, asserting)

    elif p ==  r"{CONDITION_1} : {VAR} is a normal completion":
        [var] = children
        return env0.with_type_test(var, 'is a', T_Normal, asserting)

    elif p == r"{CONDITION_1} : {VAR} is either a String, Number, Boolean, Null, or an Object that is defined by either an {NONTERMINAL} or an {NONTERMINAL}":
        [var, nonta, nontb] = children
        return env0.with_type_test(var, 'is a', T_String | T_Number | T_Boolean | T_Null | T_Object, asserting)

    # ----------------------
    # quasi-type-conditions

    elif p in [
        r"{CONDITION_1} : {VAR} is hint String",
        r"{CONDITION_1} : {VAR} is hint Number",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_LangTypeName_)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {LOCAL_REF} is {EMU_GRAMMAR}[ ]?',
        r"{CONDITION_1} : {VAR} is an instance of the production {EMU_GRAMMAR}",
    ]:
        [local_ref, emu_grammar] = children
        [production] = emu_grammar.children
        lhs = re.sub(r' :.*', '', production)
        prodn_type = ptn_type_for(lhs)
        #
        (ref_type, env1) = tc_expr(local_ref, env0); assert env1 is env0
        assert prodn_type.is_a_subtype_of_or_equal_to(ref_type)
        # but whether or not it's an instance of that particular production
        # doesn't narrow its type.
        return (env1.with_expr_type_narrowed(local_ref, prodn_type), env1)

    elif p in [
        r"{CONDITION_1} : {VAR} is an Object that has a {DSBN} internal slot",
        r'{CONDITION_1} : {VAR} is an extensible object that does not have a `("length"|prototype|name)` own property',
    ]:
        [var, _] = children
        return (
            env0.with_expr_type_narrowed(var, T_Object),
            env0
        )

    elif p == r"{CONDITION_1} : {VAR} has a {DSBN} internal slot. If it does not, the definition in {EMU_XREF} applies":
        [var, dsbn, emu_xref] = children
        assert dsbn.source_text() == '[[TypedArrayName]]'
        return (
            env0.with_expr_type_narrowed(var, T_Integer_Indexed_object_),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {VAR} is an extensible ordinary object with no own properties",
        r"{CONDITION_1} : {VAR} is an initialized RegExp instance",
        r'{CONDITION_1} : {VAR} is an Object that implements the <i>IteratorResult</i> interface',
    ]:
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_Object),
            env0
        )

    elif p in [
        r"{CONDITION_1} : {VAR} is an integer index",
        r"{CONDITION_1} : {VAR} is an array index",
    ]:
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_String),
            env0
        )

    elif p == r"{CONDITION_1} : {VAR} is not an integer index":
        [var] = children
        return (
            env0,
            env0.with_expr_type_narrowed(var, T_String)
        )

    elif p in [
        r"{CONDITION_1} : {VAR} is a {EMU_XREF}",
        r"{CONDITION_1} : {VAR} is not a {EMU_XREF}",
    ]:
        [var, emu_xref] = children

        # copula = 'isnt a' if 'not' in p else 'is a'

        assert emu_xref.source_text() in [
            '<emu-xref href="#leading-surrogate"></emu-xref>',
            '<emu-xref href="#trailing-surrogate"></emu-xref>',
        ]

        if 'is a' in p:
            return (
                env0.with_expr_type_narrowed(var, T_code_unit_),
                env0
            )
        else:
            return (
                env0,
                env0.with_expr_type_narrowed(var, T_code_unit_)
            )

    elif p in [
        r"{CONDITION_1} : The value of {SETTABLE} is {LITERAL}",
        r"{CONDITION_1} : {EXPR} is {LITERAL}",
        r"{CONDITION_1} : {EX} has the value {LITERAL}",
        r"{CONDITION_1} : {EX} is not {LITERAL}",
        r"{CONDITION_1} : {EX} is present and has value {LITERAL}",
        r"{CONDITION_1} : {EX} is {LITERAL}",
        r"{CONDITION_1} : {VAR} is also {LITERAL}",
        r"{CONDITION_1} : {VAR} is the value {LITERAL}",
        r"{CONDITION_1} : {VAR} is {LITERAL} because formal parameters mapped by argument objects are always writable",
    ]:
        [ex, literal] = children

        # kludgey?
        r = is_simple_call(ex)
        if r:
            (callee_op_name, var) = r
            #
            if callee_op_name == 'IsSharedArrayBuffer':
                t = T_SharedArrayBuffer_object_
            elif callee_op_name == 'IsPromise':
                t = T_Promise_object_
            elif callee_op_name == 'IsCallable':
                t = T_function_object_
            elif callee_op_name == 'IsConstructor':
                t = T_constructor_object_
            elif callee_op_name == 'IsPropertyKey':
                t = T_String | T_Symbol
            elif callee_op_name == 'IsInteger':
                t = T_Integer_
            else:
                t = None
            #
            if t:
                assert 'not' not in p
                if literal.source_text() == '*true*':
                    copula = 'is a'
                elif literal.source_text() == '*false*':
                    copula = 'isnt a'
                else:
                    assert 0
                #
                return env0.with_type_test(var, copula, t, asserting)

        copula = 'isnt a' if 'is not' in p else 'is a'

        # special handling for Completion Records:
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            [dsbn_name] = dsbn.children
            if dsbn_name != 'Type': break
            t = type_corresponding_to_comptype_literal(literal)
            return env0.with_type_test(lhs, copula, t, asserting)

        # ------------

        (lit_type, lit_env) = tc_expr(literal, env0)
        assert lit_env is env0

        if lit_type in [T_Undefined, T_Null, T_empty_, T_not_in_node, T_match_failure_, T_Infinity_]:
            # i.e., the literal is *undefined* or *null* or ~empty~ or ~[empty]~ or ~failure~ or &infin;
            # Because the type has only one value,
            # a value-comparison is equivalent to a type-comparison.
            return env0.with_type_test(ex, copula, lit_type, asserting)
        elif literal.source_text() == '`"ambiguous"`':
            # The return-type of ResolveExport includes String,
            # but only for the single value "ambiguous".
            # So a test against that value is a type-comparison.
            return env0.with_type_test(ex, copula, lit_type, asserting)
        else:
            # The type has more than one value.
            # So, while the is-case is type-constraining,
            # the isn't-case isn't.
            is_env = env0.with_expr_type_narrowed(ex, lit_type)
            isnt_env = env0

            if copula == 'is a':
                return (is_env, isnt_env)
            else:
                return (isnt_env, is_env)

    elif p in [
        r'{CONDITION_1} : {EX} is {LITERAL} or {LITERAL}',
        r'{CONDITION_1} : {EX} is either {LITERAL} or {LITERAL}',
        # ---
        r"{CONDITION_1} : {EX} is not {LITERAL} or {LITERAL}",
        r"{CONDITION_1} : {EX} is neither {LITERAL} nor {LITERAL}",
        r"{CONDITION_1} : {EX} is present, and is neither {LITERAL} nor {LITERAL}",
        r"{CONDITION_1} : In this case, {VAR} will never be {LITERAL} or {LITERAL}",
    ]:
        [ex, lita, litb] = children

        # special handling for Completion Records' [[Type]] field
        while True: # ONCE
            dotting = ex.is_a('{DOTTING}')
            if dotting is None: break
            (lhs, dsbn) = dotting.children
            [dsbn_name] = dsbn.children
            if dsbn_name != 'Type': break
            ta = type_corresponding_to_comptype_literal(lita)
            tb = type_corresponding_to_comptype_literal(litb)
            assert 'never' not in p
            assert 'neither' not in p
            return env0.with_type_test(lhs, 'is a', ta | tb, asserting)

        (lita_type, lita_env) = tc_expr(lita, env0); assert lita_env is env0
        (litb_type, litb_env) = tc_expr(litb, env0); assert litb_env is env0

        copula = 'isnt a' if ('never' in p or 'neither' in p or 'not' in p) else 'is a'

        # It's only a type-test if the literals are from very small types.
        if (
            lita_type == T_Null and litb_type == T_Undefined
            or
            lita_type == T_Undefined and litb_type == T_Null
        ):
            return env0.with_type_test(ex, copula, T_Null | T_Undefined, asserting)

        elif lita_type == T_Null and litb_type == T_String and litb.source_text() == '`"ambiguous"`':
            return env0.with_type_test(ex, copula, T_Null | T_String, asserting)

        elif lita_type == litb_type:
            (t, env1) = tc_expr(ex, env0)
            if t == lita_type:
                pass
            else:
                env1 = env1.with_expr_type_replaced(ex, lita_type)
            return (env1, env1)

        elif lita_type == T_Boolean and litb_type == T_Undefined:
            # Evaluation of RelationalExpression: If _r_ is *true* or *undefined*, ...
            env0.assert_expr_is_of_type(ex, T_Boolean | T_Undefined)
            return (env0, env0)

        else:
            assert 0

    elif p == r"{CONDITION_1} : {EX} is either not present or {LITERAL}":
        [ex, lit] = children
        (t_lit, env1) = tc_expr(lit, env0); assert env1 is env0
        assert t_lit == T_Undefined
        return env0.with_type_test(ex, 'is a', T_not_passed | t_lit, asserting)

    elif p == r"{CONDITION_1} : {VAR} is {LITERAL}, {LITERAL} or not supplied":
        [ex, lita, litb] = children
        (t_lita, env1) = tc_expr(lita, env0); assert env1 is env0
        (t_litb, env1) = tc_expr(litb, env0); assert env1 is env0
        assert t_lita == T_Null
        assert t_litb == T_Undefined
        return env0.with_type_test(ex, 'is a', t_lita | t_litb | T_not_passed, asserting)

    elif p == r"{CONDITION_1} : {EX} is not present, or is either {LITERAL} or {LITERAL}":
        [ex, lita, litb] = children
        (t_lita, env1) = tc_expr(lita, env0); assert env1 is env0
        (t_litb, env1) = tc_expr(litb, env0); assert env1 is env0
        assert t_lita == T_Undefined
        assert t_litb == T_Null
        return env0.with_type_test(ex, 'is a', T_not_passed | t_lita | t_litb, asserting)

    elif p == r'{CONDITION_1} : {EX} and {EX} are both {LITERAL}':
        [exa, exb, lit] = children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        if lit_type == T_Undefined:
            (a_t_env, a_f_env) = env0.with_type_test(exa, 'is a', T_Undefined, asserting)
            (b_t_env, b_f_env) = env0.with_type_test(exb, 'is a', T_Undefined, asserting)
            return (
                env_and(a_t_env, b_t_env),
                env_or(a_f_env, b_f_env)
            )
        else:
            env0.assert_expr_is_of_type(exa, lit_type)
            env0.assert_expr_is_of_type(exb, lit_type)
            return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} and {VAR} are both WriteSharedMemory or ReadModifyWriteSharedMemory events":
        # XXX spec is ambiguous: "each is A or B" vs "either both A or both B"
        [ea, eb] = children
        (a_t_env, a_f_env) = env0.with_type_test(ea, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        (b_t_env, b_f_env) = env0.with_type_test(eb, 'is a', T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event, asserting)
        return (
            env_and(a_t_env, b_t_env),
            env_or(a_f_env, b_f_env)
        )

    elif p in [
        r"{CONDITION_1} : {EX} is {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {EX} is either {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {VAR} is {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {VAR} is either {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {VAR} is one of {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}",
        r"{CONDITION_1} : {VAR} is either {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {VAR} is {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {VAR} is {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
        r"{CONDITION_1} : {VAR} is not {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}",
    ]:
        [var, *lit_] = children
        assert len(lit_) in [3,4,5,6]
        lit_types = []
        for lit in lit_:
            (ti, envi) = tc_expr(lit, env0)
            # assert envi is env0
            lit_types.append(ti)
        lt = union_of_types(lit_types)
        env1 = env0.ensure_expr_is_of_type(var, lt)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {VAR} is either {LITERAL} or an? {NONTERMINAL}":
        # Once, in EvaluateNew
        [var, literal, nont] = children
        assert literal.source_text() == '~empty~'
        t = T_empty_ | ptn_type_for(nont)
        return env0.with_type_test(var, 'is a', t, asserting)

    elif p == r"{CONDITION_1} : {VAR} is {LITERAL} or a Module Record":
        [var, lit] = children
        (lit_type, lit_env) = tc_expr(lit, env0); assert lit_env is env0
        assert lit.source_text() == '`"ambiguous"`'
        return env0.with_type_test(var, 'is a', T_String | T_Module_Record, asserting)

    elif p == r'{CONDITION_1} : {VAR} is an integer such that {CONDITION_1}':
        [var, cond] = children
        (t_env, f_env) = tc_cond(cond, env0)
        return (
            t_env.with_expr_type_narrowed(var, T_Integer_),
            t_env
        )

    elif p == r"{CONDITION_1} : {VAR} is a nonnegative integer":
        [var] = children
        return (
            env0.with_expr_type_narrowed(var, T_Integer_),
            env0
        )

    elif p == r'{CONDITION_1} : {VAR} has an? {DSBN} internal method':
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        [dsbn_name] = dsbn.children
        if dsbn_name == 'Call':
            # one of the few where the presence/absence of an internal method is a type-test?
            return env1.with_type_test(var, 'is a', T_function_object_, asserting)
        elif dsbn_name == 'Construct':
            return env1.with_type_test(var, 'is a', T_constructor_object_, asserting)
        else:
            assert dsbn_name == 'Construct'
            return (env1, env1)

    elif p == r"{CONDITION_1} : {SETTABLE} has an? {DSBN} field":
        [settable, dsbn] = children
        [dsbn_name] = dsbn.children
        t = env0.assert_expr_is_of_type(settable, T_Record)
        if t.name == 'Environment Record' and dsbn_name == 'NewTarget':
            add_pass_error(
                cond,
                "STA can't confirm that `%s` could have a `%s` field"
                % ( settable.source_text(), dsbn_name )
            )
            # We could confirm if we looked at the subtypes and what fields they have.
            return (
                env0.with_expr_type_narrowed(settable, T_function_Environment_Record),
                env0
            )
        else:
            assert dsbn_name in fields_for_record_type_named_[t.name], (t.name, dsbn_name)
            return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} does not have an? {DSBN} (field|internal slot)':
        [var, dsbn, kind] = children
        [var_name] = var.children
        if kind == 'field':
            env1 = env0.ensure_expr_is_of_type(var, T_Record)
            # XXX We should check whether its type says it *could* have such a field.
        elif kind == 'internal slot':
            env1 = env0.ensure_expr_is_of_type(var, T_Object)
            # Whether or not it has that particular slot, it's still an Object.
        else:
            assert 0
        # XXX The particular DSBN could have a (sub-)type-constraining effect
        return (env1, env1)

    elif p in [
        r'{CONDITION_1} : {VAR} also has a {DSBN} internal slot',
        r'{CONDITION_1} : {VAR} has an? {DSBN} internal slot',
    ]:
        [var, dsbn] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        # Whether or not it has that particular slot, it's still an Object.
        return (env1, env1)

    elif p == r'{CONDITION_1} : {VAR} is an IEEE 754-2008 binary32 NaN value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {VAR} is an IEEE 754-2008 binary64 NaN value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary64_)
        return (env1, env1)

    # --------
    # These 4 are affected by the strangeness described in Issue #831

    elif p == r"{CONDITION_1} : {VAR} is the {NONTERMINAL} {TERMINAL}":
        [var, nont, term] = children
        assert nont.source_text() == '|ReservedWord|'
        assert term.source_text() == "`super`"
        env0.ensure_expr_is_of_type(var, T_grammar_symbol_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is an? {NONTERMINAL}":
        [var, nont] = children
        if var.source_text() == '_symbol_' and nont.source_text() in ['|ReservedWord|', '|Identifier|']:
            t = T_grammar_symbol_
        else:
            t = T_Parse_Node
        env1 = env0.ensure_expr_is_of_type(var, t)
        return (env1, env1)
        #return env0.with_type_test(var, 'is a', ptn_type_for(nont), asserting)

    elif p == r"{CONDITION_1} : {VAR} is {NONTERMINAL}":
        [var, nont] = children
        env1 = env0.ensure_expr_is_of_type(var, T_grammar_symbol_)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {EX} is the same value as {NAMED_OPERATION_INVOCATION}":
        [ex, noi] = children
        assert ex.source_text() == 'StringValue of _symbol_'
        assert noi.source_text() == 'the StringValue of |IdentifierName|'
        # For now, just return the env unchanged.
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {VAR} is not one of {NONTERMINAL}, {NONTERMINAL}, {NONTERMINAL}, `super` or `this`",
        r"{CONDITION_1} : {VAR} is not one of {NONTERMINAL}, {NONTERMINAL}, {NONTERMINAL}, `super`, or `this`",
    ]:
        [local_ref, *_] = children
        env0.ensure_expr_is_of_type(local_ref, T_grammar_symbol_)
        return (env0, env0)

    # ------------------------
    # relating to Environment Record bindings:

    elif p in [
        r"{CONDITION_1} : {VAR} does not already have a binding for {VAR}",
        r"{CONDITION_1} : {VAR} does not have a binding for {VAR}",
        r"{CONDITION_1} : {VAR} has a binding for the name that is the value of {VAR}",
        r"{CONDITION_1} : {VAR} has a binding for {VAR}",
        r"{CONDITION_1} : {VAR} must have an uninitialized binding for {VAR}",
    ]:
        [er_var, n_var] = children
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : the binding for {VAR} in {VAR} cannot be deleted",
        r"{CONDITION_1} : the binding for {VAR} in {VAR} has not yet been initialized",
        r"{CONDITION_1} : the binding for {VAR} in {VAR} is a mutable binding",
        r"{CONDITION_1} : the binding for {VAR} in {VAR} is a strict binding",
        r"{CONDITION_1} : the binding for {VAR} in {VAR} is an uninitialized binding",
    ]:
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the binding for {VAR} is an indirect binding":
        # todo: make ER explicit in spec?
        [n_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the binding exists":
        # elliptical
        [] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : When {SETTABLE} is instantiated it will have a direct binding for {VAR}':
        [settable, var] = children
        env0.assert_expr_is_of_type(settable, T_Lexical_Environment | T_Undefined)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    # --------------------------------------------------
    # relating to strict code:

    elif p in [
        r"{CONDITION_1} : the code matched by {PROD_REF} is strict mode code",
        r"{CONDITION_1} : the function code for {PROD_REF} is strict mode code",
        r"{CONDITION_1} : the source code matching {PROD_REF} is strict mode code",
        r"{CONDITION_1} : the source code matching {VAR} is non-strict code",
        r"{CONDITION_1} : {PROD_REF} is contained in strict mode code",
        r"{CONDITION_1} : {VAR} is strict mode code",
    ]:
        [prod_ref] = children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the code matching the syntactic production that is being evaluated is contained in strict mode code":
        [] = children
        return (env0, env0)

    # -------------------------------------------------
    # introduce metavariable:

    elif p in [
        r'{CONDITION_1} : there does not exist a member {VAR} of set {VAR} such that {CONDITION_1}',
        r'{CONDITION_1} : there exists a member {VAR} of set {VAR} such that {CONDITION_1}',
    ]:
        [member_var, set_var, cond] = children
        env1 = env0.ensure_expr_is_of_type(set_var, T_CharSet)
        env2 = env1.plus_new_entry(member_var, T_character_)
        (t_env, f_env) = tc_cond(cond, env2)
        assert t_env is f_env
        return (env1, env1)

    elif p == r"{CONDITION_1} : there exists an integer {VAR} between 0 \(inclusive\) and {VAR} \(exclusive\) such that {CONDITION_1}":
        [i_var, m_var, cond] = children
        env0.assert_expr_is_of_type(m_var, T_Integer_)
        env_for_cond = env0.plus_new_entry(i_var, T_Integer_)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : there exists any integer {VAR} not smaller than {VAR} such that {CONDITION_1}, and {CONDITION_1}":
        [i_var, min_var, conda, condb] = children
        env0.assert_expr_is_of_type(min_var, T_Integer_)
        env_for_cond = env0.plus_new_entry(i_var, T_Integer_)
        (at_env, af_env) = tc_cond(conda, env_for_cond)
        (bt_env, bf_env) = tc_cond(condb, env_for_cond)
        return (env_and(at_env, bt_env), env_or(af_env, bf_env))

    elif p == r"{CONDITION_1} : for all nonnegative integers {VAR} less than {VAR}, {CONDITION_1}":
        [loop_var, min_var, cond] = children
        env0.assert_expr_is_of_type(min_var, T_Integer_)
        env_for_cond = env0.plus_new_entry(loop_var, T_Integer_)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : there is a WriteSharedMemory or ReadModifyWriteSharedMemory event {VAR} that has {VAR} in its range such that {CONDITION_1}":
        [let_var, i, cond] = children
        env0.assert_expr_is_of_type(i, T_Integer_)
        env_for_cond = env0.plus_new_entry(let_var, T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : there is an event {VAR} such that {CONDITION}":
        [let_var, cond] = children
        env_for_cond = env0.plus_new_entry(let_var, T_Shared_Data_Block_event)
        return tc_cond(cond, env_for_cond)

    elif p == r"{CONDITION_1} : {SETTABLE} is not equal to {SETTABLE} for any integer value {VAR} in the range {LITERAL} through {VAR}, exclusive":
        [seta, setb, let_var, lo, hi] = children
        env0.assert_expr_is_of_type(lo, T_Integer_)
        env0.assert_expr_is_of_type(hi, T_Integer_)
        env_for_settables = env0.plus_new_entry(let_var, T_Integer_)
        env_for_settables.assert_expr_is_of_type(seta, T_Integer_)
        env_for_settables.assert_expr_is_of_type(setb, T_Integer_)
        return (env0, env0)

    # --------------------------------------------------
    # whatever

    elif p == r'{CONDITION_1} : {VAR} is the same Number value as {VAR}':
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_Number)
        env1 = env0.ensure_expr_is_of_type(var2, T_Number)
        return (env1, env1)

    elif p in [
        r"{NUM_COMPARISON} : {NUM_COMPARAND} (equals) {NUM_COMPARAND}",
        r"{NUM_COMPARISON} : {NUM_COMPARAND} (is at least) {NUM_LITERAL}",
        r"{NUM_COMPARISON} : {NUM_COMPARAND} (is greater than or equal to) {NUM_COMPARAND}",
        r"{NUM_COMPARISON} : {NUM_COMPARAND} (is greater than) {NUM_COMPARAND}",
        r"{NUM_COMPARISON} : {NUM_COMPARAND} (is less than or equal to) {NUM_COMPARAND}",
        r"{NUM_COMPARISON} : {NUM_COMPARAND} (is not greater than) {VAR}",
        r"{NUM_COMPARISON} : {NUM_COMPARAND} (is not less than) {VAR}",
        r'{NUM_COMPARISON} : {NUM_COMPARAND} (&le;|&lt;) {NUM_COMPARAND} (&le;|&lt;) {NUM_COMPARAND}',
        r'{NUM_COMPARISON} : {NUM_COMPARAND} (&lt;|&le;|&ge;|&gt;|=|&ne;|\u2265) {NUM_COMPARAND}',
        r'{NUM_COMPARISON} : {VAR} (is less than) {FACTOR}',
    ]:
        comparands = children[0::2]
        env1 = env0
        for comparand in comparands:
            env1 = env1.ensure_expr_is_of_type(comparand, T_numeric_)
        # if trace_this_op: pdb.set_trace()
        return (env1, env1)

    elif p in [
        r'{NUM_COMPARISON} : {NUM_COMPARAND} is not less than {NUM_LITERAL} and not greater than {NUM_LITERAL}',
        r'{NUM_COMPARISON} : {NUM_COMPARAND} is less than {NUM_LITERAL} or greater than {NUM_LITERAL}',
    ]:
        [a,b,c] = children
        env0.assert_expr_is_of_type(a, T_Integer_)
        env0.assert_expr_is_of_type(b, T_Integer_)
        env0.assert_expr_is_of_type(c, T_Integer_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : the file CaseFolding.txt of the Unicode Character Database provides a simple or common case folding mapping for {VAR}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {VAR} does not consist of a single code unit':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {VAR} does not contain exactly one character':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (env1, env1)

    elif p == r'{CONDITION_1} : the Directive Prologue of {PROD_REF} contains a Use Strict Directive':
        [prod_ref] = children
        # XXX check that prod_ref makes sense
        return (env0, env0)

    elif p == r'{CONDITION_1} : The calling agent is not in the critical section for any WaiterList':
        # nothing to check
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : The execution context stack has at least two elements",
        r"{CONDITION_1} : The execution context stack is not empty",
        r"{CONDITION_1} : The execution context stack is now empty",
        r"{CONDITION_1} : the execution context stack is empty",
    ]:
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : When we return here, {VAR} has already been removed from the execution context stack and {VAR} is the currently running execution context":
        [a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_execution_context)
        env0.assert_expr_is_of_type(b_var, T_execution_context)
        return (env0, env0)

    elif p == r'{CONDITION_1} : no such execution context exists':
        [] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} contains the names {DSBN}, {DSBN}, {DSBN}, and {DSBN}':
        [var, *dsbn_] = children
        assert len(dsbn_) == 4
        # XXX assert that each dsbn_ is a slot name
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(ListType(T_SlotName_))
        return (env1, env1)

    elif p == r'{CONDITION_1} : both {EX} and {EX} are absent':
        [exa, exb] = children
        (ta, enva) = tc_expr(exa, env0); assert enva is env0
        (tb, envb) = tc_expr(exb, env0); assert envb is env0
        # XXX Could assert that T_not_set is a subtype of ta and tb,
        # but the typing of Property Descriptors is odd.
        # XXX Could look at exa.source_text() and exb.source_text()
        # and make a dichotomy re Prop Desc subtypes, but not really worth it.
        # (because the form only appears in IsAccessorDescriptor and IsDataDescriptor,
        # which are tiny)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} has a thisValue component':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a Reference to an Environment Record binding":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (env0, env0)

    elif p == r'{CONDITION_1} : The calling agent is in the critical section for {VAR}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_WaiterList)
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {EX} is an element of {VAR}',
        r"{CONDITION_1} : {EX} is not an element of {VAR}",
    ]:
        [value_ex, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(value_ex, list_var)
        return (env1, env1)

    elif p in [
        r'{CONDITION_1} : {VAR} contains {VAR}',
        r"{CONDITION_1} : {VAR} does not contain {VAR}",
    ]:
        [list_var, value_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(value_var, list_var)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {VAR} is not in {PREFIX_PAREN}":
        [item_var, set_pp] = children
        env0.assert_expr_is_of_type(set_pp, T_Set)
        env0.assert_expr_is_of_type(item_var, T_event_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} has no further use. It will never be activated as the running execution context':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_execution_context)
        return (env1, env1)

    elif p == r'{CONDITION_1} : {VAR} has a numeric value less than (0x0020 \(SPACE\))':
        [var, cu_literal] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (env1, env1)

    elif p in [
        r'{CONDITION_1} : {EX} is equal to {EX}',
        r"{CONDITION_1} : {EX} is different from {EX}",
        r"{CONDITION_1} : {EX} is the same as {EX}",
        r"{CONDITION_1} : {VAR} is not the same as {VAR}",
        r"{CONDITION_1} : {VAR} is not equal to {VAR}",
        r"{CONDITION_1} : {VAR} and {VAR} are the same",
    ]:
        [exa, exb] = children
        (exa_type, exa_env) = tc_expr(exa, env0); assert exa_env is env0
        (exb_type, exb_env) = tc_expr(exb, env0); assert exb_env is env0
        if exa_type == exb_type:
            # good
            env1 = env0
        elif exa_type == T_TBD:
            env1 = env0.with_expr_type_replaced(exa, exb_type)
        elif exa_type == T_Lexical_Environment | T_Undefined and exb_type == T_Lexical_Environment:
            env1 = env0.with_expr_type_replaced(exa, exb_type)
        elif exa_type == T_Integer_ and exb_type == T_Number:
            # XXX could be more specific
            env1 = env0
        else:
            assert 0
        return (env1, env1)

    elif p == r'{CONDITION_1} : {VAR} and {VAR} are exactly the same sequence of code units \(same length and same code units at corresponding indices\)':
        # occurs once, in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_String); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_String); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {EX} and {EX} are both {LITERAL} or both {LITERAL}':
        # occurs once, in SameValueNonNumber
        [exa, exb, litc, litd] = children
        assert litc.source_text() == '*true*'
        assert litd.source_text() == '*false*'
        enva = env0.ensure_expr_is_of_type(exa, T_Boolean); assert enva is env0
        envb = env0.ensure_expr_is_of_type(exb, T_Boolean); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {VAR} and {VAR} are both the same Symbol value':
        # occurs once, in SameValueNonNumber
        [vara, varb] = children
        enva = env0.ensure_expr_is_of_type(vara, T_Symbol); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, T_Symbol); # assert envb is env0
        return (envb, envb)

    elif p == r'{CONDITION_1} : {VAR} and {VAR} are the same (Number|Object) value':
        # 'Object' in SameValueNonNumber
        # 'Number' in Abstract Relational Comparison
        [vara, varb, type_name] = children
        t = NamedType(type_name)
        enva = env0.ensure_expr_is_of_type(vara, t); assert enva is env0
        envb = env0.ensure_expr_is_of_type(varb, t); # assert envb is env0
        return (envb, envb)

    elif p == r"{CONDITION_1} : {EX} is the same Parse Node as {EX}":
        [exa, exb] = children
        env0.assert_expr_is_of_type(exa, T_Parse_Node)
        env0.assert_expr_is_of_type(exb, T_Parse_Node)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} has attribute values { {DSBN}: \*true\*, {DSBN}: \*true\* }':
        [var, dsbn1, dsbn2] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Property_Descriptor)
        assert dsbn1.children == ['Writable']
        assert dsbn2.children == ['Enumerable']
        return (env1, env1)

    elif p == r'{CONDITION_1} : {EX} is {VAR}':
        [a_ex, b_ex] = children
        (a_t, a_env) = tc_expr(a_ex, env0)
        (b_t, b_env) = tc_expr(b_ex, env0); assert b_env is env0
        assert a_t != T_TBD
        if b_t == T_TBD:
            env1 = env0.with_expr_type_replaced(b_ex, a_t)
        elif a_t == T_Number and b_t == T_Integer_:
            env1 = env0
        elif a_t == T_Abrupt | T_Undefined and b_t == T_Abrupt:
            # Evaluate()
            env1 = env0
        else:
            assert a_t.is_a_subtype_of_or_equal_to(b_t)
            env1 = env0
        e = env_or(a_env, env0)
        return (e, e)

    elif p == r'{CONDITION_1} : {VAR} has {VAR} in its range':
        [sdbe_var, loc_var] = children
        env1 = env0.ensure_expr_is_of_type(sdbe_var, T_Shared_Data_Block_event)
        env2 = env1.ensure_expr_is_of_type(loc_var, T_Integer_)
        return (env2, env2)

    elif p in [
        r'{CONDITION_1} : {VAR} is in {VAR}',
        r'{CONDITION_1} : {VAR} is not in {VAR}',
        r'{CONDITION_1} : {VAR} occurs exactly once in {VAR}',
    ]:
        [item_var, container_var] = children
        (container_t, env1) = tc_expr(container_var, env0); assert env1 is env0
        if container_t == T_String:
            env0.assert_expr_is_of_type(item_var, T_code_unit_)
        elif container_t == T_CharSet:
            env0.assert_expr_is_of_type(item_var, T_character_)
        elif isinstance(container_t, ListType):
            # env0.assert_expr_is_of_type(item_var, container_t.element_type)
            # The stack only contains STMRs:
            assert container_t == ListType(T_Source_Text_Module_Record)
            # _requiredModule_ might be a non-ST MR:
            env0.assert_expr_is_of_type(item_var, T_Module_Record)
            # It's still reasonable to ask if _requiredModule_ is in the stack.
        else:
            assert 0, container_t
        return (env0, env0)

    elif p == r'{CONDITION_1} : its value is the name of a Job Queue recognized by this implementation':
        # Once, in EnqueueJob
        [] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : There are sufficient bytes in {VAR} starting at {VAR} to represent a value of {VAR}':
        [ab_var, st_var, t_var] = children
        env0.assert_expr_is_of_type(ab_var, T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_)
        env0.assert_expr_is_of_type(st_var, T_Integer_)
        env0.assert_expr_is_of_type(t_var, T_String)
        return (env0, env0)

    elif p == r'{CONDITION_1} : The next step never returns an abrupt completion because {DOTTING} is not {LITERAL}':
        [dotting, literal] = children
        env0.assert_expr_is_of_type(dotting, T_String)
        env0.assert_expr_is_of_type(literal, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : The next step never returns an abrupt completion because {VAR} is a String value":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} does not have an own property with key {VAR}':
        [obj_var, key_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} is not already suspended':
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} is on the list of waiters in {VAR}':
        [w_var, wl_var] = children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} was notified explicitly by another agent calling NotifyWaiter\({VAR}, {VAR}\)':
        [w_var, *blah] = children
        env0.assert_expr_is_of_type(w_var, T_agent_signifier_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} is as small as possible':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} is odd':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (env0, env0)

    elif p == r'{CONDITION_1} : {PROD_REF} is `export` {NONTERMINAL}':
        [prod_ref, nont] = children
        return (env0, env0)

    elif p in [
        r'{CONDITION_1} : {VAR} is empty',
        r"{CONDITION_1} : {VAR} is not empty",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_CharSet | T_List | T_String)
        # XXX For String, change spec to "is [not] the empty String" ?
        return (env0, env0)

    elif p == r"{CONDITION_1} : We've reached the starting point of an `import \*` circularity":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} provides the direct binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} imports a specific binding for this export":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is not contained within an? {NONTERMINAL}, {NONTERMINAL}, or {NONTERMINAL}":
        [var, *nont_] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is the {NONTERMINAL} of an? {NONTERMINAL}":
        [var, nont1, nont2] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is -1":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is not finite":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {DOTTING} is not the ordinary object internal method defined in {EMU_XREF}":
        [dotting, emu_xref] = children
        env0.assert_expr_is_of_type(dotting, T_proc_)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {VAR} and {VAR} are the same Module Record",
        r"{CONDITION_1} : {VAR} and {DOTTING} are the same Module Record",
        r"{CONDITION_1} : {DOTTING} and {DOTTING} are not the same Module Record",
    ]:
        [ex1, ex2] = children
        env0.assert_expr_is_of_type(ex1, T_Module_Record)
        env0.assert_expr_is_of_type(ex2, T_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} are the same Shared Data Block values":
        [exa, exb] = children
        env1 = env0.ensure_expr_is_of_type(exa, T_Shared_Data_Block)
        env2 = env1.ensure_expr_is_of_type(exb, T_Shared_Data_Block)
        return (env2, env2)

    elif p == r"{CONDITION_1} : This is a circular import request":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : A `default` export was not explicitly defined by this module":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : There is more than one `\*` import that includes the requested name":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : every field in {VAR} is absent":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Property_Descriptor)
        return (env0, env0)

    elif p == r"{CONDITION_1} : its value is {LITERAL}":
        # todo: change the grammar or the spec
        [lit] = children
        env0.assert_expr_is_of_type(lit, T_Boolean)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the {DSBN} fields of {VAR} and {VAR} are the Boolean negation of each other":
        [dsbn, a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_Property_Descriptor)
        env0.assert_expr_is_of_type(b_var, T_Property_Descriptor)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} have different results":
        [a_ex, b_ex] = children
        env0.assert_expr_is_of_type(a_ex, T_Boolean)
        env0.assert_expr_is_of_type(b_ex, T_Boolean)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} does not include the element {LITERAL}":
        [list_var, item_lit] = children
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_String))
        env0.assert_expr_is_of_type(item_lit, T_String)
        return (env1, env1)

    elif p == r"{CONDITION_1} : the order of evaluation needs to be reversed to preserve left to right evaluation":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a prefix of {VAR}":
        [a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_String)
        env0.assert_expr_is_of_type(b_var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the mathematical value of {VAR} is less than the mathematical value of {VAR}":
        [a_var, b_var] = children
        env0.assert_expr_is_of_type(a_var, T_Number)
        env0.assert_expr_is_of_type(b_var, T_Number)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is absent or has the value {LITERAL}":
        [ex, literal] = children
        (lit_type, env1) = tc_expr(literal, env0); assert env1 is env0
        assert lit_type == T_Boolean
        # hrm
        return (env1, env1)

    elif p == r"{CONDITION_1} : we return here":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the async function either threw an exception or performed an implicit or explicit return; all awaiting is done":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the async generator either threw an exception or performed either an implicit or explicit return":
        [] = children
        return (env0, env0)

    elif p == r"{TYPE_TEST} : Type\({TYPE_ARG}\) is {VAR}":
        [type_arg, var] = children
        env0.assert_expr_is_of_type(var, T_LangTypeName_)
        return (env0, env0)

    elif p == r"{TYPE_TEST} : Type\({TYPE_ARG}\) is not an element of {VAR}":
        [type_arg, var] = children
        env0.assert_expr_is_of_type(var, ListType(T_LangTypeName_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} does not contain a rest parameter, any binding patterns, or any initializers. It may contain duplicate identifiers":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} has any elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : it must be in the object Environment Record":
        # elliptical
        [] = children
        return (env0, env0)
 
    elif p == r"{CONDITION_1} : This method is never invoked\. See {EMU_XREF}":
        [emu_xref] = children
        return (None, env0)

    elif p == r"{CONDITION_1} : The following loop will terminate":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the base of {VAR} is an Environment Record":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the above call will not return here, but instead evaluation will continue as if the following return has already occurred":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} binds a single name":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {VAR} contains any duplicate entries",
        r"{CONDITION_1} : {VAR} contains no duplicate entries",
        r"{CONDITION_1} : {VAR} has any duplicate entries",
        r"{CONDITION_1} : {VAR} has no duplicate entries",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : All of the above CreateDataProperty operations return {LITERAL}":
        [literal] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : the generator either threw an exception or performed either an implicit or explicit return":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a String value that is this specification's name of an intrinsic object. The corresponding object must be an intrinsic that is intended to be used as the {DSBN} value of an object":
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} contain the same values in the same order":
        # Once, in GetTemplateObject.
        [a_ex, b_ex] = children
        env0.assert_expr_is_of_type(a_ex, ListType(T_String))
        env1 = env0.ensure_expr_is_of_type(b_ex, ListType(T_String))
        return (env0, env0)

    elif p == r"{CONDITION_1} : The VariableEnvironment and LexicalEnvironment of {VAR} are the same":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} does not currently have a property {VAR}":
        [obj_var, pn_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(pn_var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r"{CONDITION_1} : its value is either {LITERAL} or {LITERAL}":
        # once, in OrdinaryToPrimitive
        # elliptical    
        [alit, blit] = children
        return (env0, env0)

    elif p == r'{CONDITION_1} : {VAR} contains any code unit other than `"g"`, `"i"`, `"m"`, `"s"`, `"u"`, or `"y"` or if it contains the same code unit more than once':
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} contains {LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lit, T_String | T_code_unit_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : This is an attempt to change the value of an immutable binding":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is now the running execution context":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {PROD_REF} is the token `false`",
        r"{CONDITION_1} : {PROD_REF} is the token `true`",
    ]:
        [prod_ref] = children
        assert prod_ref.source_text() == '|BooleanLiteral|'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} has no elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : an implementation-defined debugging facility is available and enabled":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} contains a formal parameter mapping for {VAR}":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Object)
        env0.assert_expr_is_of_type(bvar, T_String | T_Symbol)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : This is a re-export of an imported module namespace object",
        r"{CONDITION_1} : this is a re-export of a single name",
    ]:
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {DOTTING} exists and has been initialized":
        [dotting] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} and {VAR} are not the same Realm Record":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Realm_Record)
        env0.assert_expr_is_of_type(bvar, T_Realm_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : any element of {NAMED_OPERATION_INVOCATION} also occurs in {NAMED_OPERATION_INVOCATION}":
        [anoi, bnoi] = children
        env0.assert_expr_is_of_type(anoi, ListType(T_String)) # T_String not justified, but always correct (currently)
        env0.assert_expr_is_of_type(bnoi, ListType(T_String))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} contains any duplicate elements":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_List)
        return (env0, env0)

    elif p == r"{CONDITION_1} : All named exports from {VAR} are resolvable":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Source_Text_Module_Record)
        return (env0, env0)

#    elif p == r"{CONDITION_1} : ModuleDeclarationInstantiation has already been invoked on {VAR} and successfully completed":
#        [var] = children
#        env0.assert_expr_is_of_type(var, T_Module_Record)
#        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} has been linked and declarations in its module environment have been instantiated":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    elif p == r'''{CONDITION_1} : The value of {VAR}'s `"length"` property is {EX}''':
        [var, ex] = children
        env0.assert_expr_is_of_type(var, T_Object)
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (env0, env0)

    elif p == r"{NUM_COMPARISON} : {VAR} is finite and less than {VAR}":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Integer_) # XXX or infinity
        env0.assert_expr_is_of_type(bvar, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the character {EX} is one of {NONTERMINAL}":
        [ex, nonterminal] = children
        env0.assert_expr_is_of_type(ex, T_character_)
        assert nonterminal.children == ['LineTerminator']
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is not the same character value as {NAMED_OPERATION_INVOCATION}":
        [anoi, bnoi] = children
        env0.assert_expr_is_of_type(anoi, T_character_)
        env0.assert_expr_is_of_type(bnoi, T_character_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is finite":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (env0, env0)

    elif p == r"{CONDITION_1} : All dependencies of {VAR} have been transitively resolved and {VAR} is ready for evaluation":
        [var, var2] = children
        assert var.children == var2.children
        env0.assert_expr_is_of_type(var, T_Module_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the host requires use of an exotic object to serve as {VAR}'s global object":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the host requires that the `this` binding in {VAR}'s global scope return an object other than the global object":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {VAR} is the source code of a script",
        r"{CONDITION_1} : {VAR} is the source code of a module",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Unicode_code_points_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the code units at index \({SUM}\) and \({SUM}\) within {VAR} do not represent hexadecimal digits":
        [posa, posb, var] = children
        env0.assert_expr_is_of_type(posa, T_Integer_)
        env0.assert_expr_is_of_type(posb, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the most significant bit in {VAR} is [01]":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the two most significant bits in {VAR} are not 10":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} does not contain a valid UTF-8 encoding of a Unicode code point":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is {U_LITERAL}":
        [noi, lit] = children
        (noi_t, noi_env) = tc_expr(noi, env0); assert noi_env is env0
        env0.assert_expr_is_of_type(lit, noi_t)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} can be the string-concatenation of {VAR} and some other String {VAR}":
        [a,b,c] = children
        env0.assert_expr_is_of_type(a, T_String)
        env0.assert_expr_is_of_type(b, T_String)
        # Hm, This is causes `c` to come into existence.
        # env0.assert_expr_is_of_type(c, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} and {VAR} each contain exactly one character":
        [a,b] = children
        env0.assert_expr_is_of_type(a, T_CharSet)
        env0.assert_expr_is_of_type(b, T_CharSet)
        return (env0, env0)

    elif p == r"{CONDITION_1} : _R_ contains any \|GroupName\|": # XXX
        return (env0, env0)
    elif p == r"{CONDITION_1} : the _i_th capture of _R_ was defined with a \|GroupName\|":
        return (env0, env0)
    elif p == r"{CONDITION_1} : A unique such \|GroupSpecifier\| is found":
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a List of Unicode code points that is identical to a List of Unicode code points that is a canonical, unaliased Unicode property name listed in the &ldquo;Canonical property name&rdquo; column of {EMU_XREF}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a List of Unicode code points that is identical to a List of Unicode code points that is a property value or property value alias for Unicode property {VAR} listed in the &ldquo;Property value and aliases&rdquo; column of {EMU_XREF} or {EMU_XREF}":
        [va, vb, emu_xref1, emu_xref2] = children
        env0.assert_expr_is_of_type(va, ListType(T_Integer_))
        env0.assert_expr_is_of_type(vb, ListType(T_Integer_))
        return (env0, env0)
    
    elif p == r"{CONDITION_1} : {VAR} is a Unicode property name or property alias listed in the &ldquo;Property name and aliases&rdquo; column of {EMU_XREF}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is a binary Unicode property or binary property alias listed in the &ldquo;Property name and aliases&rdquo; column of {EMU_XREF}":
        [v, emu_xref] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {NAMED_OPERATION_INVOCATION} is identical to a List of Unicode code points that is the name of a Unicode general category or general category alias listed in the &ldquo;Property value and aliases&rdquo; column of {EMU_XREF}":
        [noi, emu_xref] = children
        env0.assert_expr_is_of_type(noi, ListType(T_Integer_))
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} does not have a Generator component":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is an AsyncGenerator instance":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_AsyncGenerator_object_)
        return (env1, env1)
    
    elif p == r"{CONDITION_1} : {EX} is listed in the Code Unit Value column of {EMU_XREF}":
        [ex, emu_xref] = children
        assert emu_xref.source_text() == '<emu-xref href="#table-json-single-character-escapes"></emu-xref>'
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (env0, env0)

    # ----

    elif p == r"{CONDITION_1} : {VAR} is not on the list of waiters in any WaiterList":
        [sig_var] = children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is not on the list of waiters in {VAR}":
        [sig_var, wl_var] = children
        env0.assert_expr_is_of_type(sig_var, T_agent_signifier_)
        env0.assert_expr_is_of_type(wl_var, T_WaiterList)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} and {EX} are valid byte offsets within the memory of {VAR}":
        [offset1, offset2, sdb] = children
        env0.assert_expr_is_of_type(offset1, T_Integer_)
        env0.assert_expr_is_of_type(offset2, T_Integer_)
        env0.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is divisible by {NUM_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        env0.assert_expr_is_of_type(lit, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is a Boolean value":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Boolean, asserting)

    elif p == r"{CONDITION_1} : {EX} is a Number value":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Number, asserting)

    elif p == r"{CONDITION_1} : {EX} is a Symbol value":
        [ex] = children
        return env0.with_type_test(ex, 'is a', T_Symbol, asserting)

    elif p == r"{CONDITION_1} : {VAR} is a Synchronize event":
        [v] = children
        return env0.with_type_test(v, 'is a', T_Synchronize_event, asserting)

    elif p == r"{CONDITION_1} : {VAR} is not one of {LITERAL}, {LITERAL}, {LITERAL}, or {LITERAL}":
        [var, *lit_] = children
        tc_expr
        (var_t, var_env) = tc_expr(var, env0); assert var_env is env0
        for lit in lit_:
            env0.assert_expr_is_of_type(lit, var_t)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is one of the code units in {STR_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        env0.assert_expr_is_of_type(lit, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : neither {VAR} nor any prefix of {VAR} satisfies the syntax of a {NONTERMINAL} \(see {EMU_XREF}\)":
        [var1, var2, nont, emu_xref] = children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the four code units at indices {SUM}, {SUM}, {SUM}, and {SUM} within {VAR} are all hexadecimal digits":
        [e1, e2, e3, e4, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(e1, T_Integer_)
        env0.assert_expr_is_of_type(e2, T_Integer_)
        env0.assert_expr_is_of_type(e3, T_Integer_)
        env0.assert_expr_is_of_type(e4, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the two code units at indices {SUM} and {SUM} within {VAR} are both hexadecimal digits":
        [i1, i2, var] = children
        env0.assert_expr_is_of_type(i1, T_Integer_)
        env0.assert_expr_is_of_type(i2, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : GlobalSymbolRegistry does not currently contain an entry for {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String | T_Symbol)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the first two code units of {VAR} are either {STR_LITERAL} or {STR_LITERAL}":
        [var, lita, litb] = children
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} contains a code unit that is not a radix-{VAR} digit":
        [svar, rvar] = children
        env0.assert_expr_is_of_type(svar, T_String)
        env0.assert_expr_is_of_type(rvar, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} does not have all of the internal slots of an? (\w+) Iterator Instance \({EMU_XREF}\)":
        [var, x, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Object)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is the String value {STR_LITERAL} or the String value {STR_LITERAL}":
        [var, lita, litb] = children
        env0.assert_expr_is_of_type(var, T_Tangible_) # you'd expect T_String, but _hint_ in Date.prototype [ @@toPrimitive ]
        env0.assert_expr_is_of_type(lita, T_String)
        env0.assert_expr_is_of_type(litb, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is the String value {STR_LITERAL}":
        [var, lit] = children
        env0.assert_expr_is_of_type(var, T_Tangible_) # you'd expect T_String, but _hint_ in Date.prototype [ @@toPrimitive ]
        env0.assert_expr_is_of_type(lit, T_String)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : this method was called with more than one argument",
        r"{CONDITION_1} : only one argument was passed",
    ]:
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is an integer index &le; {VAR}":
        [a, b] = children
        env0.assert_expr_is_of_type(b, T_Integer_)
        env1 = env0.ensure_expr_is_of_type(a, T_Integer_)
        return (env1, env1)

    elif p == r"{CONDITION_1} : {VAR} is added as a single item rather than spread":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : both {EX} and {EX} are {LITERAL}":
        [exa, exb, lit] = children
        (t, env1) = tc_expr(lit, env0); assert env1 is env0
        env1.assert_expr_is_of_type(exa, t)
        env1.assert_expr_is_of_type(exb, t)
        return (env1, env1)

    elif p == r"{CONDITION_1} : the number of actual arguments is {NUM_LITERAL}":
        [lit] = children
        env0.assert_expr_is_of_type(lit, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : the sequence of code units of {VAR} starting at {VAR} of length {VAR} is the same as the full code unit sequence of {VAR}":
        [sa, k, n, sb] = children
        env0.assert_expr_is_of_type(sa, T_String)
        env0.assert_expr_is_of_type(k, T_Integer_)
        env0.assert_expr_is_of_type(n, T_Integer_)
        env0.assert_expr_is_of_type(sb, T_String)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is not currently an element of {VAR}":
        [item_var, list_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(item_var, list_var)
        return (env1, env1)

    elif p == r"{NUM_COMPARISON} : {NUM_COMPARAND} is 10 or less":
        [x] = children
        env0.assert_expr_is_of_type(x, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : no arguments were passed to this function invocation":
        [] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {EX} is neither {LITERAL} nor the active function":
        [ex, lit] = children
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is any ECMAScript language value other than an Object with a {DSBN} internal slot. If it is such an Object, the definition in {EMU_XREF} applies":
        [var, dsbn, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : The value of {VAR}'s `length` property is {VAR}":
        [ovar, ivar] = children
        env0.assert_expr_is_of_type(ovar, T_Object)
        env0.assert_expr_is_of_type(ivar, T_Integer_)
        return (env0, env0)

    elif p == r"{CONDITION_1} : When we reach this step, {VAR} has already been removed from the execution context stack and {VAR} is the currently running execution context":
        [vara, varb] = children
        env0.assert_expr_is_of_type(vara, T_execution_context)
        env0.assert_expr_is_of_type(varb, T_execution_context)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} has an? {DSBN} internal slot whose value is an? (Object|PromiseCapability Record)":
        [var, dsbn, typename] = children
        env0.assert_expr_is_of_type(var, T_Object) # more specific?
        return (env0, env0)

    elif p == r"{CONDITION_1} : {PAIR} is in {EX}":
        [pair, ex] = children
        env0.assert_expr_is_of_type(pair, T_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are in {EX}",
        r"{CONDITION_1} : the pairs {PAIR} and {PAIR} are not in {EX}",
        r"{CONDITION_1} : either {PAIR} or {PAIR} is in {EX}",
    ]:
        [paira, pairb, ex] = children
        env0.assert_expr_is_of_type(paira, T_pair_)
        env0.assert_expr_is_of_type(pairb, T_pair_)
        env0.assert_expr_is_of_type(ex, T_Relation)
        return (env0, env0)

    elif p == r"{CONDITION_1} : Each of the above calls will return {LITERAL}":
        [lit] = children
        assert lit.source_text() == '*true*'
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} and {VAR} are in a race in {VAR}":
        [ea, eb, exe] = children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(exe, T_candidate_execution)
        return (env0, env0)

    elif p in [
        r"{CONDITION_1} : {VAR} and {VAR} do not have disjoint ranges",
        r"{CONDITION_1} : {VAR} and {VAR} have equal ranges",
        r"{CONDITION_1} : {VAR} and {VAR} have overlapping ranges",
    ]:
        [ea, eb] = children
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        return (env0, env0)

    elif p == r"{CONDITION_1} : {VAR} is not {VAR}":
        [ea, eb] = children
        # over-specific:
        env0.assert_expr_is_of_type(ea, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(eb, T_Shared_Data_Block_event)
        return (env0, env0)


    # elif p == r"{CONDITION_1} : All named exports from {VAR} are resolvable":
    # elif p == r"{CONDITION_1} : any static semantics errors are detected for {VAR} or {VAR}":
    # elif p == r"{CONDITION_1} : either {EX} or {EX} is present":
    # elif p == r"{CONDITION_1} : either {EX} or {EX} is {LITERAL}":
    # elif p == r"{CONDITION_1} : replacing the {NONTERMINAL} {VAR} with a {NONTERMINAL} that has {VAR} as a {NONTERMINAL} would not produce any Early Errors for {VAR}":
    # elif p == r"{CONDITION_1} : the Unicode Character Database provides a language insensitive lower case equivalent of {VAR}":
    # elif p == r"{CONDITION_1} : there is an infinite number of ReadSharedMemory or ReadModifyWriteSharedMemory events in SharedDataBlockEventSet\({VAR}\) with equal range that {SAB_RELATION} {VAR}":
    # elif p == r"{CONDITION_1} : there is no such integer {VAR}":
    # elif p == r"{CONDITION_1} : {VAR} _R_ {VAR}":
    # elif p == r"{CONDITION_1} : {VAR} and {VAR} are in {EX}":
    # elif p == r"{CONDITION_1} : {VAR} and {VAR} have equal range":
    # elif p == r"{CONDITION_1} : {VAR} has _order_ `"Init"`":
    # elif p == r"{CONDITION_1} : {VAR} is a List of WriteSharedMemory or ReadModifyWriteSharedMemory events":
    # elif p == r"{CONDITION_1} : {VAR} is a WriteSharedMemory or ReadModifyWriteSharedMemory event":
    # elif p == r"{CONDITION_1} : {VAR} is an exotic String object":
    # elif p == r"{CONDITION_1} : {VAR} is an instance of a nonterminal":
    # elif p == r"{CONDITION_1} : {VAR} is an instance of {VAR}":
    # elif p == r"{CONDITION_1} : {VAR} is any ECMAScript language value other than an Object with an? {DSBN} internal slot":
    # elif p == r"{CONDITION_1} : {VAR} is before {VAR} in List order of {EX}":
    # elif p == r"{CONDITION_1} : {VAR} is bound by any syntactic form other than an? {NONTERMINAL}, an? {NONTERMINAL}, the {NONTERMINAL} of a for statement, the {NONTERMINAL} of a for-in statement, or the {NONTERMINAL} of a for-in statement":
    # elif p == r"{CONDITION_1} : {VAR} is not the Environment Record for a \|Catch\| clause":
    # elif p == r"{CONDITION_1} : {EX} is not {LITERAL} or {LITERAL}":
    # elif p == r"{CONDITION_1} : {VAR} is not {VAR}":
    # elif p == r"{CONDITION_1} : {VAR} {SAB_RELATION} {VAR}":
    # elif p == r"{CONDITION_AS_COMMAND} : At least one of {VAR} or {VAR} does not have {DSBN} {STR_LITERAL} or {VAR} and {VAR} have overlapping ranges\.":
    # elif p == r"{CONDITION_AS_COMMAND} : It is not the case that {CONDITION}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : The host provides a {SAB_RELATION} Relation for {DOTTING}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : There is a List of length equal to {DOTTING} of WriteSharedMemory or ReadModifyWriteSharedMemory events {VAR} such that {PREFIX_PAREN} is {VAR}\.":
    # elif p == r"{CONDITION_AS_COMMAND} : There is no WriteSharedMemory or ReadModifyWriteSharedMemory event {VAR} in SharedDataBlockEventSet\({VAR}\) with equal range as {VAR} such that {VAR} is not {VAR}, {VAR} {SAB_RELATION} {VAR}, and {VAR} {SAB_RELATION} {VAR}\.":
    # elif p == r"{CONDITION_AS_COMMAND} : There is no WriteSharedMemory or ReadModifyWriteSharedMemory event {VAR} that has {VAR} in its range such that {CONDITION}\.":
    # elif p == r"{CONDITION_AS_COMMAND} : There is no cycle in the union of {SAB_RELATION} and {SAB_RELATION}\.":
    # elif p == r"{CONDITION_AS_COMMAND} : {DOTTING} is a strict partial order, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} _R_ {VAR} or {VAR} _R_ {VAR}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} has coherent reads, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} has sequentially consistent atomics\.":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} has tear free reads, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} has valid chosen reads, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} has {VAR} in its range\.":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} is equal to {VAR} and {SETTABLE} is equal to {SETTABLE} for all integer values {VAR} in the range {NUM_LITERAL} through {VAR}, exclusive\.":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} is not {VAR}, and":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} is not {VAR}\.":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} {SAB_RELATION} {VAR} or {VAR} {SAB_RELATION} {VAR}\.":
    # elif p == r"{CONDITION_AS_COMMAND} : {VAR} {SAB_RELATION} {VAR}\.":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : it is not the case that {CONDITION}":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : there is no {VAR} such that {CONDITION}":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : {VAR} _R_ {VAR}":
    # elif p == r"{CONDITION_AS_SMALL_COMMAND} : {VAR} {SAB_RELATION} {VAR}":
    # elif p == r"{CONDITION} : {CONDITION_1}, {CONDITION_1}, and {CONDITION_1}":

    else:
        stderr()
        stderr("tc_cond:")
        stderr('    elif p == r"%s":' % p)
        sys.exit(0)

# ------------------------------------------------------------------------------

def tc_expr(expr, env0, expr_value_will_be_discarded=False):
    p = str(expr.prod)
    expr_text = expr.source_text()

    if trace_this_op:
        print()
        print("Entering e:", p)
        print("           ", expr_text)
        mytrace(env0)

    if expr_text in env0.vars:
        if trace_this_op:
            print()
            print("Getting type from cache")
        expr_type = env0.vars[expr_text]
        # stderr("cache: %s :: %s" % (expr_text, expr_type))
        assert isinstance(expr_type, Type)
        env1 = env0

    else:
        (expr_type, env1) = tc_expr_(expr, env0, expr_value_will_be_discarded)

        assert isinstance(expr_type, Type)
        assert isinstance(env1, Env)

        if expr_type in [T_Top_, T_TBD, T_0]:
            add_pass_error(
                expr,
                "warning: expr `%s` has type %s" % (expr_text, expr_type)
            )

    if 0 and not expr_value_will_be_discarded:
        if expr_type != T_Top_ and T_not_returned.is_a_subtype_of_or_equal_to(expr_type):
            add_pass_error(
                expr,
                f"warning: `{p}` could be not_returned"
            )
            # There are a few problems with this:
            # - If a param's type isn't Top_, but has been carved down from Top_,
            #   it will probably include not_returned.
            #   (Mind you, there's a problem there anyway.)
            #
            # - Can't pass expr_value_will_be_discarded=True to assert_expr_is_of_type.
            #   (Only affects "Perform LeaveCriticalSection" step.)
            #
            # - In cases where it actually makes a useful complaint,
            #   it complains at multiple levels.
            #   (But that's okay, because you're going to fix it, right?)

    if trace_this_op:
        print()
        print("Leaving e:", p)
        print("          ", expr_text)
        mytrace(env1)

    return (expr_type, env1)

# --------------------

def tc_expr_(expr, env0, expr_value_will_be_discarded):
    p = str(expr.prod)
    children = expr.children

    # stderr('>>>', expr.source_text())

    if p in [
        r"{EXPR} : the result of performing {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the result of {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : {EX}",
        r"{EXPR} : {FACTOR} \(a value so large that it will round to \*\+&infin;\*\)",
        r"{EX} : \({EX}\)",
        r"{EX} : the previous value of {VAR}",
        r"{EX} : the value of {SETTABLE}",
        r"{EX} : the {VAR} flag",
        r"{EX} : {CU_LITERAL}",
        r"{EX} : {LITERAL}",
        r"{EX} : {LOCAL_REF}",
        r"{EX} : {NAMED_OPERATION_INVOCATION}",
        r"{EX} : {NUM_EXPR}",
        r"{EX} : {PRODUCT}",
        r"{EX} : {RECORD_CONSTRUCTOR}",
        r"{EX} : {SUM}",
        r"{EX} : {U_LITERAL}",
        r"{FACTOR} : \({NUM_EXPR}\)",
        r"{FACTOR} : \({SUM}\)",
        r"{FACTOR} : {NAMED_OPERATION_INVOCATION}",
        r"{FACTOR} : {NUM_LITERAL}",
        r"{FACTOR} : {PREFIX_PAREN}",
        r"{FACTOR} : {SETTABLE}",
        r"{LITERAL} : {CU_LITERAL}",
        r"{LITERAL} : {NUM_LITERAL}",
        r"{LOCAL_REF} : {PROD_REF}",
        r"{LOCAL_REF} : {SETTABLE}",
        r"{NOI} : {PREFIX_PAREN}",
        r"{NUM_COMPARAND} : {FACTOR}",
        r"{NUM_COMPARAND} : {NUM_LITERAL}",
        r"{NUM_COMPARAND} : {PREFIX_PAREN}",
        r"{NUM_COMPARAND} : {SETTABLE}",
        r"{NUM_COMPARAND} : {SUM}",
        r"{NUM_COMPARAND} : {PRODUCT}",
        r"{NUM_EXPR} : {PRODUCT}",
        r"{NUM_EXPR} : {SUM}",
        r"{NUM_EXPR} : {BIT_OP}",
        r"{PRODUCT} : [+-]{FACTOR}",
        r"{SETTABLE} : {DOTTING}",
        r"{TERM} : \({PRODUCT}\)",
        r"{TERM} : {DOTTING}",
        r"{TERM} : {FACTOR}",
        r"{TERM} : {PREFIX_PAREN}",
        r"{TERM} : {PRODUCT}",
        r"{TYPE_ARG} : {DOTTING}",
        r"{TYPE_ARG} : {VAR}",
    ]:
        [child] = children
        return tc_expr(child, env0, expr_value_will_be_discarded)

    elif p == r"{EXPR} : the (Matcher|CharSet|Completion Record) that is {EXPR}":
        [type_name, ex] = children
        if type_name == 'Completion Record':
            t = T_Tangible_ | T_empty_ | T_Abrupt
        else:
            t = maybe_NamedType(type_name)
        env1 = env0.ensure_expr_is_of_type(ex, t)
        return (t, env1)

    # ------------------------------------------------------
    # literals

    elif p == r'{LITERAL} : \*(false|true|null|undefined)\*':
        [chars] = children
        if chars in ['false', 'true']:
            t = T_Boolean
        elif chars == 'null':
            t = T_Null
        elif chars == 'undefined':
            t = T_Undefined
        else:
            assert 0
        return (t, env0)

    elif p == r'{LITERAL} : \*(true|false|undefined)\*':
        [chars] = children
        if chars == 'undefined':
            return (T_Undefined, env0)
        elif chars in ['true', 'false']:
            return (T_Boolean, env0)
        else:
            assert 0

    elif p == r"{LITERAL} : (@@\w+)":
        return (T_Symbol, env0)    

    elif p == r"{NUM_LITERAL} : &infin;":
        return (T_Infinity_, env0)

    elif p == r"{LITERAL} : {TYPE_NAME}":
        [type_name] = children
        return (T_LangTypeName_, env0)

    elif p == r"{EX} : hint (Number|String)":
        [type_name] = children
        return (T_LangTypeName_, env0)

    elif p in [
        r"{LITERAL} : the value \*undefined\*",
        r"{U_LITERAL} : \*undefined\*",
    ]:
        [] = children
        return (T_Undefined, env0)

    elif p == r"{LITERAL} : ~(\[empty\]|failure|strict|empty|lexical|enumerate|Normal|Arrow|Method|assignment|varBinding|lexicalBinding|iterate|global|async|async-iterate|non-generator|sync|invalid|simple)~":
        [chars] = children
        if chars == '[empty]':
            # The spec uses ~[empty]~ to denote
            # what you get when you ask for, e.g.
            # "the second |Expression|",
            # and it's not present.
            return (T_not_in_node, env0)
        elif chars == 'empty':
            return (T_empty_, env0)
        elif chars == 'failure':
            return (T_match_failure_, env0)
        elif chars == 'strict':
            # T_this_mode or T_AssignmentTargetType_, depending on context
            # super-kludge to get context:
            if 'Mode' in spec.text[expr.start_posn-20:expr.start_posn]:
                return (T_this_mode, env0)
            else:
                return (T_AssignmentTargetType_, env0)
        elif chars in ['lexical', 'global']:
            return (T_this_mode, env0)
        elif chars in ['enumerate', 'iterate', 'async-iterate']:
            return (T_IterationKind_, env0)
        elif chars in ['Normal', 'Arrow', 'Method']:
            return (T_FunctionKind1_, env0)
        elif chars in ['assignment', 'varBinding', 'lexicalBinding']:
            return (T_LhsKind_, env0)
        elif chars in ['non-generator', 'async', 'sync']:
            return (T_IteratorKind_, env0)
        elif chars in ['simple', 'invalid']:
            return (T_AssignmentTargetType_, env0)
        else:
            assert 0, chars

    # --------------------------------------------------------
    # introduce metavariables:

    elif p == r'{EXPR} : {EX}, where {VAR} is {EX}':
        [exa, var, exb] = children
        (exb_type, env1) = tc_expr(exb, env0); assert env1 is env0
        env2 = env1.plus_new_entry(var, exb_type)
        (exa_type, env3) = tc_expr(exa, env2)
        return (exa_type, env3)

    elif p == r'{EXPR} : {EX}, where {VAR} is {EX} and {VAR} is {EX}':
        [ex3, var2, ex2, var1, ex1] = children

        (ex1_type, ex1_env) = tc_expr(ex1, env0); assert ex1_env is env0
        env1 = ex1_env.plus_new_entry(var1, ex1_type)

        (ex2_type, ex2_env) = tc_expr(ex2, env1); assert ex2_env is env1
        env2 = ex2_env.plus_new_entry(var2, ex2_type)

        (ex3_type, ex3_env) = tc_expr(ex3, env2); assert ex3_env is env2
        return (ex3_type, ex3_env)

    elif p in [
        r"{EXPR} : the largest possible nonnegative integer {VAR} not larger than {VAR} such that {CONDITION}; but if there is no such integer {VAR}, return the value {NUM_EXPR}",
        r"{EXPR} : the smallest possible integer {VAR} not smaller than {VAR} such that {CONDITION}; but if there is no such integer {VAR}, return the value {NUM_EXPR}",
    ]:
        [let_var, limit_var, cond, let_var2, default] = children
        assert same_source_text(let_var2, let_var)
        env0.assert_expr_is_of_type(limit_var, T_Integer_)
        env0.assert_expr_is_of_type(default, T_Integer_)
        env_for_cond = env0.plus_new_entry(let_var, T_Integer_)
        (t_env, f_env) = tc_cond(cond, env_for_cond)
        return (T_Integer_, t_env)

    # --------------------------------------------------------
    # invocation of named operation:

    elif p in [
        r"{NAMED_OPERATION_INVOCATION} : (?:the )?{ISDO_NAME} of {PROD_REF}",
        r"{NOI} : {OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF} as defined in {EMU_XREF}",
        r"{NOI} : {OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF}",
        r"{NOI} : {OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF}; if {LOCAL_REF} is not present, use the numeric value zero",
        r"{NOI} : {OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF} \(see {EMU_XREF}\)",
    ]:
        [callee, local_ref] = children[0:2]
        #
        [callee_op_name] = callee.children
        if callee_op_name == 'UTF16Encoding':
            # An abstract operation that uses SDO-style invocation.
            return tc_ao_invocation(callee_op_name, [local_ref], expr, env0)
        else:
            return tc_sdo_invocation(callee_op_name, local_ref, [], expr, env0)

    elif p == r"{NOI} : {OPN_BEFORE_FOROF} (?:for|of) {LOCAL_REF} {WITH_ARGS}":
        [callee, local_ref, with_args] = children
        [callee_op_name] = callee.children
        if with_args.prod.rhs_s in [
            'with argument {EX}',
            'with arguments {VAR} and {EX}',
            '(?:passing|using|with) {VAR} and {EX} as(?: the)? arguments',
            '(?:passing|using|with) {EX} as the argument',
            'using {VAR}, {VAR}, and {VAR} as(?: the)? arguments',
            'with {VAR}, {VAR}, and {VAR} as the arguments',
        ]:
            args = with_args.children 
        elif with_args.prod.rhs_s == 'with arguments {VAR} and {EX} as the optional {VAR} argument':
            args = with_args.children[0:2]
        else:
            assert 0, with_args.prod.rhs_s
        return tc_sdo_invocation(callee_op_name, local_ref, args, expr, env0)

    elif p in [
        r"{EXPR} : the result of evaluating {LOCAL_REF}",
        r"{EXPR} : the result of evaluating {LOCAL_REF}\. This may be of type Reference",
    ]:
        [local_ref] = children
        if local_ref.source_text() in [
            '|Atom|',
            '|AtomEscape|',
            '|Disjunction|',
            '|RegExpUnicodeEscapeSequence|',
            '|ClassAtom|',
            '|ClassEscape|',
            '|LeadSurrogate|',
            '|TrailSurrogate|',
            '|NonSurrogate|',
            '|CharacterEscape|',
        ]:
            op_name = 'regexp-Evaluate'
        else:
            op_name = 'Evaluation'
        return tc_sdo_invocation(op_name, local_ref, [], expr, env0)

    elif p == r"{EXPR} : the result of evaluating {LOCAL_REF} with argument {VAR}":
        [local_ref, var] = children
        assert local_ref.source_text() in [
            '|Atom|',
            '|AtomEscape|',
            '|Disjunction|',
        ]
        op_name = 'regexp-Evaluate'
        return tc_sdo_invocation(op_name, local_ref, [var], expr, env0)

    elif p == r"{EXPR} : the result of evaluating {NONTERMINAL} {VAR}":
        [nont, var] = children
        env0.assert_expr_is_of_type(var, ptn_type_for(nont))
        return tc_sdo_invocation('Evaluation', var, [], expr, env0)

#?    elif p == r"{EXPR} : the result of evaluating {DOTTING}":
#?        [dotting] = children
#?        return tc_sdo_invocation('Evaluation', dotting, [], expr, env0)

    elif p in [
        r"{NOI} : {LOCAL_REF} Contains {VAR}",
        r"{NOI} : {LOCAL_REF} Contains {NONTERMINAL}",
    ]:
        [lhs, rhs] = children
        return tc_sdo_invocation('Contains', lhs, [rhs], expr, env0)

    elif p == r"{FACTOR} : the MV of {PROD_REF}":
        [prod_ref] = children
        return tc_sdo_invocation('MV', prod_ref, [], expr, env0)

    # ------

    elif p in [
        r'{PREFIX_PAREN} : {OPN_BEFORE_PAREN}\({EXLIST_OPT}\)',
        r"{EXPR} : {OPN_BEFORE_PAREN}\({V}\)",
    ]:
        [opn_before_paren, arglist] = children
        if arglist.prod.lhs_s == '{EXLIST_OPT}':
            args = exes_in_exlist_opt(arglist)
        else:
            args = [arglist]

        if opn_before_paren.prod.rhs_s in [
            r'(ForIn/Of(?:Head|Body)Evaluation|(?!Type\b)[A-Za-z]\w+)',
            r'(HasPrimitiveBase)',
        ]:
            [callee_op_name] = opn_before_paren.children

            if callee_op_name == 'NormalCompletion':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                assert arg_type.is_a_subtype_of_or_equal_to(T_Normal)
                return_type = arg_type
                return (return_type, env0)
                # don't call tc_args etc

            elif callee_op_name == 'ThrowCompletion':
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                assert arg_type.is_a_subtype_of_or_equal_to(T_Normal)
                return_type = ThrowType(arg_type)
                return (return_type, env0)

            elif callee_op_name == 'Completion':
                assert len(args) == 1
                [arg] = args
                (arg_type, env1) = tc_expr(arg, env0)
                return_type = arg_type # bleah
                return (return_type, env1)

            elif callee_op_name == 'Await':
                assert len(args) == 1
                [arg] = args
                env0.assert_expr_is_of_type(arg, T_Tangible_|T_empty_)
                return (T_Abrupt|T_Tangible_|T_empty_, env0)

            elif callee_op_name in ['floor', 'abs']:
                assert len(args) == 1
                [arg] = args
                (arg_type, arg_env) = tc_expr(arg, env0); assert arg_env is env0
                if callee_op_name == 'floor':
                    return_type = T_Integer_
                elif callee_op_name == 'abs':
                    return_type = arg_type
                else:
                    assert 0
                return (return_type, env0)

            elif callee_op_name in ['min', 'max']:
                assert len(args) == 2
                env1 = env0
                for arg in args:
                    env1 = env1.ensure_expr_is_of_type(arg, T_Number)
                return (T_Integer_, env1)

            elif callee_op_name in [
                # 30232 Day Number and Time within Day
                'Day',
                'TimeWithinDay',

                # 30264 Month Number
                'MonthFromTime',

                # 30286 Date Number
                'DateFromTime',

                # 30305 Week Day
                'WeekDay',

                # 30424 Year Number
                'YearFromTime',

                # 30376 Hours, Minutes, Second, and Milliseconds
                'HourFromTime',
                'MinFromTime',
                'SecFromTime',
                'msFromTime',

                # 'DaylightSavingTA',
            ]:
                assert len(args) == 1
                [arg] = args
                env0.ensure_expr_is_of_type(arg, T_Number)
                return_type = T_Integer_
                return (return_type, env0)

            # ---------------

            else:
                callee_op = operation_named_[callee_op_name]
                if callee_op.kind == 'syntax-directed operation':
                    add_pass_error(
                        expr,
                        "Unusual to invoke a SDO via prefix-paren notation: " + expr.source_text()
                    )
                    assert len(args) == 1
                    return tc_sdo_invocation(callee_op_name, args[0], [], expr, env0)
                else:
                    assert callee_op.kind == 'abstract operation'
                params = callee_op.parameters
                return_type = callee_op.return_type
                # fall through to tc_args etc

                # if callee_op_name == 'ResolveBinding': pdb.set_trace()

        elif opn_before_paren.prod.rhs_s == r'{VAR}\.([A-Z][A-Za-z0-9]+)':
            [var, callee_op_name] = opn_before_paren.children

            (var_type, env1) = tc_expr(var, env0); assert env1 is env0
            var_type.is_a_subtype_of_or_equal_to(T_Environment_Record | T_Module_Record)

            callee_op = operation_named_[callee_op_name]
            assert callee_op.kind == 'concrete method'
            params = callee_op.parameters
            return_type = callee_op.return_type

        elif opn_before_paren.prod.rhs_s in [
            r'{DOTTING}',
            r'{VAR}',
        ]:
            [thing] = opn_before_paren.children
            (t, env0) = tc_expr(thing, env0)

            assert isinstance(t, ProcType)
            params = with_fake_param_names(t.param_types)
            return_type = t.return_type

#        elif opn_before_paren.prod.rhs_s == '{SAB_FUNCTION}':
#            [sab_function] = opn_before_paren.children
#            assert sab_function.prod.rhs_s == 'reads-bytes-from'
#            params = with_fake_param_names([ T_ReadSharedMemory_event | T_ReadModifyWriteSharedMemory_event ])
#            return_type = ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)

        else:
            assert 0, opn_before_paren.prod.rhs_s

        # context = 'in call to `%s`' % opn_before_paren.source_text()
        env2 = tc_args(params, args, env0, expr)
        return (return_type, env2)

    # -----

    elif p == r"{NOI} : Strict Equality Comparison {VAR} === {EX}":
        [lhs, rhs] = children
        return tc_ao_invocation('Strict Equality Comparison', [lhs, rhs], expr, env0)

    elif p in [
        r"{EXPR} : the result of the comparison {EX} == {EX}",
        r"{NOI} : Abstract Equality Comparison {VAR} == {VAR}",
    ]:
        [lhs, rhs] = children
        return tc_ao_invocation('Abstract Equality Comparison', [lhs, rhs], expr, env0)

    elif p == r"{NOI} : Abstract Relational Comparison {VAR} &lt; {VAR}":
        [lhs, rhs] = children
        return tc_ao_invocation('Abstract Relational Comparison', [lhs, rhs], expr, env0)

    elif p == r"{NOI} : Abstract Relational Comparison {VAR} &lt; {VAR} with {VAR} equal to {LITERAL}":
        [lhs, rhs, param, lit] = children
        return tc_ao_invocation('Abstract Relational Comparison', [lhs, rhs, lit], expr, env0)

    # --------------------------------------------------------

    elif p == r"{SETTABLE} : the {DSBN} field of {EXPR}":
        [dsbn, ex] = children
        [dsbn_name] = dsbn.children
        # over-specific:
        assert dsbn_name == 'EventList'
        env0.assert_expr_is_of_type(ex, T_Agent_Events_Record)
        return (ListType(T_event_), env0)

    elif p in [
        r'{DOTTING} : {VAR}\.{DSBN}',
        r"{DOTTING} : {DOTTING}\.{DSBN}",
    ]:
        [lhs_var, dsbn] = children
        lhs_text = lhs_var.source_text()
        [dsbn_name] = dsbn.children
        (lhs_t, env1) = tc_expr(lhs_var, env0)

        # assert dsbn_name != 'Type'
        # because anything involving [[Type]] has been intercepted at a higher level
        # Nope, _reaction_.[[Type]]

        # ----------------------------------

        # Handle "Completion Records" specially.
        while True: # ONCE
            if dsbn_name not in ['Type', 'Target', 'Value']:
                # We can't be dealing with a Completion Record
                break
            if lhs_t in [
                T_MapData_record_,
                T_PromiseReaction_Record,
                T_Property_Descriptor,
                T_boolean_value_record_,
                T_integer_value_record_,
            ]:
                # We know we're not dealing with a Completion Record
                break

            assert lhs_text not in [
                '_D_',
                '_Desc_',
                '_alreadyResolved_',
                '_current_',
                '_desc_',
                '_like_',
                '_newLenDesc_',
                '_oldLenDesc_',
                '_reaction_',
                '_remainingElementsCount_',
            ]

            result_memtypes = set()
            for memtype in lhs_t.set_of_types():
                if dsbn_name == 'Value':
                    if memtype.is_a_subtype_of_or_equal_to(T_Abrupt):
                        result_memtype = T_Tangible_ | T_empty_
                    elif memtype == T_Normal:
                        result_memtype = T_Tangible_ | T_empty_
                    elif memtype.is_a_subtype_of_or_equal_to(T_Tangible_ | T_empty_):
                        result_memtype = memtype

                    elif memtype.is_a_subtype_of_or_equal_to(T_Reference):
                        # Completion Record's [[Value]] can be a Reference, despite the definition of CR?
                        result_memtype = memtype
                    elif memtype in [T_not_returned, ListType(T_code_unit_), T_Top_]:
                        # hm.
                        result_memtype = memtype
                    else:
                        assert 0, memtype

                elif dsbn_name == 'Target':
                    if memtype in [T_continue_, T_break_, T_Abrupt]:
                        result_memtype = T_String | T_empty_
                    elif memtype == T_throw_:
                        result_memtype = T_empty_
                    elif memtype in [T_TBD, T_Top_]:
                        result_memtype = T_String | T_empty_
                    elif memtype in [T_Tangible_, T_empty_]:
                        result_memtype = T_empty_
                    elif memtype in [T_Reference, T_not_returned, ListType(T_code_unit_)]:
                        # hm.
                        result_memtype = T_empty_
                    else:
                        assert 0, memtype

                elif dsbn_name == 'Type':
                    assert 0

                else:
                    assert 0

                result_memtypes.add(result_memtype)

            result_type = union_of_types(result_memtypes)
            return (result_type, env1)

        # Finished with "Completion Records"
        # ----------------------------------

        if lhs_t == T_0:
            if lhs_text == '_starResolution_':
                # ResolveExport _starResolution_
                # The first time through the For loop,
                # _starResolution has type Null,
                # so after "If _starResolution_ is *null*,",
                # in the Else branch it has type T_0.
                # Properly, that should make us not do STA on the Else branch,
                # then we would re-STA the loop-body
                # with a wider type for _starResolution_.
                # But I'm hoping to avoid the need to re-STA loop-bodies.
                lhs_t = T_ResolvedBinding_Record
            elif lhs_text == '_received_':
                # Similar to the above,
                # in Evaluation of YieldExpression
                lhs_t = T_Tangible_ | T_throw_ # ?
            elif lhs_text == '_declResult_':
                # EvaluateBody: See Issue 837
                lhs_t = T_throw_
            else:
                assert 0, expr.source_text()
            add_pass_error(
                expr,
                "`%s` has type T_0, changing to %s" % (lhs_text, lhs_t)
            )
            env2 = env1

        elif lhs_t == T_Property_Descriptor | T_Undefined:
            # CreateGlobalFunctionBinding:
            # If _existingProp_ is *undefined* or _existingProp_.[[Configurable]] is *true*
            lhs_t = T_Property_Descriptor
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t in [
            T_Object | T_Boolean | T_Environment_Record | T_Number | T_String | T_Symbol | T_Undefined,
            T_Object | T_Null,
            T_Object | T_Undefined,
        ]:
            # GetValue. (Fix by replacing T_Reference with ReferenceType(base_type)?)
            lhs_t = T_Object
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t == T_Realm_Record | T_Undefined:
            lhs_t = T_Realm_Record
            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        elif lhs_t in [
            T_TBD,
            T_Top_,
            T_Tangible_,
            T_Normal,
            T_empty_,
            T_Tangible_ | T_empty_,
            T_Tangible_ | T_empty_ | T_Abrupt,
        ]:
            # Have to peek at the dsbn to infer the type of the lhs_var.

            candidate_type_names = []

            for (record_type_name, fields) in sorted(fields_for_record_type_named_.items()):
                if dsbn_name in fields:
                    candidate_type_names.append(record_type_name)

            if dsbn_name in type_of_internal_thing_:
                candidate_type_names.append('Object')
                # But we could sometimes be more specific about the kind of Object:
                # 'PromiseState'    : Promise Instance object
                # 'TypedArrayName'  : Integer Indexed object
                # 'GeneratorState'  : Generator Instance
                # 'OriginalSource'  : RegExp Instance
                # 'GeneratorContext': Generator Instance

            if dsbn_name == 'Realm':
                assert candidate_type_names == ['Module Record', 'PendingJob', 'Script Record', 'Source Text Module Record', 'other Module Record', 'Object']
                if lhs_text == '_scriptRecord_':
                    lhs_t = T_Script_Record
                elif lhs_text == '_module_':
                    lhs_t = T_Source_Text_Module_Record
                else:
                    assert 0
            elif dsbn_name == 'Status':
                assert candidate_type_names == ['Module Record', 'Source Text Module Record', 'other Module Record']
                assert lhs_text == '_module_'
                lhs_t = T_Module_Record
            elif dsbn_name == 'Done':
                assert candidate_type_names == ['iterator_record_', 'Object']
                assert lhs_text == '_iteratorRecord_'
                lhs_t = T_iterator_record_
            else:
                assert len(candidate_type_names) == 1, (dsbn_name, candidate_type_names)
                [type_name] = candidate_type_names
                lhs_t = parse_type_string(type_name)

            env2 = env1.with_expr_type_replaced(lhs_var, lhs_t)

        else:
            env2 = env1

        # --------------------------------------------

        if lhs_t.is_a_subtype_of_or_equal_to(T_Object):
            assert dsbn_name in type_of_internal_thing_, dsbn_name
            it_type = type_of_internal_thing_[dsbn_name]
            # But for some subtypes of Object, we can give a narrower type for the slot
            if lhs_t == T_SharedArrayBuffer_object_ and dsbn_name == 'ArrayBufferData':
                narrower_type = T_Shared_Data_Block
                assert narrower_type.is_a_subtype_of_or_equal_to(it_type)
                assert narrower_type != it_type
                it_type = narrower_type
            return (it_type, env2)

        elif lhs_t.is_a_subtype_of_or_equal_to(T_Abrupt):
            # Handle "Completion Records" specially.
            t = {
                'Value'  : T_Tangible_ | T_empty_,
                'Target' : T_String | T_empty_,
            }[dsbn_name]
            return (t, env2)

        elif lhs_t.is_a_subtype_of_or_equal_to(T_Record):
            if isinstance(lhs_t, NamedType):
                if lhs_t.name == 'Record':
                    add_pass_error(
                        expr,
                        "type of `%s` is only 'Record', so don't know about a `%s` field"
                        % (lhs_text, dsbn_name)
                    )
                    for record_type_name in [
                        'Property Descriptor', # for the almost-Property Descriptor in CompletePropertyDescriptor
                        'iterator_record_',
                        'templateMap_entry_',
                        'methodDef_record_',
                    ]:
                        pd_fields = fields_for_record_type_named_[record_type_name]
                        if dsbn_name in pd_fields:
                            field_type = pd_fields[dsbn_name]
                            break
                    else:
                        assert 0, dsbn_name
                elif lhs_t.name == 'Intrinsics Record':
                    field_type = {
                        '%Array%'             : T_constructor_object_,
                        '%FunctionPrototype%' : T_Object,
                        '%ObjectPrototype%'   : T_Object,
                        '%ThrowTypeError%'    : T_function_object_,
                    }[dsbn_name]
                else:
                    assert lhs_t.name in fields_for_record_type_named_, lhs_t.name
                    fields_info = fields_for_record_type_named_[lhs_t.name]
                    if dsbn_name in fields_info:
                        field_type = fields_info[dsbn_name]
                    else:
                        add_pass_error(
                            expr,
                            "STA can't confirm that `%s` has a `%s` field"
                            % (lhs_text, dsbn_name)
                        )

                        field_type = {
                            (T_Environment_Record, 'NewTarget')        : T_Object | T_Undefined,
                            (T_Module_Record,      'DFSAncestorIndex') : T_Integer_,
                            (T_Module_Record,      'DFSIndex')         : T_Integer_ | T_Undefined,
                            (T_Module_Record,      'EvaluationError')  : T_Abrupt | T_Undefined,
                        }[(lhs_t, dsbn_name)]

                return (field_type, env2)
            elif isinstance(lhs_t, UnionType):
                types_for_field = set()
                for mt in lhs_t.member_types:
                    fields_info = fields_for_record_type_named_[mt.name]
                    assert dsbn_name in fields_info
                    field_type = fields_info[dsbn_name]
                    types_for_field.add(field_type)
                assert len(types_for_field) == 1
                field_type = types_for_field.pop()
                return (field_type, env2)
            else:
                assert 0, (expr.source_text(), lhs_t)

        else:
            assert 0, (expr.source_text(), str(lhs_t))

    # -------------------------------------------------

    elif p == r"{EXPR} : {EX} if {CONDITION}\. Otherwise, it is {EXPR}":
        [exa, cond, exb] = children
        (t_env, f_env) = tc_cond(cond, env0)
        (ta, enva) = tc_expr(exa, t_env)
        (tb, envb) = tc_expr(exb, f_env)
        return (ta | tb, env_or(enva, envb))

    # -------------------------------------------------
    # return T_Number

    elif p in [
        r'{NUM_LITERAL} : \*NaN\*',
        r'{NUM_LITERAL} : \*[+-]&infin;\*',
        r'{NUM_LITERAL} : the \*NaN\* Number value',
        r"{NUM_LITERAL} : 8.64",
        r"{NUM_LITERAL} : 0.5",
    ]:
        [] = children
        return (T_Number, env0)

    elif p == r'{EXPR} : the Number value that corresponds to {VAR}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_IEEE_binary32_ | T_IEEE_binary64_ | T_Integer_)
        return (T_Number, env1)

    elif p in [
        r"{EXPR} : the Number value for \({SUM}\)",
        r"{EXPR} : the Number value for {NAMED_OPERATION_INVOCATION}",
        r"{EX} : the Number value for {PRODUCT}",
    ]:
        [sub] = children
        env0.assert_expr_is_of_type(sub, T_transitioning_from_Number_to_MathReal)
        # doesn't accomplish anything:
        (sub_t, env1) = tc_expr(sub, env0); assert env1 is env0
        result_t = T_Integer_ if sub_t.is_a_subtype_of_or_equal_to(T_MathInteger_) else T_Number
        return (result_t, env0)

    elif p in [
        r"{EXPR} : the number value that is the same sign as {VAR} and whose magnitude is {EX}",
        r"{EXPR} : the Number value that is the same sign as {VAR} and whose magnitude is {EX}",
    ]:
        [var, ex] = children
        env0.assert_expr_is_of_type(var, T_Number)
        env0.assert_expr_is_of_type(ex, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the Element Size specified in {EMU_XREF} for Element Type {VAR}",
        r"{EXPR} : the Element Size value in {EMU_XREF} for {VAR}",
        r"{EXPR} : the Element Size value specified in {EMU_XREF} for Element Type {VAR}",
        r"{EXPR} : the Element Size value specified in {EMU_XREF} for {VAR}",
        r"{EXPR} : the Number value of the Element Size specified in {EMU_XREF} for Element Type {VAR}",
        r"{EXPR} : the Number value of the Element Size value in {EMU_XREF} for {VAR}",
        r"{EXPR} : the Number value of the Element Size value specified in {EMU_XREF} for(?: Element Type)? {VAR}",
    ]:
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : {VAR} `\*` msPerHour `\+` {VAR} `\*` msPerMinute `\+` {VAR} `\*` msPerSecond `\+` {VAR}, performing the arithmetic according to IEEE 754-2008 rules \(that is, as if using the ECMAScript operators `\*` and `\+`\)":
        for var in children:
            env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of forming the value of the \|NumericLiteral\|":
        [] = children
        return (T_Number, env0)

    elif p == r"{EXPR} : the number whose value is {NAMED_OPERATION_INVOCATION} as defined in {EMU_XREF}": # XXX replaced by next
        [noi, emu_xref] = children
        env0.assert_expr_is_of_type(noi, T_transitioning_from_Number_to_MathReal)
        return (T_Number, env0)

    elif p == r"{EXPR} : the Number value represented by {NONTERMINAL} as defined in {EMU_XREF}":
        [nont, emu_xref] = children
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of adding the value {NUM_LITERAL} to {VAR}, using the same rules as for the `\+` operator \(see {EMU_XREF}\)",
        r"{EXPR} : the result of subtracting the value {NUM_LITERAL} from {VAR}, using the same rules as for the `-` operator \(see {EMU_XREF}\)"
    ]:
        [num_lit, var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of negating {VAR}; that is, compute a Number with the same magnitude but opposite sign",
        r"{EXPR} : the result of applying bitwise complement to {VAR}. The result is a signed 32-bit integer",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (T_Number, env0)

    elif p in [
        r'{EXPR} : the result of <emu-xref href="#sec-applying-the-exp-operator" title>Applying the \*\* operator</emu-xref> with {VAR} and {VAR} as specified in {EMU_XREF}',
        r"{EXPR} : the result of applying the addition operation to {VAR} and {VAR}. See the Note below {EMU_XREF}",
        r"{EXPR} : the result of applying the subtraction operation to {VAR} and {VAR}. See the note below {EMU_XREF}",        
    ]:
        [avar, bvar, emu_xref] = children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of applying the {NONTERMINAL} \(.+\) to {VAR} and {VAR} as specified in {EMU_XREF}, {EMU_XREF}, or {EMU_XREF}":
        [nonterminal, avar, bvar, *emu_xrefs] = children
        env0.assert_expr_is_of_type(avar, T_Number)
        env0.assert_expr_is_of_type(bvar, T_Number)
        return (T_Number, env0)

    elif p in [
        r"{EXPR} : the result of left shifting {VAR} by {VAR} bits. The result is a signed 32-bit integer",
        r"{NOI} : a sign-extending right shift of {VAR} by {VAR} bits. The most significant bit is propagated. The result is a signed 32-bit integer",
        r"{NOI} : a zero-filling right shift of {VAR} by {VAR} bits. Vacated bits are filled with zero. The result is an unsigned 32-bit integer",
        r"{EXPR} : the result of applying the bitwise operator @ to {VAR} and {VAR}. The result is a signed 32-bit integer",
    ]:
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, T_Integer_)
        env0.assert_expr_is_of_type(bvar, T_Integer_)
        return (T_Number, env0)

    # --------------------------------------------------------
    # return T_MathInteger_

    elif p in [
        u"{EX} : \\d+<sub>\u211d</sub>",
        u"{FACTOR} : \\d+<sub>\u211d</sub>",
        u"{BASE} : 10<sub>\u211d</sub>",
        u"{FACTOR} : 0x[0-9A-F]+<sub>\u211d</sub>",
    ]:
        [] = children
        return (T_MathInteger_, env0)

    elif p == u"{FACTOR} : \u211d\\({VAR}\\)":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_MathInteger_, env0)

    elif p == u"{PRODUCT} : -<sub>\u211d</sub>{VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_MathInteger_)
        return (T_MathInteger_, env0)

    elif p in [
        r"{EXPR} : the mathematical integer number of code points in {PROD_REF}",
        r"{EX} : the mathematical integer number of code points in {PROD_REF}",
        r"{EX} : the mathematical value of the number of code points in {PROD_REF}",
    ]:
        [prod_ref] = children
        return (T_MathInteger_, env0)

    # --------------------------------------------------------
    # return T_MathReal_

    elif p in [
        u"{PRODUCT} : {FACTOR} &times;<sub>\u211d</sub> {FACTOR}",
        u"{SUM} : {VAR}-<sub>\u211d</sub>{VAR}",
        u"{SUM} : {TERM} -<sub>\u211d</sub> {TERM}",
    ]:
        [left, right] = children
        env0.assert_expr_is_of_type(left, T_MathReal_)
        env0.assert_expr_is_of_type(right, T_MathReal_)
        return (T_MathReal_, env0)

    elif p in [
        r'{EXPR} : the negative of {EX}',
    ]:
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_transitioning_from_Number_to_MathReal)
        return (T_transitioning_from_Number_to_MathReal, env0)

    # --------------------------------------------------------
    # return T_Integer_: The size of some collection:

    elif p in [
        r"{NUM_COMPARAND} : the length of {VAR}",
        r"{EXPR} : the length of {VAR}",
        r"{EXPR} : the number of code units in {VAR}",
        r"{TERM} : the number of code units in {VAR}",
        r"{EXPR} : the number of code unit elements in {VAR}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the number of characters contained in {VAR}",
        r"{EXPR} : the number of elements in the List {VAR}",
        r"{EX} : the number of elements in {VAR}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_List)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the number of elements in {VAR}'s _captures_ List":
        [var] = children
        env0.assert_expr_is_of_type(var, T_State)
        return (T_Integer_, env0)

    elif p in [
        r'{EX} : the number of code points in {PROD_REF}',
        r"{EXPR} : the number of code points in {PROD_REF}",
    ]:
        [prod_ref] = children
        env0.assert_expr_is_of_type(prod_ref, T_Parse_Node)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the number of bytes in {VAR}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Data_Block | T_Shared_Data_Block)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the array size":
        # only once, in Encode()
        [] = children
        return (T_Integer_, env0)

    # ----
    # return T_Integer_: arithmetic:

    elif p == r"{EXPR} : the result of masking out all but the least significant 5 bits of {VAR}, that is, compute {VAR} &amp; 0x1F":
        [var, var2] = children
        assert var.children == var2.children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the numeric value 1",
        r"{EX} : [0-9]+",
        r"{FACTOR} : 0x[0-9A-F]+",
        r"{FACTOR} : [0-9]+",
        r"{NUM_COMPARAND} : -6",
        r"{NUM_LITERAL} : 0x[0-9A-F]+",
        r"{NUM_LITERAL} : [0-9]+",
        r"{NUM_LITERAL} : \*[+-]0\*",
        r"{NUM_LITERAL} : zero",
        r"{BASE} : 10",
    ]:
        [] = children
        return (T_Integer_, env0)

    elif p == r"{NUM_LITERAL} : (2|10)<sup>[0-9]+</sup>":
        [_] = children
        return (T_Integer_, env0)

#    elif p == r'{FACTOR} : 10<sup>{EX}</sup>':
#        [ex] = children
#        (t, env1) = tc_expr(ex, env0); assert env1 is env0
#        if t == T_TBD:
#            pass
#        else:
#            assert t.is_a_subtype_of_or_equal_to(T_Integer_)
#        return (T_Integer_, env0) # unless EX is negative!

    elif p in [
        r"{FACTOR} : {BASE}<sup>{NUM_EXPR}</sup>",
        r"{FACTOR} : {BASE}<sup>{VAR}</sup>",
        r"{FACTOR} : {BASE}<sup>{EX}</sup>",
    ]:
        [base, exponent] = children
        # env0.assert_expr_is_of_type(base, T_Integer_)
        # env0.assert_expr_is_of_type(exponent, T_Integer_)
        (base_t, env1) = tc_expr(base, env0); assert env1 is env0
        assert base_t.is_a_subtype_of_or_equal_to(T_Integer_ | T_MathInteger_)
        env0.assert_expr_is_of_type(exponent, T_MathReal_ if base_t == T_MathInteger_ else T_Number)
        return (base_t, env0) # unless exponent is negative


    elif p == r"{PRODUCT} : {FACTOR} modulo {FACTOR}":
        [factor1, factor2] = children
        env0.assert_expr_is_of_type(factor1, T_Number) # Should be Integer, but _m_ modulo 12
        env0.assert_expr_is_of_type(factor2, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{EX} : the remainder of dividing {EX} by {EX}":
        [aex, bex] = children
        env0.assert_expr_is_of_type(aex, T_Integer_)
        env0.assert_expr_is_of_type(bex, T_Integer_)
        return (T_Integer_, env0)

    elif  p == r"{BIT_OP} : {FACTOR} (&amp;|&gt;&gt;|&lt;&lt;) {FACTOR}":
        [numa, op, numb] = children
        env0.assert_expr_is_of_type(numa, T_Integer_)
        env0.assert_expr_is_of_type(numb, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{SUM} : {TERM} plus {TERM} plus {TERM} plus {TERM}":
        for term in children:
            env0.assert_expr_is_of_type(term, T_transitioning_from_Number_to_MathReal)
        return (T_MathReal_, env0)

    elif p == r"{EXPR} : the mathematical value that is the same sign as {VAR} and whose magnitude is floor\(abs\({VAR}\)\)":
        [var1, var2] = children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_Number)
        return (T_Integer_, env0)

    # ----

    elif p in [
        r"{NUM_COMPARAND} : the numeric value of {VAR}",
        r"{EX} : the numeric value of {EX}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the integer that is {EXPR}":
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (T_Integer_, env0)

    # ----

    elif p in [
        r'{EXPR} : the character value of character {VAR}',
        r"{EXPR} : {VAR}'s character value",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the code point value of {CP_LITERAL}",
        r"{EXPR} : the code point value of {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the code point value of {VAR}",
        r"{EXPR} : {VAR}'s code point value",
    ]:
        [x] = children
        env1 = env0.ensure_expr_is_of_type(x, T_code_point_)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the code point value according to {EMU_XREF}":
        return (T_Integer_, env0)

    elif p == r'{EXPR} : the byte elements of {VAR} concatenated and interpreted as a bit string encoding of an unsigned little-endian binary number':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the byte elements of {VAR} concatenated and interpreted as a bit string encoding of a binary little-endian 2's complement number of bit length {PRODUCT}":
        [var, product] = children
        env1 = env0.ensure_expr_is_of_type(product, T_Integer_ | T_Number); assert env1 is env0
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_Integer_, env1)

    elif p in [
        r"{EX} : {VAR}'s _endIndex_",
        r"{EX} : {VAR}'s _endIndex_ value",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the value at index {VAR} within {VAR}":
        # only once, in Encode()
        [index_var, list_var] = children
        env0.assert_expr_is_of_type(list_var, ListType(T_Integer_))
        env0.assert_expr_is_of_type(index_var, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the index into {VAR} of the character that was obtained from element {VAR} of {VAR}":
        [list_var, index_var, str_var] = children
        env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(index_var, T_Integer_)
        env0.assert_expr_is_of_type(str_var, T_String) # todo: element of String
        return (T_Integer_, env0)

    elif p in [
        r"{EXPR} : the number of left-capturing parentheses in the entire regular expression that occur to the left of {PROD_REF}. This is the total number of {EMU_GRAMMAR} Parse Nodes prior to or enclosing {PROD_REF}",
        r"{EXPR} : the number of left-capturing parentheses in {PROD_REF}. This is the total number of {EMU_GRAMMAR} Parse Nodes enclosed by {PROD_REF}",
    ]:
        [prod_ref, emu_grammar, prod_ref2] = children
        assert same_source_text(prod_ref, prod_ref2)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the 8-bit value represented by the two hexadecimal digits at index {EX} and {EX}":
        [posa, posb] = children
        env0.assert_expr_is_of_type(posa, T_Integer_)
        env0.assert_expr_is_of_type(posb, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the value obtained by applying the UTF-8 transformation to {VAR}, that is, from a List of octets into a 21-bit value":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_Integer_))
        return (T_Integer_, env0)

    # -------------------------------------------------
    # return Number or Integer_ (arithmetic)

    elif p in [
        r'{SUM} : {TERM} [+-] {TERM}',
        r"{SUM} : {SUM} [+-] {TERM}",
    ]:
        t_ = [None, None]
        for (i,term) in enumerate(children):
            (t_[i], env1) = tc_expr(term, env0); assert env1 is env0
            if t_[i].is_a_subtype_of_or_equal_to(T_numeric_):
                pass
            else:
                # Only happens on non-final passes:
                add_pass_error(
                    expr,
                    "Expected numeric, got %s" % str(t_[i])
                )

        if t_[0] == T_TBD and t_[1] == T_TBD:
            assert 0
            result_type = T_Integer_
        elif t_[0] == T_TBD:
            # non-final only
            add_pass_error(expr, "t0 is TBD")
            result_type = t_[1]
        elif t_[1] == T_TBD:
            assert 0
            result_type = t_[0]

        elif t_[0] == t_[1]:
            # usually Integer_, but twice Number:
            # `_t_ + LocalTZA(_t_, *true*)`
            # `_t_ - LocalTZA(_t_, *false*)`
            # Although in practice, LocalTZA probably always returns an integer
            result_type = t_[0]

        elif t_[1].is_a_subtype_of_or_equal_to(t_[0]):
            # 4 times
            result_type = t_[0]
        elif t_[0].is_a_subtype_of_or_equal_to(t_[1]):
            # 3 times
            result_type = t_[1]

        elif t_[0] == T_code_unit_ and t_[1] == T_Integer_:
            # 2 times, both in UTF16Decode:
            # `_lead_ - 0xD800`
            # `_trail_ - 0xDC00`
            result_type = t_[1]

        else:
            assert 0
        return (result_type, env1)

    # merge the blocks above + below

    elif p in [
        r'{PRODUCT} : {FACTOR} (&times;) {FACTOR}',
        r'{PRODUCT} : {FACTOR} (&divide;|/) {FACTOR}',
        r'{PRODUCT} : {FACTOR} times {FACTOR}',
        r'{PRODUCT} : {FACTOR} &times; {FACTOR}',
        r'{SUM} : {TERM} plus {TERM}',
        r'{SUM} : {TERM} - {TERM}',
    ]:
        if '(' in p:
            [a, _, b] = children
        else:
            [a, b] = children
        (a_type, enva) = tc_expr(a, env0); assert enva is env0
        (b_type, envb) = tc_expr(b, env0); assert envb is env0
        if a_type == T_TBD:
            # Happens during non-final passes.
            assert b_type != T_TBD
            assert b_type.is_a_subtype_of_or_equal_to(T_numeric_)
            a_type = b_type
            # env1 = env0.with_expr_type_replaced(a, a_type)
            env1 = env0
            add_pass_error(
                expr,
                "left operand type is TBD"
            )
        elif b_type == T_TBD:
            # Happens during non-final passes.
            assert a_type != T_TBD
            assert a_type.is_a_subtype_of_or_equal_to(T_numeric_)
            b_type = a_type
            env1 = env0
            add_pass_error(
                expr,
                "right operand type is TBD"
            )
        elif a_type == T_Integer_ | T_not_set and b_type == T_Integer_:
            add_pass_error(
                expr,
                "left operand might be not_set?"
            )
            a_type = T_Integer_
            env1 = env0
        else:
            assert a_type.is_a_subtype_of_or_equal_to(T_numeric_)
            assert b_type.is_a_subtype_of_or_equal_to(T_numeric_)
            env1 = env0

        if a_type == T_Integer_ and b_type == T_Integer_:
            return (T_Integer_, env1)

        elif a_type == T_MathReal_ and b_type == T_MathReal_:
            return (T_MathReal_, env1)

        elif a_type == T_MathReal_ and b_type == T_MathInteger_:
            return (T_MathReal_, env1)

        elif a_type == T_MathInteger_ and b_type == T_MathReal_:
            return (T_MathReal_, env1)

        elif a_type == T_MathInteger_ and b_type == T_MathInteger_:
            return (T_MathInteger_, env1)

        elif a_type == T_Number and b_type == T_Number:
            return (T_Number, env1)

        elif a_type == T_Number and b_type == T_Integer_:
            # Only 2 occurrences:
            # `_m_ / 12` in MakeDay
            # `8.64 &times; 10<sup>15</sup>` in TimeClip
            return (T_Number, env1)

        elif a_type == T_Integer_ and b_type == T_Number:
            return (T_Number, env1)

#        elif a_type == T_Integer_ | T_Number and b_type == T_Number:
#            assert 0
#            add_pass_error( expr, "Int|Num op Number -> Int|Num")
#            return (a_type, env1)
#
#        elif a_type == T_Number and b_type == T_numeric_:
#            assert 0
#            add_pass_error( expr, "Number op numeric -> Number")
#            return (T_Number, env1)
#        elif a_type == T_numeric_ and b_type == T_Number:
#            assert 0
#            add_pass_error( expr, "numeric or Number -> Number")
#            return (T_Number, env1)

        else:
            assert 0, (a_type, b_type)

    elif p in [
        r'{PRODUCT} : -{VAR}',
        r"{NUM_EXPR} : -{FACTOR}",
    ]:
        [ex] = children
        # almost: env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        # but's a vaguer type-requirement, and we need the actual type out.

        (t, env1) = tc_expr(ex, env0); assert env1 is env0
        if t == T_TBD:
            t = T_Integer_ # maybe
            env2 = env1.with_expr_type_replaced(ex, t)
        else:
            assert t.is_a_subtype_of_or_equal_to(T_Integer_), t
            env2 = env1
        return (t, env2)

    # -------------------------
    # return T_String

    elif p in [
        r'{LITERAL} : {STR_LITERAL}',
        r'{STR_LITERAL} : {CU_LITERAL}',
        r'{STR_LITERAL} : `"[^`"]*"`',
    ]:
        return (T_String, env0)

    elif expr.prod.lhs_s == '{STR_LITERAL}':
        return (T_String, env0)

    elif p in [
        r"{EX} : the String {VAR}",
        r"{EXPR} : the String {STR_LITERAL}",
        r"{EXPR} : the String value {SETTABLE}",
    ]:
        [ex] = children
        env0.ensure_expr_is_of_type(ex, T_String)
        return (T_String, env0)

    elif p == r"{MULTILINE_EXPR} : the String value corresponding to the value of {VAR} as follows:{I_TABLE}":
        [old_var, table] = children
        env1 = env0.ensure_expr_is_of_type(old_var, T_code_unit_)
        return (T_String, env0)

    elif p == r'{EXPR} : the same result produced as if by performing the algorithm for `String.prototype.toUpperCase` using {VAR} as the \*this\* value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

    elif p == r'{EX} : the referenced name component of {VAR}':
        [v] = children
        env0.assert_expr_is_of_type(v, T_Reference)
        return (T_String | T_Symbol, env0)

    elif p == r'{EXPR} : the string result of converting {EX} to a String of four lowercase hexadecimal digits':
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String value consisting solely of {CU_LITERAL}",
        r"{EXPR} : the String value containing only the code unit {VAR}",
        r"{EXPR} : the String value consisting of the single code unit {VAR}",
    ]:
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_unit_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value consisting of the sequence of code units corresponding to {PROD_REF}. In determining the sequence any occurrences of {TERMINAL} {NONTERMINAL} are first replaced with the code point represented by the {NONTERMINAL} and then the code points of the entire {PROD_REF} are converted to code units by UTF16Encoding each code point":
        return (T_String, env0)

    elif p == r"{EXPR} : the String value that is the same as {VAR} except that each occurrence of {CU_LITERAL} in {VAR} has been replaced with the six code unit sequence {STR_LITERAL}":
        [var, lita, var2, litb] = children
        assert var.children == var2.children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env1)

    elif p == r"{MULTILINE_EXPR} : the string-concatenation of:{I_BULLETS}":
        [bullets] = children
        # Should check the bullets
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the string-concatenation of {EX} and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
        r"{EXPR} : the string-concatenation of {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, {EX}, and {EX}",
    ]:
        env1 = env0
        for ex in children:
            env1 = env1.ensure_expr_is_of_type(ex, T_String | T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : the string-concatenation of {EX}, {EX}, and {EX}\. If {VAR} is 0, the first element of the concatenation will be the empty String":
        p_var = children[3]
        env0.assert_expr_is_of_type(p_var, T_Integer_)
        env1 = env0
        for ex in children[0:3]:
            env1 = env1.ensure_expr_is_of_type(ex, T_String | T_code_unit_ | ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r'{EX} : the two uppercase hexadecimal digits encoding {VAR}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p in [
        r"{EX} : the code unit of the single digit of {VAR}",
        r"{EX} : the code units of the decimal representation of the integer abs\({VAR}-1\) \(with no leading zeroes\)",
        r"{EX} : the code units of the most significant digit of the decimal representation of {VAR}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p in [
        r"{EX} : the code units of the most significant {VAR} digits of the decimal representation of {VAR}",
        r"{EX} : the code units of the remaining {NUM_EXPR} digits of the decimal representation of {VAR}",
        r"{EX} : the code units of the {VAR} digits of the decimal representation of {VAR} \(in order, with no leading zeroes\)",
        r"{EX} : the code units of the {VAR} digits of the decimal representation of {VAR}",

    ]:
        [nd_var, num_var] = children
        env0.assert_expr_is_of_type(nd_var, T_Integer_)
        env0.assert_expr_is_of_type(num_var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EX} : {EX} occurrences of {CU_LITERAL}":
        [ex, cu_lit] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        env0.assert_expr_is_of_type(cu_lit, T_code_unit_)
        return (ListType(T_code_unit_), env1)

    elif p == r"{EX} : {CU_LITERAL} or {CU_LITERAL} according to whether {VAR}-1 is positive or negative":
        [lit1, lit2, var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the substring of {VAR} from index {VAR} to index {VAR} inclusive",
        r"{EXPR} : the matched substring \(i.e. the portion of {VAR} between offset {VAR} inclusive and offset {VAR} exclusive\)",
        r"{EX} : the substring of {VAR} consisting of the code units from {VAR} \(inclusive\) up to {VAR} \(exclusive\)",
    ]:
        [s_var, start_var, end_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(start_var, T_Integer_)
        env0.assert_expr_is_of_type(end_var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EX} : the substring of {VAR} consisting of the code units from {VAR} \(inclusive\) up through the final code unit of {VAR} \(inclusive\)":
        [s_var, start_var, s_var2] = children
        assert same_source_text(s_var, s_var2)
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(start_var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value of {DOTTING}":
        # todo: sounds like "String value" is an operation applied to the result of DOTTING
        [dotting] = children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value of the Element Type value in {EMU_XREF} for {VAR}":
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the String value of length 1, containing one code unit from {VAR}, namely the code unit at index {VAR}",
        r"{EXPR} : the String value of length 1, containing one code unit from {VAR}, specifically the code unit at index {VAR}",
    ]:
        [s_var, i_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(i_var, T_Integer_)
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the sole element of {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the sole element of {VAR}",
    ]:
        [noi] = children
        env0.assert_expr_is_of_type(noi, ListType(T_String)) # not justified
        return (T_String, env0)

    elif p == r"{EXPR} : the string that is the only element of {NAMED_OPERATION_INVOCATION}":
        [noi] = children
        env0.assert_expr_is_of_type(noi, ListType(T_String))
        return (T_String, env0)

    elif p == r"{EXPR} : {VAR}'s {DSBN} value":
        [var, dsbn] = children
        env0.assert_expr_is_of_type(var, T_Symbol)
        assert dsbn.children == ['Description']
        return (T_String | T_Undefined, env0)

    elif p in [
        r"{EXPR} : the String value whose code units are {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the String value whose elements are {NAMED_OPERATION_INVOCATION}",
    ]:
        [noi] = children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_code_unit_))
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String value consisting of the code units of {VAR}",
        r"{EXPR} : the String value consisting of {EX}",
        r"{EXPR} : the String value consisting of {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the String value whose code units are, in order, the elements in {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the String value whose elements are, in order, the elements in {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : the string consisting of the code units of {VAR}",
    ]:
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose code units are the elements of {NAMED_OPERATION_INVOCATION} as defined in {EMU_XREF}":
        [noi, emu_xref] = children    
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_code_unit_))
        return (T_String, env1)

    elif p in [
        r"{EXPR} : the String value whose code units are the elements of {VAR} followed by the elements of {VAR}",
        r"{EXPR} : the String value whose code units are the elements of {VAR} followed by the elements of {VAR} followed by the elements of {VAR}",
    ]:
        for var in children:
            env0 = env0.ensure_expr_is_of_type(var, T_String | ListType(T_code_unit_))
        return (T_String, env0)

    elif p == r"{EXPR} : a String according to {EMU_XREF}":
        [emu_xref] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the String value of the property name":
        # property of the Global Object
        # todo: make that explicit
        [] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the String value formed by concatenating all the element Strings of {VAR} with each adjacent pair of Strings separated with {CU_LITERAL}. A comma is not inserted either before the first String or after the last String":
        [var, str_literal] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value formed by concatenating all the element Strings of {VAR} with each adjacent pair of Strings separated with {VAR}. The {VAR} String is not inserted either before the first String or after the last String":
        [var, sep_var, sep_var2] = children
        assert sep_var.children == sep_var2.children
        env0.assert_expr_is_of_type(sep_var, T_String)
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_String))
        return (T_String, env1)

    elif p == r"{EXPR} : the Name of the entry in {EMU_XREF} with the Number {NAMED_OPERATION_INVOCATION}":
        [emu_xref, noi] = children
        env0.assert_expr_is_of_type(noi, T_Number)
        return (T_String, env0)

    elif p in [
        r"{EXPR} : the String representation of {EX}, formatted as a decimal number of at least four digits, padded to the left with zeroes if necessary",
        r"{EXPR} : the String representation of {EX}, formatted as a number of at least four digits, padded to the left with zeroes if necessary",
        r"{EXPR} : the String representation of {EX}, formatted as a two-digit decimal number, padded to the left with a zero if necessary",
    ]:
        [ex] = children
        env0.assert_expr_is_of_type(ex, T_Number)
        return (T_String, env0)

    elif p == r"{EXPR} : an implementation-defined string that is either {EX} or {EXPR}":
        [exa, exb] = children
        env0.assert_expr_is_of_type(exa, T_String)
        env0.assert_expr_is_of_type(exb, T_String)
        return (T_String, env0)

    elif p == r"{EX} : an implementation-dependent timezone name":
        [] = children
        return (T_String, env0)

    elif p == r"{EX} : the Escape Sequence for {VAR} as specified in {EMU_XREF}":
        [var, emu_xref] = children
        assert emu_xref.source_text() == '<emu-xref href="#table-json-single-character-escapes"></emu-xref>'
        return (T_String, env0)

    elif p == r"{EXPR} : the String value derived from {VAR} by copying code unit elements from {VAR} to {VAR} while performing replacements as specified in {EMU_XREF}. These `\$` replacements are done left-to-right, and, once such a replacement is performed, the new replacement text is not subject to further replacements":
        [va, vb, vc, _] = children
        assert same_source_text(va, vb)
        env0.assert_expr_is_of_type(vb, T_String)
        # env0.assert_expr_is_of_type(vc, T_String) repeats the var-being-defined
        return (T_String, env0)

    # ----------------------------------------------------------
    # return T_character_

    elif p == r"{EXPR} : the character {CP_LITERAL}":
        [cp_literal] = children
        return (T_character_, env0)

    elif p == r"{EXPR} : the character matched by {PROD_REF}":
        [prod_ref] = children
        return (T_character_, env0)

    elif p == r"{EXPR} : the character whose character value is {VAR}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Integer_)
        return (T_character_, env1)

    elif p == r"{EXPR} : the character whose code is {EXPR}":
        # todo: I think "code" means "code unit" and/or "value"?
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, ListType(T_code_unit_) | T_Integer_)
        return (T_character_, env1)

    elif p == r'{EXPR} : the result of applying that mapping to {VAR}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_character_)
        return (T_character_, env1)

    elif p == r'{EXPR} : the one character in CharSet {VAR}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_CharSet)
        return (T_character_, env1)

    elif p == r"{EXPR} : the character {SETTABLE}":
        [settable] = children
        env1 = env0.ensure_expr_is_of_type(settable, T_character_)
        return (T_character_, env1)

    elif p == r"{EXPR} : the character according to {EMU_XREF}":
        [emu_xref] = children
        return (T_character_, env0)

    # ----------------------------------------------------------
    # return T_code_unit_

    elif expr.prod.lhs_s == '{CU_LITERAL}':
        return (T_code_unit_, env0)

    elif p == r"{EXPR} : {VAR}'s single code unit element": # todo: element of String
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

    elif p == r'{EX} : the first code unit of {VAR}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (T_code_unit_, env1)

    elif p == r"{EXPR} : the code unit whose value is determined by the {NONTERMINAL} according to {EMU_XREF}":
        [nonterminal, emu_xref] = children
        return (T_code_unit_, env0)

    elif p in [
        r"{EXPR} : the code unit whose value is {SUM}",
        r"{EXPR} : the code unit whose value is {EXPR}",
    ]:
        [ex] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_ | T_MathInteger_)
        return (T_code_unit_, env0)

    elif p == r"{EX} : the code unit {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_code_unit_, env0)

    elif p == r"{EX} : the code unit that is {NAMED_OPERATION_INVOCATION}":
        [noi] = children
        env0.assert_expr_is_of_type(noi, ListType(T_code_unit_))
        return (T_code_unit_, env0)

    # ----

    elif p == r"{EX} : the code unit at index {EX} within {EX}":
        [index_ex, str_ex] = children
        env0.assert_expr_is_of_type(str_ex, T_String)
        env1 = env0.ensure_expr_is_of_type(index_ex, T_Integer_)
        return (T_code_unit_, env1)

    # ----------------------------------------------------------
    # return T_code_point_

    elif p == r"{EXPR} : the code point {VAR}":
        # This means "the code point whose numeric value is {VAR}"
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_code_point_, env0)

    elif p == r"{EXPR} : the code point with the same numeric value as code unit {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (T_code_point_, env0)

    elif p in [
        r"{CP_LITERAL} : U\+0000 \(NULL\)",
        r"{CP_LITERAL} : U\+0008 \(BACKSPACE\)",
        r"{CP_LITERAL} : U\+002D \(HYPHEN-MINUS\)",
        r"{CP_LITERAL} : U\+005C \(REVERSE SOLIDUS\)",
        r"{CP_LITERAL} : `-` U\+002D \(HYPHEN-MINUS\)",
    ]:
        return (T_code_point_, env0)

    elif p == r"{EXPR} : the code point matched by {NONTERMINAL}":
        [nont] = children
        return (T_code_point_, env0)
            

    # ----------------------------------------------------------
    # return T_Unicode_code_points_

    elif p == r'{EXPR} : the source text that was recognized as {PROD_REF}':
        [nonterminal] = children
        # XXX Should check whether nonterminal makes sense
        # with respect to the emu-grammar accompanying this alg/expr.
        return (T_Unicode_code_points_, env0)

    elif p == r"{EXPR} : a List whose elements are the code points resulting from applying UTF-16 decoding to {VAR}'s sequence of elements":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_point_), env0)

    # ----------------------------------------------------------
    # return ListType

    # --------------------
    # ListType(T_Integer_)

    elif (
        p.startswith(r'{EXPR} : a List containing the 4 bytes that are the result of converting {VAR} to IEEE 754-2008 binary32 format')
        or
        p.startswith(r'{EXPR} : a List containing the 8 bytes that are the IEEE 754-2008 binary64 format encoding of {VAR}.')
    ):
        var = children[0]
        env0.assert_expr_is_of_type(var, T_Number)
        return (ListType(T_Integer_), env0)

    elif p in [
        r'{EXPR} : a List containing the {VAR}-byte binary encoding of {VAR}. If {VAR} is {LITERAL}, the bytes are ordered in big endian order. Otherwise, the bytes are ordered in little endian order',
        r"{EXPR} : a List containing the {VAR}-byte binary 2's complement encoding of {VAR}. If {VAR} is {LITERAL}, the bytes are ordered in big endian order. Otherwise, the bytes are ordered in little endian order",
    ]:
        [n_var, v_var, i_var, literal] = children
        env0.assert_expr_is_of_type(n_var, T_Number)
        env0.assert_expr_is_of_type(v_var, T_Integer_)
        env0.assert_expr_is_of_type(i_var, T_Boolean)
        env0.assert_expr_is_of_type(literal, T_Boolean)
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : a List of length 1 that contains a nondeterministically chosen byte value":
        [] = children
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : a List of length {VAR} of nondeterministically chosen byte values":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : a List of {VAR} containing, in order, the {VAR} sequence of bytes starting with {EX}":
        # todo: fix odd syntax in spec.
        [var1, var2, ex] = children
        assert var1.children == var2.children
        env0.assert_expr_is_of_type(var1, T_Integer_)
        env0.assert_expr_is_of_type(ex, T_Integer_)
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : a List of 8-bit integers of size {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the List of octets resulting by applying the UTF-8 transformation to {VAR}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_code_point_)
        return (ListType(T_Integer_), env1)

    # ----------------------
    # ListType(T_code_unit_)

    elif p == r"{EXPR} : the empty code unit sequence":
        [] = children
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : the sequence consisting of {CU_LITERAL}":
        [lit] = children
        return (ListType(T_code_unit_), env0)

    elif p in [
        r"{EX} : a sequence of up to two code units that is {NAMED_OPERATION_INVOCATION}",
        r"{EX} : the code units of {NAMED_OPERATION_INVOCATION}",
        r"{EX} : the code units of {NAMED_OPERATION_INVOCATION} in order",
        r"{EX} : the code units of {VAR}",
    ]:
        [noi] = children
        env1 = env0.ensure_expr_is_of_type(noi, ListType(T_code_unit_))
        return (ListType(T_code_unit_), env1)

    elif p in [
        r"{EXPR} : {EX} followed by {EX}",
        r"{EXPR} : the sequence consisting of {EX} followed by {EX}",
        r"{EXPR} : the sequence consisting of {EX} followed by {EX} followed by {EX}",
        r"{EXPR} : the sequence consisting of {EX} followed by {EX} followed by {EX} followed by {EX}",
    ]:
        env1 = env0
        for ex in children:
            env1 = env1.ensure_expr_is_of_type(ex, T_code_unit_ | ListType(T_code_unit_))
        return (ListType(T_code_unit_), env1)

    elif p in [
        r"{EXPR} : a sequence consisting of the code units of {NAMED_OPERATION_INVOCATION} followed by the code units of {NAMED_OPERATION_INVOCATION}",
    ]:
        [ex1, ex2] = children
        env1 = (
            env0.ensure_expr_is_of_type(ex1, ListType(T_code_unit_))
                .ensure_expr_is_of_type(ex2, ListType(T_code_unit_))
        )
        return (ListType(T_code_unit_), env1)

    elif p == r"{EXPR} : a List whose elements are the code unit elements of {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

    elif p in [
        r"{EXPR} : the sequence of code units consisting of the code units of {VAR} followed by the elements of {VAR}",
        r"{EXPR} : the sequence of code units consisting of the elements of {VAR} followed by the code units of {VAR} followed by the elements of {VAR}",
    ]:
        for var in children:
            env0.ensure_expr_is_of_type(var, T_String | ListType(T_code_unit_))
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : the code unit sequence consisting of {VAR} followed by {VAR}":
        [var1, var2] = children
        env0.assert_expr_is_of_type(var1, T_Integer_)
        env0.assert_expr_is_of_type(var2, T_Integer_)
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : the UTF16Encoding of the code point value of {NONTERMINAL}":
        [nonterminal] = children
        # Should look up the return type of UTF16Encoding
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : the UTF16Encoding of {NAMED_OPERATION_INVOCATION}":
        # todo: should be "the UTF16Encoding of the code point whose value is ..."
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_transitioning_from_Number_to_MathReal)
        return (ListType(T_code_unit_), env0)

    elif p == r"{NOI} : the UTF16Encoding of each code point of {NAMED_OPERATION_INVOCATION}":
        [noi] = children
        env0.assert_expr_is_of_type(noi, T_Unicode_code_points_)
        return (ListType(T_code_unit_), env0)

    elif p == r"{NOI} : the UTF16Encoding of the code points of {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_code_point_))
        return (ListType(T_code_unit_), env0)

    elif p == r"{EXPR} : a List consisting of the sequence of code units that are the elements of {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_unit_), env0)

    # ---------------
    # ListType(T_String)

    elif p == r"{EXPR} : a List containing {VAR} followed by the elements, in order, of {VAR}":
        # once, in TemplateStrings
        [item_var, list_var] = children
        env1 = env0.ensure_expr_is_of_type(item_var, ListType(T_code_unit_))
        env2 = env1.ensure_expr_is_of_type(list_var, ListType(T_String))
        return (ListType(T_String), env2)

    # ---------------
    # ListType(other)

    elif p == r'{EXPR} : a new empty List':
        [] = children
        return (T_List, env0) # (ListType(T_0), env0)

    elif p in [
        r"{EXPR} : a List containing only {VAR}",
        r"{EXPR} : a List containing the one element which is {VAR}",
        r"{EXPR} : a List containing the single element, {VAR}",
        r"{EXPR} : a List containing {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : a List containing {PROD_REF}",
        r"{EXPR} : a List whose sole item is {VAR}",
        r"{EXPR} : a new List containing {EXPR}",
    ]:
        [element_expr] = children
        (element_type, env1) = tc_expr(element_expr, env0); assert env1.equals(env0)
        return (ListType(element_type), env0)

    elif p in [
        r"{EXPR} : the result of appending to {VAR} the elements of {NAMED_OPERATION_INVOCATION}",
        r"{EXPR} : a copy of {VAR} with all the elements of {VAR} appended",
    ]:
        [var, noi] = children
        (t1, env1) = tc_expr(var, env0); assert env1 is env0
        (t2, env2) = tc_expr(noi, env0); assert env2 is env0
        if t1 == T_TBD and t2 == T_TBD:
            list_type = T_List
        elif t1 == T_List and t2 == T_TBD:
            list_type = t1
        elif isinstance(t1, ListType) and t1 == t2:
            list_type = t1
        else:
            assert 0
            # assert t1.element_type == t2.element_type
        return (list_type, env0)

    elif p in [
        r"{EXPR} : a copy of {VAR} with {VAR} appended",
        r"{EXPR} : a List containing the elements, in order, of {VAR} followed by {VAR}",
    ]:
        [list_var, item_var] = children
        env1 = env0.ensure_A_can_be_element_of_list_B(item_var, list_var)
        list_type = env1.lookup(list_var)
        return (list_type, env1)

    elif p == r"{EXPR} : a List whose first element is {VAR}, whose second elements is {VAR}, and whose subsequent elements are the elements of {VAR}, in order. {VAR} may contain no elements":
        [e1_var, e2_var, rest_var, _] = children
        (t1, env1) = tc_expr(e1_var, env0); assert env1 is env0
        (t2, env2) = tc_expr(e2_var, env0); assert env2 is env0
        (rest_t, rest_env) = tc_expr(rest_var, env0); assert rest_env is env0
        if t1 == T_TBD and t2 == T_TBD and rest_t == T_List:
            # can't really do much
            pass
        elif t1 == T_TBD and t2 == T_Tangible_:
            pass
        elif t1 == T_Object and t2 == T_Tangible_ and rest_t == ListType(T_Tangible_):
            pass
        else:
            assert t1 == t2
            assert isinstance(rest_t, ListType)
            assert t1 == rest_t.element_type
        return (rest_t, rest_env)

    elif p == r'{EXPR} : a new List containing the same values as the list {VAR} where the values are ordered as if an Array of the same values had been sorted using `Array.prototype.sort` using \*undefined\* as _comparefn_':
        [var] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_List)
        return (t, env0)

    elif p == r"{EXPR} : the List of {NONTERMINAL} items in {PROD_REF}, in source text order":
        [nont, prod_ref] = children
        return (ListType(T_Parse_Node), env0)

    elif p == r"{EXPR} : a new list containing the same values as the list {VAR} in the same order followed by the same values as the list {VAR} in the same order":
        [avar, bvar] = children
        env0.assert_expr_is_of_type(avar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(bvar, ListType(T_Tangible_))
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : {VAR}<sup>th</sup> element of {VAR}'s _captures_ List":
        [n_var, state_var] = children
        env0.assert_expr_is_of_type(n_var, T_Integer_)
        env0.assert_expr_is_of_type(state_var, T_State)
        return (T_captures_entry_, env0)

    elif p == r"{EXPR} : a List consisting of the sequence of code points of {VAR} interpreted as a UTF-16 encoded \({EMU_XREF}\) Unicode string":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (ListType(T_code_point_), env0)

    elif p == r"{EXPR} : a List of {VAR} {LITERAL} values, indexed 1 through {VAR}":
        [var, literal, var2] = children
        assert var.children == var2.children
        env0.assert_expr_is_of_type(var, T_Integer_)
        (lit_t, env1) = tc_expr(literal, env0); assert env1 is env0
        return (ListType(lit_t), env1)

    elif p == r"{EXPR} : a new List whose elements are the characters of {VAR} at indices {VAR} \(inclusive\) through {VAR} \(exclusive\)":
        [list_var, s_var, e_var] = children
        env0.assert_expr_is_of_type(list_var, ListType(T_character_))
        env0.assert_expr_is_of_type(s_var, T_Integer_)
        env0.assert_expr_is_of_type(e_var, T_Integer_)
        return (ListType(T_character_), env0)

    # --------------------------------------------------------
    # return T_Parse_Node

    elif p == r'{MULTILINE_EXPR} : the result of parsing the source text{_INDENT}{_NL} +<pre><code class="javascript">([^<>]+)</code></pre>{_NL} +using the syntactic grammar with the goal symbol {NONTERMINAL}\.{_OUTDENT}':
        [_, nonterminal] = children
        return (ptn_type_for(nonterminal), env0)

    elif p == r"{EXPR} : the {NONTERMINAL} that is covered by {LOCAL_REF}":
        [nonterminal, local_ref] = children
        env0.assert_expr_is_of_type(local_ref, T_Parse_Node)
        return (ptn_type_for(nonterminal), env0)

    elif p == r"{EXPR} : the ECMAScript code that is the result of parsing {VAR}, interpreted as UTF-16 encoded Unicode text as described in {EMU_XREF}, for the goal symbol {NONTERMINAL}. If {VAR} is {LITERAL}, additional early error rules from {EMU_XREF} are applied. If {VAR} is {LITERAL}, additional early error rules from {EMU_XREF} are applied. If {VAR} is {LITERAL}, additional early error rules from {EMU_XREF} are applied. If the parse fails, throw a {ERROR_TYPE} exception. If any early errors are detected, throw a {ERROR_TYPE} or a {ERROR_TYPE} exception, depending on the type of the error \(but see also clause {EMU_XREF}\). Parsing and early error detection may be interweaved in an implementation-dependent manner":
        [s_var, emu_xref, goal_nont,
        b1_var, b1_lit, emu_xref1,
        b2_var, b2_lit, emu_xref2,
        b3_var, b3_lit, emu_xref3,
        error_type1,
        error_type2, error_type3, emu_xref4] = children
        #
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(b1_var, T_Boolean)
        env0.assert_expr_is_of_type(b2_var, T_Boolean)
        env0.assert_expr_is_of_type(b3_var, T_Boolean)
        [error_type_name1] = error_type1.children
        [error_type_name2] = error_type2.children
        [error_type_name3] = error_type3.children
        proc_add_return(env0, ThrowType(NamedType(error_type_name1)), error_type1)
        proc_add_return(env0, ThrowType(NamedType(error_type_name2)), error_type2)
        proc_add_return(env0, ThrowType(NamedType(error_type_name3)), error_type3)
        return (ptn_type_for(goal_nont), env0)

    elif p == r"{EXPR} : the result of parsing {VAR}, interpreted as UTF-16 encoded Unicode text as described in {EMU_XREF}, using {VAR} as the goal symbol. Throw a {ERROR_TYPE} exception if the parse fails":
        [var, emu_xref, goal_var, error_type] = children    
        env0.assert_expr_is_of_type(var, T_String)
        env0.assert_expr_is_of_type(goal_var, T_grammar_symbol_)
        [error_type_name] = error_type.children
        proc_add_return( env0, ThrowType(NamedType(error_type_name)), error_type)
        return (T_Parse_Node, env0)

    # ----

    elif p == r'{LOCAL_REF} : the {NONTERMINAL} of {VAR}':
        [nonterminal, var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        # XXX could check that t is a nonterminal that actually has a child of that type
        # but that requires having the whole grammar handy
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : this {NONTERMINAL}':
        [nonterminal] = children
        # XXX check
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : {NONTERMINAL}':
        [nonterminal] = children
        return (ptn_type_for(nonterminal), env0)

    elif p == r'{PROD_REF} : the (first|second|third|fourth) {NONTERMINAL}':
        [nth, nonterminal] = children
        # XXX should check that the 'current' production has such.
        return (ptn_type_for(nonterminal), env0)

    elif p in [
        r'{PROD_REF} : the {NONTERMINAL}',
        r'{PROD_REF} : the (first|second|third) {NONTERMINAL}',
    ]:
        nonterminal = children[-1]
        return (ptn_type_for(nonterminal), env0)

    elif p == r"{PROD_REF} : the corresponding {NONTERMINAL}":
        [nont] = children
        return (ptn_type_for(nont), env0)

    elif p == r"{PROD_REF} : the {NONTERMINAL} that is that {NONTERMINAL}":
        [a_nont, b_nont] = children
        return (ptn_type_for(a_nont), env0)

    elif p == r"{EXPR} : an instance of the production {EMU_GRAMMAR}":
        [emu_grammar] = children
        [production] = emu_grammar.children
        assert production == 'FormalParameters : [empty]'
        return (ptn_type_for('FormalParameters'), env0)

    elif p == r"{EXPR} : the {NONTERMINAL}, {NONTERMINAL}, or {NONTERMINAL} that most closely contains {VAR}":
        [*nont_, var] = children
        env0.assert_expr_is_of_type(var, T_Parse_Node)
        return (T_Parse_Node, env0)

    elif p == r"{PROD_REF} : the {NONTERMINAL} that is that single code point":
        [nont] = children
        return (T_Parse_Node, env0)

    elif p == r"{LOCAL_REF} : the parsed code that is {DOTTING}":
        [dotting] = children
        env0.assert_expr_is_of_type(dotting, T_Parse_Node)
        return (T_Parse_Node, env0)

    # --------------------------------------------------------
    # return T_Object

    elif p == r'{EXPR} : the binding object for {VAR}':
        [var] = children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_object_Environment_Record)
        return (T_Object, env0)

    elif p == r'{EXPR} : a newly created object with an internal slot for each name in {VAR}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_SlotName_))
        return (T_Object, env1)

    elif p == r'{EXPR} : a newly created object':
        [] = children
        return (T_Object, env0)

    elif p in [
        r"{LITERAL} : (%\w+%)",
        r"{EXPR} : the intrinsic object (%\w+%)",
    ]:
        [wki_name] = children
        return (T_Object, env0)
        # could be more specific in some cases

    elif p == r"{SETTABLE} : the Generator component of {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_execution_context)
        return (T_Object, env0)

    elif p == r"{EXPR} : the arguments object":
        [] = children
        return (T_Object, env0)

    elif p == r"{EXPR} : a newly created arguments exotic object with a {DSBN} internal slot":
        [dsbn] = children
        return (T_Object, env0)

    elif p == r"{EXPR} : {VAR}'s intrinsic object named {VAR}":
        [r_var, n_var] = children
        env0.assert_expr_is_of_type(r_var, T_Realm_Record)
        env0.assert_expr_is_of_type(n_var, T_String)
        return (T_Object, env0)

    elif p == r"{EXPR} : a newly created String exotic object":
        [] = children
        return (T_Object, env0)

    # -------------------------------------------------
    # return T_CharSet

    elif p == r'{EXPR} : the set containing all characters numbered {VAR} through {VAR}, inclusive':
        [var1, var2] = children
        env1 = env0.ensure_expr_is_of_type(var1, T_Integer_)
        env2 = env0.ensure_expr_is_of_type(var2, T_Integer_)
        assert env1 is env0
        assert env2 is env0
        return (T_CharSet, env0)

    elif p == r"{EXPR} : an empty set":
        [] = children
        return (T_CharSet, env0)

    elif p in [
        r"{EXPR} : the CharSet containing the single character {CP_LITERAL}",
        r"{EXPR} : the CharSet containing the single character {VAR}",
        r"{EXPR} : the CharSet containing the single character that is {EXPR}",
    ]:
        [ex] = children
        env0.ensure_expr_is_of_type(ex, T_character_)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing the character matched by {PROD_REF}":
        [prod_ref] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : a one-element CharSet containing the character {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_character_)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the union of CharSets {VAR}, {VAR} and {VAR}":
        [va, vb, vc] = children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        envc = env0.ensure_expr_is_of_type(vc, T_CharSet)
        return (T_CharSet, envs_or([enva, envb, envc]))

    elif p == r"{EXPR} : the union of CharSets {VAR} and {VAR}":
        [va, vb] = children
        enva = env0.ensure_expr_is_of_type(va, T_CharSet)
        envb = env0.ensure_expr_is_of_type(vb, T_CharSet)
        return (T_CharSet, env_or(enva, envb))

    elif p == r"{MULTILINE_EXPR} : a set of characters containing the sixty-three characters:{FIGURE}":
        [figure] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters except {NONTERMINAL}":
        [nonterminal] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the ten-element set of characters containing the characters `0` through `9` inclusive":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters not included in the set returned by {EMU_GRAMMAR}[ ]?":
        [emu_grammar] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of characters containing the characters that are on the right-hand side of the {NONTERMINAL} or {NONTERMINAL} productions":
        [nont1, nont2] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the set of all characters returned by {PREFIX_PAREN}":
        [pp] = children
        env0.assert_expr_is_of_type(pp, T_CharSet)
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the empty CharSet":
        [] = children
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {VAR} with value {VAR}":
        [va, vb] = children
        env0.assert_expr_is_of_type(va, ListType(T_Integer_))
        env0.assert_expr_is_of_type(vb, ListType(T_Integer_))
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property &ldquo;General_Category&rdquo; with value {VAR}":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (T_CharSet, env0)

    elif p == r"{EXPR} : the CharSet containing all Unicode code points whose character database definition includes the property {VAR} with value &ldquo;True&rdquo;":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (T_CharSet, env0)

    # -------------------------------------------------
    # return T_function_object_

    elif p == r'{EXPR} : a newly created ECMAScript function object with the internal slots listed in {EMU_XREF}. All of those internal slots are initialized to {LITERAL}':
        [emu_xref, literal] = children
        return (T_function_object_, env0)

    elif p == r'{EXPR} : a new built-in function object that when called performs the action described by {VAR}. The new function object has internal slots whose names are the elements of {VAR}. The initial value of each of those internal slots is {LITERAL}':
        [var1, var2, literal] = children
        # literal
        env1 = env0.ensure_expr_is_of_type(var1, T_alg_steps)
        # env1 = env0.ensure_expr_is_of_type(var2, )
        return (T_function_object_, env1)

    # ------------------------------------------------
    # return T_alg_steps

    elif p == r"{EXPR} : the algorithm steps defined in {EMU_XREF}":
        [emu_xref] = children
        return (T_alg_steps, env0)

    elif p == r"{EXPR} : the algorithm steps defined in (.+) \({EMU_XREF}\)":
        [_, emu_xref] = children
        return (T_alg_steps, env0)

    elif p in [
        r"{EXPR} : the steps of an ArgGetter function as specified below",
        r"{EXPR} : the steps of an ArgSetter function as specified below",
    ]:
        [] = children
        return (T_alg_steps, env0)

    elif p == r"{EXPR} : the algorithm steps specified in {EMU_XREF} for the %ThrowTypeError% function":
        [emu_xref] = children
        return (T_alg_steps, env0)

    elif p == r"{EXPR} : an empty sequence of algorithm steps":
        [] = children
        return (T_alg_steps, env0)

    # ------------------------------------------------
    # return T_execution_context

    elif p == r"{EXPR} : a new execution context":
        [] = children
        return (T_execution_context, env0)

    elif p == r"{EXPR} : a new ECMAScript code execution context":
        [] = children
        return (T_execution_context, env0)

    elif p == r'{EXPR} : the running execution context':
        [] = children
        return (T_execution_context, env0)

    elif p == r'{EXPR} : the topmost execution context on the execution context stack whose ScriptOrModule component is not {LITERAL}':
        [literal] = children
        return (T_execution_context, env0)

    elif p == r"{EXPR} : the second to top element of the execution context stack":
        [] = children
        return (T_execution_context, env0)

    # -------------------------------------------------
    # return T_Reference

    elif p == r'{EXPR} : a value of type Reference whose base value component is {EX}, whose referenced name component is {VAR}, and whose strict reference flag is {VAR}':
        [bv_ex, rn_var, srf_var] = children

        env1 = env0.ensure_expr_is_of_type(bv_ex, T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number | T_Environment_Record)
        env2 = env1.ensure_expr_is_of_type(rn_var, T_String | T_Symbol)
        env3 = env2.ensure_expr_is_of_type(srf_var, T_Boolean)

        return (T_Reference, env3)

    elif p in [
        r'{V} : the reference (_V_)',
        r'{V} : (_V_)',
    ]:
        [v_name] = children
        assert v_name == '_V_'
        assert env0.vars[v_name] == T_Reference
        return (T_Reference, env0)

    elif p == r"{EXPR} : a value of type Reference that is a Super Reference whose base value component is {VAR}, whose referenced name component is {VAR}, whose thisValue component is {VAR}, and whose strict reference flag is {VAR}":
        [b_var, n_var, t_var, s_var] = children
        env0.assert_expr_is_of_type(b_var, T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number)
        env0.assert_expr_is_of_type(n_var, T_String | T_Symbol)
        env0.assert_expr_is_of_type(t_var, T_Tangible_)
        env0.assert_expr_is_of_type(s_var, T_Boolean)
        return (T_Reference, env0)

    # -------------------------------------------------

    elif p == r"{EXPR} : the value of the thisValue component of the reference {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return (T_Tangible_, env0)

    elif p in [
        r"{EXPR} : the value currently bound to {VAR} in {VAR}",
        r"{SETTABLE} : the bound value for {VAR} in {VAR}",
    ]:
        [n_var, er_var] = children
        env0.assert_expr_is_of_type(n_var, T_String)
        env0.assert_expr_is_of_type(er_var, T_Environment_Record)
        return (T_Tangible_, env0)

    elif p == r"{EXPR} : the result of applying {VAR} to {VAR} and {VAR} as if evaluating the expression {VAR} {VAR} {VAR}":
        [op_var, avar, bvar, avar2, op_var2, bvar2] = children
        assert op_var.children == op_var2.children
        assert avar.children == avar2.children
        assert bvar.children == bvar2.children
        env0.assert_expr_is_of_type(op_var, T_proc_)
        env1 = env0.ensure_expr_is_of_type(avar, T_Tangible_)
        env2 = env1.ensure_expr_is_of_type(bvar, T_Tangible_)
        return (T_Tangible_, env2)

    elif p == r"{EXPR} : the Completion Record that is the result of evaluating {VAR} in an implementation-defined manner that conforms to the specification of {VAR}. {VAR} is the \*this\* value, {VAR} provides the named parameters, and the NewTarget value is \*undefined\*":
        [avar, bvar, cvar, dvar] = children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, T_Tangible_)
        env0.assert_expr_is_of_type(dvar, ListType(T_Tangible_))
        return (T_Tangible_ | T_throw_, env0)

    elif p == r"{EXPR} : the Completion Record that is the result of evaluating {VAR} in an implementation-defined manner that conforms to the specification of {VAR}. The \*this\* value is uninitialized, {VAR} provides the named parameters, and {VAR} provides the NewTarget value":
        [avar, bvar, cvar, dvar] = children
        assert avar.children == bvar.children
        env0.assert_expr_is_of_type(avar, T_function_object_)
        env0.assert_expr_is_of_type(cvar, ListType(T_Tangible_))
        env0.assert_expr_is_of_type(dvar, T_Tangible_)
        return (T_Tangible_ | T_throw_, env0)

    # -------------------------------------------------
    # return component of T_execution_context

    elif p == r"{SETTABLE} : {VAR}'s ScriptOrModule component":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_execution_context)
        return (T_Module_Record | T_Script_Record, env1)

    elif p in [
        r"{SETTABLE} : the (Function|Realm|ScriptOrModule|LexicalEnvironment|VariableEnvironment) of {VAR}",
        r"{SETTABLE} : {VAR}'s (Function|Realm|ScriptOrModule|LexicalEnvironment|VariableEnvironment)",
        r"{SETTABLE} : the {VAR}'s (Function|Realm|ScriptOrModule|LexicalEnvironment|VariableEnvironment)",
    ]:
        if p.endswith('{VAR}'):
            [component_name, var] = children
        else:
            [var, component_name] = children

        # env0.assert_expr_is_of_type(var, T_execution_context)

        (t, env1) = tc_expr(var, env0); assert env1 is env0
        if t == T_TBD:
            t = T_execution_context
            env2 = env1.with_expr_type_replaced(var, t)
        else:
            env2 = env1

        result_type = {
            # todo: make it a record?
            # 7110: Table 22: State Components for All Execution Contexts
            'Function'      : T_function_object_,
            'Realm'         : T_Realm_Record,
            'ScriptOrModule': T_Module_Record | T_Script_Record,

            # 7159: Table 23: Additional State Components for ECMAScript Code Execution Contexts
            'LexicalEnvironment' : T_Lexical_Environment,
            'VariableEnvironment': T_Lexical_Environment,

            # 7191: Table 24: Additional State Components for Generator Execution Contexts
            # 'Generator' : T_Gen
        }[component_name]

        return (result_type, env2)

    # ----
    # return component of T_Lexical_Environment

    elif p == r"{SETTABLE} : {VAR}'s (EnvironmentRecord|outer environment reference)":
        [var, component_name] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0

        if t == T_TBD:
            t = T_Lexical_Environment
            env2 = env1.with_expr_type_replaced(var, t)
        else:
            env2 = env1

        result_type = {
            'EnvironmentRecord': T_Environment_Record,
            'outer environment reference': T_Null | T_Lexical_Environment,
        }[component_name]
        return (result_type, env2)

    elif p == r"{SETTABLE} : the EnvironmentRecord component of {VAR}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Lexical_Environment)
        return (T_Environment_Record, env1)

    elif p == r'{SETTABLE} : the outer lexical environment reference of {VAR}':
        [var] = children
        env0.assert_expr_is_of_type(var, T_Lexical_Environment)
        return (T_Lexical_Environment | T_Null, env0)

    # -------------------------------------------------
    # return proc type

    elif p == r'{EXPR} : the abstract operation named in the Conversion Operation column in {EMU_XREF} for Element Type {VAR}':
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_String)
        return (ProcType([T_Tangible_], T_Integer_), env1)

    elif p == r"{EXPR} : the `@` where \|AssignmentOperator\| is `@=`":
        return (ProcType([T_Number, T_Number], T_Number), env0)

    elif p == r"{EXPR} : the internal procedure that evaluates the above parse of {VAR} by applying the semantics provided in {EMU_XREF} using {VAR} as the pattern's List of {NONTERMINAL} values and {VAR} as the flag parameters":
        [source_var, emu_xref, chars_var, nont, f_var] = children
        env0.assert_expr_is_of_type(source_var, T_String)
        env0.assert_expr_is_of_type(chars_var, ListType(T_character_))
        env0.assert_expr_is_of_type(f_var, T_String)
        return (T_RegExpMatcher_, env0)

    elif p == r"{EXPR} : a Continuation that always returns its State argument as a successful MatchResult":
        [] = children
        return (T_Continuation, env0)

    elif p == r"{EXPR} : a Continuation that takes a State argument {VAR} and returns the result of calling {PREFIX_PAREN}":
        [state_param, pp] = children
        env_for_body = env0.plus_new_entry(state_param, T_State)
        (pp_type, env1) = tc_expr(pp, env_for_body)
        assert pp_type == T_MatchResult
        return (T_Continuation, env0)

    elif p in [
        r"{MULTILINE_EXPR} : an internal AssertionTester closure that takes a State argument {VAR} and performs the following steps when evaluated:{IND_COMMANDS}",
        r"{MULTILINE_EXPR} : an internal Continuation closure that takes one State argument {VAR} and performs the following steps(?: when evaluated)?:{IND_COMMANDS}",
    ]:
        [state_param, commands] = children
        env_for_commands = env0.plus_new_entry(state_param, T_State)
        defns = [(None, commands)]
        env_after_commands = tc_proc(None, defns, env_for_commands)
        if 'AssertionTester' in p:
            closure_t = T_AssertionTester
        elif 'Continuation' in p:
            closure_t = T_Continuation
        else:
            assert 0
        assert env_after_commands.vars['*return*'].is_a_subtype_of_or_equal_to(closure_t.return_type)
        return (closure_t, env0)

    elif p == r"{MULTILINE_EXPR} : an internal Matcher closure that takes two arguments, a State {VAR} and a Continuation {VAR}, and performs the following steps(?: when evaluated)?:{IND_COMMANDS}":
        [state_param, cont_param, commands] = children
        env_for_commands = env0.plus_new_entry(state_param, T_State).plus_new_entry(cont_param, T_Continuation)
        defns = [(None, commands)]
        env_after_commands = tc_proc(None, defns, env_for_commands)
        # returns from within `commands`
        # contribute to the matcher's return type,
        # not to the current operation's.
        assert env_after_commands.vars['*return*'] == T_MatchResult
        return (T_Matcher, env0)

    elif p == r"{EXPR} : a Matcher that takes two arguments, a State {VAR} and a Continuation {VAR}, and returns the result of calling {PREFIX_PAREN}":
        [state_param, cont_param, prefix_paren] = children
        env_for_pp = env0.plus_new_entry(state_param, T_State).plus_new_entry(cont_param, T_Continuation)
        (t, env1) = tc_expr(prefix_paren, env_for_pp)
        assert t == T_MatchResult
        return (T_Matcher, env0)

    elif p == r"{MULTILINE_EXPR} : an internal closure that takes two arguments, a String {VAR} and an integer {VAR}, and performs the following steps:{IND_COMMANDS}":
        [s_param, i_param, commands] = children
        env_for_commands = env0.plus_new_entry(s_param, T_String).plus_new_entry(i_param, T_Integer_)
        defns = [(None, commands)]
        env_after_commands = tc_proc(None, defns, env_for_commands)
        t  = ProcType([T_String, T_Integer_], T_MatchResult)
        return (t, env0)

    # -------------------------------------------------
    # return Environment_Record

    elif p == r'{EXPR} : a new declarative Environment Record containing no bindings':
        return (T_declarative_Environment_Record, env0)

    elif p == r'{EXPR} : a new function Environment Record containing no bindings':
        return (T_function_Environment_Record, env0)

    elif p == r'{EXPR} : a new object Environment Record containing {VAR} as the binding object':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return (T_object_Environment_Record, env1)

    elif p == r'{EXPR} : a new global Environment Record':
        return (T_global_Environment_Record, env0)

    elif p == r'{EXPR} : a new module Environment Record containing no bindings':
        return (T_module_Environment_Record, env0)

    # -------------------------------------------------
    # return T_Realm_Record

    elif p == r'{EX} : the current Realm Record':
        [] = children
        return (T_Realm_Record, env0)

    elif p == r"{EXPR} : a new Realm Record":
        [] = children
        return (T_Realm_Record, env0)

    # -------------------------------------------------
    # whatever

    elif p == r"{NONTERMINAL} : \|([A-Za-z][A-Za-z0-9]+(?:\[[^][]+\])?(?:_opt)?)\|":
        [nont_name] = children
        # Note that |Foo| often denotes a Parse Node,
        # rather than a grammar symbol,
        # but we capture those cases before they get to here.
        return (T_grammar_symbol_, env0)

    elif p == r"{EXPR} : the grammar symbol {NONTERMINAL}":
        [nont] = children
        return (T_grammar_symbol_, env0)

    elif expr.prod.lhs_s == '{VAR}':
        [var_name] = children
        return (env0.vars[var_name], env0)

    elif p in [
        r'{SETTABLE} : {VAR}',
        r'{FACTOR} : {VAR}',
    ]:
        [var] = children
        [var_name] = var.children
        assert var_name in env0.vars, var_name # XXX else complain
        t = env0.vars[var_name]
        # print("the type of %s is %s" % (var_name, t))
        return (t, env0)

    elif p == r'{EXPR} : the Agent Record of the surrounding agent':
        [] = children
        return (T_Agent_Record, env0)

    elif p == r'{EXPR} : a new (Data Block|Shared Data Block) value consisting of {VAR} bytes\. If it is impossible to create such a (Data Block|Shared Data Block), throw a {ERROR_TYPE} exception':
        [block_type, var, block_type2, error_type] = children
        assert block_type == block_type2
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_Integer_)
        [error_type_name] = error_type.children
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
        return (parse_type_string(block_type), env1)

    elif p == r'{EXPR} : a new Shared Data Block value consisting of {VAR} bytes\. If it is impossible to create such a Shared Data Block, throw a {ERROR_TYPE} exception':
        [var, error_type] = children
        (t, env1) = tc_expr(var, env0)
        assert env1 is env0
        assert t.is_a_subtype_of_or_equal_to(T_Integer_)
        [error_type_name] = error_type.children
        proc_add_return(env0, ThrowType(NamedType(error_type_name)), error_type)
        return (T_Shared_Data_Block, env1)

    elif expr.prod.lhs_s == '{RECORD_CONSTRUCTOR}':
        [constructor_prefix, fields] = children

        if constructor_prefix == 'Completion':
            f_ = dict( get_field_items(fields) )
            assert sorted(f_.keys()) == ['Target', 'Type', 'Value']
            type_ex = f_['Type']
            value_ex = f_['Value']
            target_ex = f_['Target']

            if fields.source_text() == '[[Type]]: _completionRecord_.[[Type]], [[Value]]: _value_, [[Target]]: _completionRecord_.[[Target]]':
                # The specialest of special cases!
                # Occurs once, in UpdateEmpty.
                # In the context there,
                # the static type of _completionRecord_ is
                # (or would be, if STA were smart enough)
                # T_empty_ | T_continue_ | T_break_,
                # and the static type of _value_ is T_Tangible_ | T_empty_

                return (T_Tangible_ | T_empty_ | T_continue_ | T_break_, env0)
                
            else:
                env1 = env0.ensure_expr_is_of_type(value_ex, T_Tangible_ | T_empty_)
                (value_type, _) = tc_expr(value_ex, env1) # bleah

                env0.assert_expr_is_of_type(target_ex, T_String | T_empty_)

                comptype_lit = type_ex.is_a('{COMPTYPE_LITERAL}')
                assert comptype_lit is not None
                ct = type_corresponding_to_comptype_literal(comptype_lit)
                if ct == T_Normal:
                    t = value_type
                elif ct == T_throw_:
                    t = ThrowType(value_type)
                else:
                    t = ct

                return (t, env1)

        if constructor_prefix == 'Record':
            record_type_name = None
            field_names = sorted(get_field_names(fields))
            if field_names == ['Array', 'Site']:
                record_type_name = 'templateMap_entry_'
            elif field_names == ['Closure', 'Key']:
                record_type_name = 'methodDef_record_'
            elif field_names == ['Configurable', 'Enumerable', 'Get', 'Set', 'Value', 'Writable']:
                # CompletePropertyDescriptor: the almost-Property Descriptor
                record_type_name = 'Property Descriptor'
            elif field_names == ['Done', 'Iterator', 'NextMethod']:
                record_type_name = 'iterator_record_'
            elif field_names == ['ExportName', 'Module']:
                record_type_name = 'ExportResolveSet_Record_'
            elif field_names == ['Key', 'Symbol']:
                record_type_name = 'GlobalSymbolRegistry Record'
            elif field_names == ['Key', 'Value']:
                record_type_name = 'MapData_record_'
            elif field_names == ['Reject', 'Resolve']:
                record_type_name = 'ResolvingFunctions_record_'
            elif field_names == ['Value']:
                fst = fields.source_text()
                if fst == '[[Value]]: *false*':
                    record_type_name = 'boolean_value_record_'
                elif fst == '[[Value]]: 1':
                    record_type_name = 'integer_value_record_'
                else:
                    assert 0, fst

            if record_type_name:
                add_pass_error(
                    expr,
                    "Inferred record type `%s`: be explicit!" % record_type_name
                )
                field_info = fields_for_record_type_named_[record_type_name]
            else:
                add_pass_error(
                    expr,
                    "Could not infer a record type for fields: " + str(field_names)
                )
                record_type_name = 'Record'
                field_info = None

        else:
            if constructor_prefix in [
                'ReadModifyWriteSharedMemory',
                'ReadSharedMemory',
                'WriteSharedMemory',
            ]:
                record_type_name = constructor_prefix + ' event'
            elif constructor_prefix in [
                'Completion',
                'PromiseReaction',
                'PromiseCapability',
                'AsyncGeneratorRequest',
            ]:
                record_type_name = constructor_prefix + ' Record'
            elif constructor_prefix == 'PropertyDescriptor':
                record_type_name = 'Property Descriptor'
            else:
                record_type_name = constructor_prefix
            field_info = fields_for_record_type_named_[record_type_name]

        envs = []
        for (dsbn_name, ex) in get_field_items(fields):
            if field_info is None:
                # (because it's just a Record, not a particular (named) kind of Record)
                # We can't really assert anything.
                (t, env1) = tc_expr(ex, env0); assert env1 is env0
            else:
                declared_field_type = field_info[dsbn_name]
                env1 = env0.ensure_expr_is_of_type(ex, declared_field_type)
            envs.append(env1)
        env2 = envs_or(envs)

        # XXX: Should also ensure that each field is specified exactly once.

        return ( parse_type_string(record_type_name), env2 )

    elif p == r"{SETTABLE} : the {DSBN} field of the surrounding agent's Agent Record":
        [dsbn] = children
        [dsbn_name] = dsbn.children
        assert dsbn_name in fields_for_record_type_named_['Agent Record'], dsbn_name
        return ( fields_for_record_type_named_['Agent Record'][dsbn_name], env0 )

    elif p == r'{SETTABLE} : the {DSBN} field of the element in {DOTTING} whose {DSBN} is {PREFIX_PAREN}':
        [dsbn1, dotting, dsbn2, pp] = children
        (list_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        telm = list_type.element_type
        [dsbn_name1] = dsbn1.children
        [dsbn_name2] = dsbn2.children
        assert telm == T_Agent_Events_Record
        assert dsbn_name2 == 'AgentSignifier'
        env1.assert_expr_is_of_type(pp, T_agent_signifier_)
        assert dsbn_name1 == 'EventList'
        return ( fields_for_record_type_named_['Agent Events Record'][dsbn_name1], env1 )

    elif p == r'{EXPR} : an Iterator object \({EMU_XREF}\) whose `next` method iterates over all the String-valued keys of enumerable properties of {VAR}. The iterator object is never directly accessible to ECMAScript code. The mechanics and order of enumerating the properties is not specified but must conform to the rules specified below':
        [emu_xref, var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Object)
        return (T_iterator_record_, env1)

    elif p == r'{EX} : the base value component of {VAR}':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Reference)
        return (T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number | T_Environment_Record, env1)

    elif p == r"{NAMED_OPERATION_INVOCATION} : {NOI}":
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0, expr_value_will_be_discarded)
        if noi_t == T_TBD:
            # Don't do the comparison to Normal,
            # because that loses the TBD-ness,
            # which is used as a sentinel all over.
            return (noi_t, env1)
        else:
            # (normal_part_of_type, abrupt_part_of_type) = noi_t.split_by(T_Normal)
            # if abrupt_part_of_type != T_0:
            #     add_pass_error(
            #         expr,
            #         "warning: `%s` static type includes `%s`, but isn't prefixed by ! or ?"
            #         % (expr.source_text(), abrupt_part_of_type)
            #     )
            #     # But that might be okay.
            #     # E.g. Return {NOI} -- inserting a '?' would have no effect.
            #     # or if next instruction is ReturnIfAbrupt.
            #     # So I dropped this warning,
            #     # and just rely on Abrupt values being flagged if necessary down the line.
            return (noi_t, env1)

    elif p == r'{NAMED_OPERATION_INVOCATION} : ! {NOI}':
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0)

        if noi_t == T_TBD:
            return (T_TBD, env1)

        (abrupt_part_of_type, normal_part_of_type) = noi_t.split_by(T_Abrupt)

        if abrupt_part_of_type == T_0:
            add_pass_error(
                noi,
                "The static type of the invocation is `%s`, so shouldn't need a '!'" % str(noi_t)
            )
        else:
            # add_pass_error(
            #     expr,
            #     "STA fails to confirm that `%s` will return a Normal" % noi.source_text()
            # )
            # It's unsurprising, perhaps even *expected*,
            # that STA can't confirm it.
            pass

        return (normal_part_of_type, env1)

    elif p == r'{NAMED_OPERATION_INVOCATION} : \? {NOI}':
        [noi] = children
        (noi_t, env1) = tc_expr(noi, env0)

        if noi_t == T_TBD:
            return (T_TBD, env1)

        (abrupt_part_of_type, normal_part_of_type) = noi_t.split_by(T_Abrupt)

        if normal_part_of_type == T_0:
            add_pass_error(
                expr,
                "used '?', but STA says operation can't return normal: " + expr.source_text()
            )

        if abrupt_part_of_type == T_0:
            add_pass_error(
                expr,
                "used '?', but STA says operation can't return abrupt: " + expr.source_text()
            )

        proc_add_return(env1, abrupt_part_of_type, expr)

        return (normal_part_of_type, env1)

    elif p == r"{TYPE_ARG} : {VAR}'s base value component":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Reference)
        return_type = T_Undefined | T_Object | T_Boolean | T_String | T_Symbol | T_Number | T_Environment_Record
        return (return_type, env0)

    elif p == r'{EX} : the strict reference flag of {VAR}':
        [v] = children
        env0.assert_expr_is_of_type(v, T_Reference)
        return (T_Boolean, env0)

    elif p == r"{SETTABLE} : the running execution context's (LexicalEnvironment|VariableEnvironment)":
        [component_name] = children
        t = {
            'LexicalEnvironment' : T_Lexical_Environment,
            'VariableEnvironment': T_Lexical_Environment,
        }[component_name]
        return (t, env0)

    elif p == r'{EXPR} : the (declarative|function|module|object|global) Environment Record for which the method was invoked':
        [which] = children
        t = parse_type_string(which + ' Environment Record')
        return (t, env0)

    elif p == r'{EXPR} : a new Lexical Environment':
        return (T_Lexical_Environment, env0)

    elif p == r'{EXPR} : the byte elements of {VAR} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2008 binary32 value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_IEEE_binary32_, env1)

    elif p == r'{EXPR} : the byte elements of {VAR} concatenated and interpreted as a little-endian bit string encoding of an IEEE 754-2008 binary64 value':
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_Integer_))
        return (T_IEEE_binary64_, env1)

    elif p == r"{EXPR} : a copy of {VAR}'s _captures_ List":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_captures_list_, env1)

    elif p in [
        r"{SETTABLE} : {VAR}\[{EX}\]",
        r"{SETTABLE} : {DOTTING}\[{EX}\]",
    ]:
        [seq_ex, subscript_var] = children
        (seq_type, seq_env) = tc_expr(seq_ex, env0); assert seq_env is env0
        env2 = env0.ensure_expr_is_of_type(subscript_var, T_Integer_); assert env2 is env0
        if isinstance(seq_type, ListType):
            item_type = seq_type.element_type
        elif seq_type == T_List:
            item_type = T_TBD
        elif seq_type.is_a_subtype_of_or_equal_to(T_Data_Block | T_Shared_Data_Block):
            item_type = T_Integer_
        elif seq_type.is_a_subtype_of_or_equal_to(T_Data_Block | T_Shared_Data_Block | T_Null):
            add_pass_error(
                expr,
                "STA fails to confirm that %s isnt Null" %
                (seq_ex.source_text())
            )
            item_type = T_Integer_
        else:
            assert 0, seq_type
        return (item_type, env0)

    elif p == r"{EXPR} : the State \({EX}, {VAR}\)":
        [ex, var] = children
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_); assert env1 is env0
        env2 = env0.ensure_expr_is_of_type(var, T_captures_list_); assert env2 is env0
        return (T_State, env0)

    elif p == r"{EXPR} : {VAR}'s State":
        # todo?: change to Assert: _r_ is a State
        [var] = children
        env0.assert_expr_is_of_type(var, T_State)
        return (T_State, env0)

    elif p == r"{EXPR} : an empty Set":
        [] = children
        return (T_Set, env0)

    elif p == r"{EX} : &laquo; &raquo;":
        [] = children
        return (T_List, env0)

    elif p == r"{EX} : &laquo; {EXLIST} &raquo;":
        [exlist] = children
        ex_types = set()
        for ex in exes_in_exlist(exlist):
            (ex_type, env1) = tc_expr(ex, env0); assert env1 is env0
            ex_types.add(ex_type)
        if len(ex_types) == 0:
            list_type = T_List # ListType(T_0)
        else:
            element_type = union_of_types(ex_types)
            list_type = ListType(element_type)
        return (list_type, env0)

    elif p == r"{EX} : the _withEnvironment_ flag of {VAR}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_object_Environment_Record)
        return (T_Boolean, env1)

    elif p == r"{SETTABLE} : the _withEnvironment_ flag of {VAR}'s EnvironmentRecord":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Lexical_Environment)
        return (T_Boolean, env1)

    elif p == r"{EXPR} : {VAR}'s _captures_ List":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, T_State)
        return (T_captures_list_, env1)

    elif p == r"{EX} : {DSBN}":
        [dsbn] = children
        return (T_SlotName_, env0)

    elif p == r"{SETTABLE} : the LexicalEnvironment of the running execution context":
        [] = children
        return (T_Lexical_Environment, env0)

    elif p in [
        r"{EXPR} : a newly created Property Descriptor with no fields",
        r"{EXPR} : a new Property Descriptor that initially has no fields",
    ]:
        [] = children
        return (T_Property_Descriptor, env0)

    elif p == r"{EXPR} : the fully populated data property descriptor for the property containing the specified attributes for the property. For properties listed in {EMU_XREF}, {EMU_XREF}, or {EMU_XREF} the value of the {DSBN} attribute is the corresponding intrinsic object from {VAR}":
        [emu_xref1, emu_xref2, emu_xref3, dsbn, var] = children
        env0.assert_expr_is_of_type(var, T_Realm_Record)
        return (T_Property_Descriptor, env0)

    elif p == r"{EXPR} : {VAR}'s own property whose key is {VAR}":
        [obj_var, key_var] = children
        env0.assert_expr_is_of_type(obj_var, T_Object)
        env0.assert_expr_is_of_type(key_var, T_String | T_Symbol)
        return (T_property_, env0)

    elif p == r"{SETTABLE} : {VAR}'s {DSBN} attribute":
        [prop_var, dsbn] = children
        [dsbn_name] = dsbn.children
        if dsbn_name in ['Enumerable', 'Configurable']:
            env0.assert_expr_is_of_type(prop_var, T_property_)
            result_type = T_Boolean
        elif dsbn_name in ['Value', 'Writable']:
            env0.assert_expr_is_of_type(prop_var, T_data_property_)
            result_type = T_Tangible_ if dsbn_name == 'Value' else T_Boolean
        elif dsbn_name in ['Get', 'Set']:
            env0.assert_expr_is_of_type(prop_var, T_accessor_property_)
            result_type = T_Object | T_Undefined
        else:
            assert 0
        return (result_type, env0)

    elif p == r"{SETTABLE} : the {DSBN} internal slot of this Date object":
        [dsbn] = children
        [dsbn_name] = dsbn.children
        assert dsbn_name == 'DateValue'
        return (T_Number, env0)

    elif p == r"{EXPR} : this Source Text Module Record":
        [] = children
        return (T_Source_Text_Module_Record, env0)

    elif p == r"{EX} : (ScriptEvaluationJob|TopLevelModuleEvaluationJob|PromiseResolveThenableJob|PromiseReactionJob)":
        [op_name] = children
        return (T_proc_, env0)

    elif p == r"{EXPR} : a newly created Array exotic object":
        [] = children
        return (T_Array_object_, env0)

    elif p in [
        r"{EXPR} : a copy of {VAR}",
        r"{EXPR} : a copy of {DOTTING}",
    ]:
        [var] = children
        (t, env1) = tc_expr(var, env0); assert env1 is env0
        return (t, env1)

    elif p in [
        r"{EXPR} : a copy of the List {VAR}",
        r"{EXPR} : a new List which is a copy of {VAR}",
    ]:
        [var] = children
        t = env0.assert_expr_is_of_type(var, T_List)
        return (t, env0)

    elif p == r"{EXPR} : a new List of {VAR} with {LITERAL} appended":
        [list_var, element] = children
        t = env0.assert_expr_is_of_type(list_var, T_List)
        env0.assert_expr_is_of_type(element, t.element_type)
        return (t, env0)

    elif p in [
        r"{EXPR} : the value of the first element of {VAR}",
        r"{EXPR} : the first element of {VAR}",
        r"{EXPR} : the second element of {VAR}",
        r"{EXPR} : the last element in {VAR}",
    ]:
        # todo: replace with ad hoc record
        [var] = children
        list_type = env0.assert_expr_is_of_type(var, T_List)
        return (list_type.element_type, env0)

    elif p == r"{EXPR} : an implementation-defined Completion value":
        [] = children
        return (T_Tangible_ | T_empty_ | T_throw_, env0)

    elif p == r"{EXPR} : the element of {VAR} whose {DSBN} is the same as {DOTTING}":
        [list_var, dsbn, dotting] = children
        [dsbn_name] = dsbn.children
        (list_type, env1) = tc_expr(list_var, env0); assert env1 is env0
        assert isinstance(list_type, ListType)
        et = list_type.element_type
        assert isinstance(et, NamedType)
        fields = fields_for_record_type_named_[et.name]
        whose_type = fields[dsbn_name]
        env1.assert_expr_is_of_type(dotting, whose_type)
        return (et, env1)

    elif p == r"{EXPR} : the three results {VAR}, {VAR}, and {LITERAL}":
        [a, b, c] = children
        (a_t, env1) = tc_expr(a, env0); assert env1 is env0
        (b_t, env2) = tc_expr(b, env0); assert env2 is env0
        (c_t, env3) = tc_expr(c, env0); assert env3 is env0
        t = TupleType( (a_t, b_t, c_t) )
        return (t, env0)

    elif p == r"{EXPR} : the two results {EX} and {EX}":
        [a, b] = children
        (a_t, env1) = tc_expr(a, env0); assert env1 is env0
        (b_t, env2) = tc_expr(b, env0); assert env2 is env0
        t = TupleType( (a_t, b_t) )
        return (t, env0)

    elif p == r"{EXPR} : a new Record":
        # Once, in CreateIntrinsics
        [] = children
        return (T_Intrinsics_Record, env0)

    elif p == r"{EXPR} : such an object created in an implementation-defined manner":
        [] = children
        return (T_Object, env0)

    elif p == r"{EXPR} : a non-empty Job Queue chosen in an implementation-defined manner. If all Job Queues are empty, the result is implementation-defined":
        [] = children
        return (ListType(T_PendingJob), env0)

    elif p == r"{EXPR} : the PendingJob record at the front of {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_PendingJob))
        return (T_PendingJob, env0)

    elif p == r"{NOI} : the abstract operation named by {DOTTING} using the elements of {DOTTING} as its arguments":
        [adotting, bdotting] = children
        env0.assert_expr_is_of_type(adotting, T_proc_)
        env0.assert_expr_is_of_type(bdotting, T_List)
        return (T_Tangible_ | T_empty_ | T_Abrupt, env0)
    
    elif p == r"{EX} : a newly created {ERROR_TYPE} object":
        [error_type] = children
        [error_type_name] = error_type.children
        return (NamedType(error_type_name), env0)

    elif p == r"{EXPR} : the canonical property name of {VAR} as given in the &ldquo;Canonical property name&rdquo; column of the corresponding row":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the List of Unicode code points of {VAR}":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the canonical property value of {VAR} as given in the &ldquo;Canonical property value&rdquo; column of the corresponding row":
        [v] = children
        env0.assert_expr_is_of_type(v, ListType(T_Integer_))
        return (ListType(T_Integer_), env0)

    elif p == r"{EXPR} : the List, in source text order, of Unicode code points in the source text matched by this production":
        [] = children
        return (ListType(T_Integer_), env0)

    # ----

    elif p == r"{EXPR} : the WaiterList that is referenced by the pair \({VAR}, {VAR}\)":
        [sdb, i] = children
        env0.assert_expr_is_of_type(sdb, T_Shared_Data_Block)
        env0.assert_expr_is_of_type(i, T_Integer_)
        return (T_WaiterList, env0)

    elif p in [
        r"{FACTOR} : msPerDay",
        r"{FACTOR} : msPerMinute",
    ]:
        [] = children
        return (T_Integer_, env0)

    elif p == r"{EXPR} : a reference to the list of waiters in {VAR}":
        [wl] = children
        env0.assert_expr_is_of_type(wl, T_WaiterList)
        return (ListType(T_agent_signifier_), env0)

    elif p == r"{EXPR} : the first waiter in {VAR}":
        [wl] = children
        env0.assert_expr_is_of_type(wl, ListType(T_agent_signifier_))
        return (T_agent_signifier_, env0)

    elif p in [
        r"{EX} : \*this\* value",
        r"{EX} : the \*this\* value",
    ]:
        return (T_Tangible_, env0)

    elif p in [
        r"{EXPR} : a List consisting of all of the arguments passed to this function, starting with the second argument. If fewer than two arguments were passed, the List is empty",
        r"{EXPR} : a List containing the arguments passed to this function",
        r"{EXPR} : a List whose elements are the arguments passed to this function",
        r"{EXPR} : a List whose elements are, in left to right order, the arguments that were passed to this function invocation",
        r"{EXPR} : a List whose elements are, in left to right order, the portion of the actual argument list starting with the third argument. The list is empty if fewer than three arguments were passed",
        r"{EXPR} : a zero-origined List containing the argument items in order",
        r"{EXPR} : the List of argument values starting with the second argument",
        r"{EXPR} : the List of arguments passed to this function",
    ]:
        [] = children
        return (ListType(T_Tangible_), env0)

    elif p in [
        r"{EXPR} : the actual number of arguments passed to this function",
        r"{EXPR} : the number of actual arguments minus 2",
        r"{EXPR} : the number of actual arguments",
        r"{EXPR} : the number of arguments passed to this function call",
    ]:
        [] = children
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the String value that is the result of normalizing {VAR} into the normalization form named by {VAR} as specified in <a [^<>]+>[^<>]+</a>":
        [s_var, nf_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(nf_var, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value that is a copy of {VAR} with both leading and trailing white space removed. The definition of white space is the union of \|WhiteSpace\| and \|LineTerminator\|. When determining whether a Unicode code point is in Unicode general category &ldquo;Space_Separator&rdquo; \(&ldquo;Zs&rdquo;\), code unit sequences are interpreted as UTF-16 encoded code point sequences as specified in {EMU_XREF}":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the code unit \(represented as a 16-bit unsigned integer\) at index {VAR} within {VAR}":
        [ivar, svar] = children
        env0.assert_expr_is_of_type(ivar, T_Integer_)
        env0.assert_expr_is_of_type(svar, T_String)
        return (T_code_unit_, env0)

    elif p == r"{EXPR} : the String value containing the single code unit {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_code_unit_)
        return (T_String, env0)

    elif p == r"{EXPR} : a substring of {VAR} consisting of the leftmost code unit that is not a \|StrWhiteSpaceChar\| and all code units to the right of that code unit. \(In other words, remove leading white space.\) If {VAR} does not contain any such code units, let {VAR} be the empty string":
        [var1, var2, var3] = children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the longest prefix of {VAR}, which might be {VAR} itself, that satisfies the syntax of a {NONTERMINAL}":
        [var1, var2, nont] = children
        assert same_source_text(var1, var2)
        env0.assert_expr_is_of_type(var1, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the Number value for {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_transitioning_from_Number_to_MathReal)
        return (T_Number, env0)

    elif p == r"{EXPR} : the integer represented by the four hexadecimal digits at indices {NUM_EXPR}, {NUM_EXPR}, {NUM_EXPR}, and {NUM_EXPR} within {VAR}":
        [e1, e2, e3, e4, var] = children
        env0.assert_expr_is_of_type(e1, T_Integer_)
        env0.assert_expr_is_of_type(e2, T_Integer_)
        env0.assert_expr_is_of_type(e3, T_Integer_)
        env0.assert_expr_is_of_type(e4, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the integer represented by two zeroes plus the two hexadecimal digits at indices {NUM_EXPR} and {NUM_EXPR} within {VAR}":
        [i1, i2, var] = children
        env0.assert_expr_is_of_type(i1, T_Integer_)
        env0.assert_expr_is_of_type(i2, T_Integer_)
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : this Date object":
        [] = children
        return (T_Object | ThrowType(T_TypeError), env0)

    elif p == r"{EXPR} : the List that is {DOTTING}":
        [dotting] = children
        (dotting_type, env1) = tc_expr(dotting, env0); assert env1 is env0
        dotting_type.is_a_subtype_of_or_equal_to(T_List)
        return (dotting_type, env0)

    elif p == r"{EXPR} : the number of leading zero bits in the 32-bit binary representation of {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{NUM_EXPR} : the exact mathematical value of {SUM}":
        [summ] = children
        env0.assert_expr_is_of_type(summ, T_Number)
        return (T_transitioning_from_Number_to_MathReal, env0)

    elif p == r"{EX} : the digits of the decimal representation of {VAR} \(in order, with no leading zeroes\)":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        return (ListType(T_code_unit_), env0)

    elif p == r"{EX} : the remaining {EX} code units of {VAR}":
        [ex, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(ex, T_Integer_)
        return (T_String, env1)

    elif p == r"{EX} : the first {SUM} code units of {VAR}":
        [summ, var] = children
        env0.assert_expr_is_of_type(var, T_String)
        env1 = env0.ensure_expr_is_of_type(summ, T_Integer_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String representation of this Number value using the radix specified by {VAR}. Letters `a`-`z` are used for digits with values 10 through 35. The precise algorithm is implementation-dependent, however the algorithm should be a generalization of that specified in {EMU_XREF}":
        [var, emu_xref] = children
        env1 = env0.ensure_expr_is_of_type(var, T_Integer_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose code units are, in order, the elements in the List {VAR}. If {VAR} is 0, the empty string is returned":
        [list_var, len_var] = children
        env0.assert_expr_is_of_type(len_var, T_Integer_)
        env1 = env0.ensure_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose code units are, in order, the elements in the List {VAR}. If {VAR} has no elements, the empty string is returned":
        [list_var, list_var2] = children
        assert same_source_text(list_var, list_var2)
        env0.assert_expr_is_of_type(list_var, ListType(T_code_unit_))
        return (T_String, env0)

    elif p == r"{EXPR} : the String value that is made from {VAR} copies of {VAR} appended together. If {VAR} is 0, {VAR} is the empty String":
        [n_var, s_var, n_var2, x_var] = children
        assert same_source_text(n_var2, n_var)
        env0.assert_expr_is_of_type(s_var, T_String)
        env1 = env0.ensure_expr_is_of_type(n_var, T_Integer_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value containing {VAR} consecutive code units from {VAR} beginning with the code unit at index {VAR}":
        [len_var, s_var, k_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(len_var, T_Integer_)
        env1 = env0.ensure_expr_is_of_type(k_var, T_Integer_)
        return (T_String, env1)

    elif p == r"{EXPR} : the String value whose length is {EX}, containing code units from {VAR}, namely the code units with indices {VAR} through {EX}, in ascending order":
        [len_ex, s_var, start_var, end_var] = children
        env0.assert_expr_is_of_type(s_var, T_String)
        env0.assert_expr_is_of_type(start_var, T_Integer_)
        env0.assert_expr_is_of_type(end_var, T_Integer_)
        env0.assert_expr_is_of_type(len_ex, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : a value of Number type, whose value is {EXPR}":
        [expr] = children
        env1 = env0.ensure_expr_is_of_type(expr, T_Number)
        return (T_Number, env1)

    elif p == r"{EXPR} : a List containing in order the code points as defined in {EMU_XREF} of {VAR}, starting at the first element of {VAR}":
        [emu_xref, s_var, s_var2] = children
        assert same_source_text(s_var2, s_var)
        env0.assert_expr_is_of_type(s_var, T_String)
        return (ListType(T_code_point_), env0)

    elif p == r"{EXPR} : a List where the elements are the result of toLowercase\({VAR}\), according to the Unicode Default Case Conversion algorithm":
        [var] = children
        env0.assert_expr_is_of_type(var, ListType(T_code_point_))
        return (ListType(T_code_point_), env0)

    elif p in [
        r"{EX} : the GlobalSymbolRegistry List",
        r"{EX} : the GlobalSymbolRegistry List \(see {EMU_XREF}\)",
    ]:
        return (ListType(T_GlobalSymbolRegistry_Record), env0)

    elif p == r"{EXPR} : a new unique Symbol value whose {DSBN} value is {VAR}":
        [dsbn, var] = children
        assert dsbn.source_text() == '[[Description]]'
        env0.assert_expr_is_of_type(var, T_String | T_Undefined)
        return (T_Symbol, env0)

    elif p == r"{EXPR} : a String containing one instance of each code unit valid in {NONTERMINAL}":
        [nont] = children
        return (T_String, env0)

    elif p == r"{EXPR} : a String containing one instance of each code unit valid in {NONTERMINAL} plus {STR_LITERAL}":
        [nont, strlit] = children
        env0.assert_expr_is_of_type(strlit, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : a String containing one instance of each code unit valid in {NONTERMINAL} and {NONTERMINAL} plus {STR_LITERAL}":
        [nonta, nontb, strlit] = children
        env0.assert_expr_is_of_type(strlit, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : a newly created substring of {VAR} consisting of the first code unit that is not a {NONTERMINAL} and all code units following that code unit. \(In other words, remove leading white space.\) If {VAR} does not contain any such code unit, let {VAR} be the empty string":
        [var, nont, var2, x] = children
        assert same_source_text(var2, var)
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the substring of {VAR} consisting of all code units before the first such code unit":
        [var] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_String, env0)

    elif p == r"{EXPR} : the mathematical integer value that is represented by {VAR} in radix-{VAR} notation, using the letters <b>A</b>-<b>Z</b> and <b>a</b>-<b>z</b> for digits with values 10 through 35":
        [zvar, rvar] = children
        env0.assert_expr_is_of_type(zvar, T_String)
        env0.assert_expr_is_of_type(rvar, T_Integer_)
        return (T_transitioning_from_Number_to_MathReal, env0)

    elif p == r"{EXPR} : the String value consisting of repeated concatenations of {EX} truncated to length {VAR}":
        [ex, var] = children
        env0.assert_expr_is_of_type(ex, T_String)
        env0.assert_expr_is_of_type(var, T_Integer_)
        return (T_String, env0)

    elif p == r"{EX} : `compareExchange`":
        [] = children
        return (T_bytes_combining_op_, env0)

    elif p == r"{EXPR} : the first agent in {VAR}":
        [var] = children
        env1 = env0.ensure_expr_is_of_type(var, ListType(T_agent_signifier_))
        return (T_agent_signifier_, env1)

    elif p == r"{EX} : `(add|and|second|or|subtract|xor)`":
        [name] = children
        return (T_bytes_combining_op_, env0)

    elif p == r"{EXPR} : the number of elements of {VAR}":
        [var] = children
        env0.assert_expr_is_of_type(var, T_List)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the Record { {DSBN}, {DSBN} } that is the value of {EX}":
        [dsbna, dsbnb, ex] = children
        assert dsbna.source_text() == '[[Key]]'
        assert dsbnb.source_text() == '[[Value]]'
        env0.assert_expr_is_of_type(ex, T_MapData_record_)
        return (T_MapData_record_, env0)

    elif p == r"{LITERAL} : the intrinsic function %ObjProto_toString%":
        [] = children
        return (T_function_object_, env0)

    elif p == r"{EX} : the first {VAR} code units of {VAR}":
        [n, s] = children
        env0.assert_expr_is_of_type(n, T_Integer_)
        env0.assert_expr_is_of_type(s, T_String)
        return (ListType(T_code_unit_), env0)

    elif p == r"{EX} : the trailing substring of {VAR} starting at index {VAR}":
        [s, n] = children
        env0.assert_expr_is_of_type(s, T_String)
        env0.assert_expr_is_of_type(n, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value equal to the substring of {VAR} consisting of the (code units|elements) at indices {VAR} \(inclusive\) through {VAR} \(exclusive\)":
        [s, _, start, end] = children
        assert _ == 'code units'
        env0.assert_expr_is_of_type(s, T_String)
        env0.assert_expr_is_of_type(start, T_Integer_)
        env0.assert_expr_is_of_type(end, T_Integer_)
        return (T_String, env0)

    elif p == r"{EXPR} : a List whose first element is {VAR} and whose subsequent elements are, in left to right order, the arguments that were passed to this function invocation":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : a new \(possibly empty\) List consisting of all of the argument values provided after {VAR} in order":
        [var] = children
        env0.assert_expr_is_of_type(var, T_Tangible_)
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : the String value for the list-separator String appropriate for the host environment's current locale \(this is derived in an implementation-defined way\)":
        [] = children
        return (T_String, env0)

    elif p == r"{EXPR} : the larger of 0 and the result of {VAR} minus the number of elements of {VAR}":
        [num_var, list_var] = children
        env0.assert_expr_is_of_type(list_var, T_List)
        env1 = env0.ensure_expr_is_of_type(num_var, T_Integer_)
        return (T_Integer_, env1)

    elif p == r"{EXPR} : the intrinsic object listed in column one of {EMU_XREF} for {DOTTING}":
        [emu_xref, dotting] = children
        env0.assert_expr_is_of_type(dotting, T_String)
        return (T_function_object_, env0)

    elif p == r"{EXPR} : the result of parsing and evaluating {VAR} as if it was the source text of an ECMAScript {NONTERMINAL}. The extended PropertyDefinitionEvaluation semantics defined in {EMU_XREF} must not be used during the evaluation":
        [svar, nont, emu_xref] = children
        env0.assert_expr_is_of_type(svar, T_String)
        return (T_Tangible_ | T_Abrupt, env0)

    elif p == r"{EXPR} : the String value containing {VAR} occurrences of {CU_LITERAL}. This will be the empty String if {VAR} is less than 1":
        [n, lit, n2] = children
        assert same_source_text(n, n2)
        env0.assert_expr_is_of_type(lit, T_code_unit_)
        return (T_String, env0)

    elif p == r"{EXPR} : the String value consisting of the first 10 code units of {VAR}":
        [v] = children
        env0.assert_expr_is_of_type(v, T_String)
        return (T_String, env0)

    elif p == r"{EX} : the current value of {VAR}":
        [var] = children
        (var_t, var_env) = tc_expr(var, env0); assert var_env is env0
        return (var_t, env0)

    elif p == "{EXPR} : a String in the form of a {NONTERMINAL} \({NONTERMINAL} if {VAR} contains `\"u\"`\) equivalent to {VAR} interpreted as UTF-16 encoded Unicode code points \({EMU_XREF}\), in which certain code points are escaped as described below. {VAR} may or may not be identical to {VAR}; however, the internal procedure that would result from evaluating {VAR} as a {NONTERMINAL} \({NONTERMINAL} if {VAR} contains `\"u\"`\) must behave identically to the internal procedure given by the constructed object's {DSBN} internal slot. Multiple calls to this abstract operation using the same values for {VAR} and {VAR} must produce identical results":
        # XXX
        return (T_String, env0)

    elif p == r"{EX} : NewTarget":
        [] = children
        return (T_constructor_object_ | T_Undefined, env0)

    elif p == r"{EXPR} : the active function object":
        [] = children
        return (T_function_object_, env0)

    elif p in [
        "{EX} : <code>\"%<var>NativeError</var>Prototype%\"</code>",
        "{EX} : <code>\"%<var>TypedArray</var>Prototype%\"</code>",
    ]:
        [] = children
        return (T_String, env0)
        
    elif p == r"{EXPR} : the {VAR} that was passed to this function by {DSBN} or {DSBN}":
        [var, dsbna, dsbnb] = children
        assert var.source_text() == '_argumentsList_'
        # It's not a reference to an in-scope variable,
        # it's a reference to a variable at a higher level.
        # It's more of a reminder of where the '_args_' parameter comes from.
        return (ListType(T_Tangible_), env0)

    elif p == r"{EXPR} : the Number that is the time value \(UTC\) identifying the current time":
        [] = children
        return (T_Number, env0)

    elif p == r"{EXPR} : the time value \(UTC\) identifying the current time":
        [] = children
        return (T_Number, env0)

    elif p == r"{EXPR} : the result of parsing {VAR} as a date, in exactly the same manner as for the `parse` method \({EMU_XREF}\)":
        [var, emu_xref] = children
        env0.assert_expr_is_of_type(var, T_String)
        return (T_Integer_, env0)

    elif p == r"{EXPR} : the String value of the Constructor Name value specified in {EMU_XREF} for this <var>TypedArray</var> constructor":
        [emu_xref] = children
        return (T_String, env0)

    elif p == r"{PAIR} : \({VAR}, {VAR}\)":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_Shared_Data_Block_event)
        env0.assert_expr_is_of_type(b, T_Shared_Data_Block_event)
        return (T_pair_, env0)

    elif p in [
        r"{EXPR} : the element in {DOTTING} whose {DSBN} is {EX}",
        r"{EXPR} : the element of {DOTTING} whose {DSBN} field is {VAR}",
    ]:
        [dotting, dsbn, e] = children
        # over-specific:
        if ' in ' in p:
            env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
            assert dsbn.source_text() == '[[AgentSignifier]]'
            env0.assert_expr_is_of_type(e, T_agent_signifier_)
            return (T_Agent_Events_Record, env0)
        elif ' of ' in p:
            env0.assert_expr_is_of_type(dotting, ListType(T_Chosen_Value_Record))
            assert dsbn.source_text() == '[[Event]]'
            env0.assert_expr_is_of_type(e, T_Shared_Data_Block_event)
            return (T_Chosen_Value_Record, env0)
        else:
            assert 0

    elif p == r"{EXPR} : the Agent Events Record in {DOTTING} whose {DSBN} is {NAMED_OPERATION_INVOCATION}":
        [dotting, dsbn, e] = children
        env0.assert_expr_is_of_type(dotting, ListType(T_Agent_Events_Record))
        assert dsbn.source_text() == '[[AgentSignifier]]'
        env0.assert_expr_is_of_type(e, T_agent_signifier_)
        return (T_Agent_Events_Record, env0)

    elif p in [
        r"{EXPR} : an implementation-dependent String source code representation of {VAR}\. The representation must conform to the rules below. It is implementation-dependent whether the representation includes bound function information or information about the target function",
        r"{EXPR} : an implementation-dependent String source code representation of {VAR}\. The representation must conform to the rules below",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_function_object_)
        return (T_String, env0) # XXX: spec should talk about encoding source code in UTF-16?

    elif p in [
        r"{EXPR} : the result of converting {VAR} to a value in IEEE 754-2008 binary32 format using roundTiesToEven",
        r"{EXPR} : the result of converting {VAR} to a value in IEEE 754-2008 binary64 format",
        r"{EXPR} : the ECMAScript Number value corresponding to {VAR}",
    ]:
        [var] = children
        env0.assert_expr_is_of_type(var, T_Number)
        # XXX The intermediates are not really T_Number
        return (T_Number, env0)

    elif p == r"{EX} : The remainder of dividing {EX} by {EX}":
        [a, b] = children
        env0.assert_expr_is_of_type(a, T_Integer_)
        env0.assert_expr_is_of_type(b, T_Integer_)
        return (T_Integer_, env0)

    elif p == r"{EX} : \({EX}, {EX}\)":
        [a, b] = children
        # over-specific:
        env0.assert_expr_is_of_type(a, T_Synchronize_event)
        env0.assert_expr_is_of_type(b, T_Synchronize_event)
        return (T_pair_, env0)

    # elif p == r"{EXPR} : a List containing the 4 bytes that are the result of converting {VAR} to IEEE 754-2008 binary32 format using &ldquo;Round to nearest, ties to even&rdquo; rounding mode. If {VAR} is {LITERAL}, the bytes are arranged in big endian order. Otherwise, the bytes are arranged in little endian order. If {VAR} is \*NaN\*, {VAR} may be set to any implementation chosen IEEE 754-2008 binary32 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable \*NaN\* value":
    # elif p == r"{EXPR} : a List containing the 8 bytes that are the IEEE 754-2008 binary64 format encoding of {VAR}. If {VAR} is {LITERAL}, the bytes are arranged in big endian order. Otherwise, the bytes are arranged in little endian order. If {VAR} is \*NaN\*, {VAR} may be set to any implementation chosen IEEE 754-2008 binary64 format Not-a-Number encoding. An implementation must always choose the same encoding for each implementation distinguishable \*NaN\* value":
    # elif p == r"{EXPR} : an implementation-dependent String value that represents {VAR} as a date and time in the current time zone using a convenient, human-readable form":
    # elif p == r"{EXPR} : the CharSet containing the single character that is {EXPR}":
    # elif p == r"{EXPR} : the CharSet containing the single character {VAR}":
    # elif p == r"{EXPR} : the ECMAScript Number value corresponding to {VAR}":
    # elif p == r"{EXPR} : the List (containing the|of) {NONTERMINAL} items in {PROD_REF}, in source text order. If {PROD_REF} is not present, {VAR} is &laquo; &raquo;":
    # elif p == r"{EXPR} : the List of events {PREFIX_PAREN}":
    # elif p == r"{EXPR} : the String value computed by the concatenation of {EX} and {EX}":
    # elif p == r"{EXPR} : the String value consisting of {EX} followed by {EX}":
    # elif p == r"{EXPR} : the String value consisting solely of {CU_LITERAL}":
    # elif p == r"{EXPR} : the String value containing the two code units {VAR} and {VAR}":
    # elif p == r"{EXPR} : the String value containing {VAR} consecutive elements from {VAR} beginning with the element at index {VAR}": # todo: element of String
    # elif p == r"{EXPR} : the String value produced by concatenating {EX} and {EX}":
    # elif p == r"{EXPR} : the String value that is the concatenation of {EX} and {EX}":
    # elif p == r"{EXPR} : the String value that is the result of concatenating {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the String value whose elements are, in order, the elements of {VAR}":
    # elif p == r"{EXPR} : the character represented by {PROD_REF}":
    # elif p == r"{EXPR} : the character {CP_LITERAL}":
    # elif p == r"{EXPR} : the concatenation of Strings {EX} and {EX}":
    # elif p == r"{EXPR} : the concatenation of the Strings {EX} and {EX}":
    # elif p == r"{EXPR} : the concatenation of {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the concatenation of the four Strings {EX}, {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the concatenation of the three Strings {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the concatenation of {EX}, {EX}, {EX}, {EX}, and {EX}":
    # elif p == r"{EX} : the first {SUM} elements of {VAR}":
    # elif p == r"{EX} : the remaining {EX} elements of {VAR}":
    # elif p == r"{EXPR} : the result of applying the subtraction operation to {VAR} and {VAR}. See the note below {EMU_XREF}":
    # elif p == r"{EXPR} : the result of concatenating the strings {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the result of concatenating {EX}, {EX}, {EX}, and {EX}":
    # elif p == r"{EXPR} : the string consisting of the code unit {VAR} followed by the code unit {VAR}":
    # elif p == r"{EXPR} : the string consisting of the single code unit {VAR}":
    # elif p == r"{EXPR} : the string that is the concatenation of {EX} and {EX}":
    # elif p == r"{EXPR} : the two results {EX} and {EX}":
    # elif p == r"{EXPR} : the {NONTERMINAL} component of {VAR}":
    # elif p == r"{FIELDS} : {FIELDS}, {FIELD}":
    # elif p == r"{FIELDS} : {FIELD}":
    # elif p == r"{FIGURE} : {_NL} +<figure>{I_TABLE}{_NL} +</figure>":
    # elif p == r"{IF_CLOSED} : If {CONDITION}, {SMALL_COMMAND}\. However, an implementation is permitted to extend the behaviour of `\w+` for values of {VAR} less than {NUM_LITERAL} or greater than {NUM_LITERAL}. In this case `\w+` would not necessarily throw {ERROR_TYPE} for such values\.":
    # elif p == r"{IF_OPEN} : If {CONDITION}, then {SMALL_COMMAND}\.":
    # elif p == r"{IF_OPEN} : If {CONDITION}, then{IND_COMMANDS}":
    # elif p == r"{IF_OPEN} : If {CONDITION}, {SMALL_COMMAND} and {SMALL_COMMAND}\.":
    # elif p == r"{IF_OPEN} : If {CONDITION}, {SMALL_COMMAND}\.":
    # elif p == r"{I_BULLETS} : {_INDENT}{BULLETS}{_OUTDENT}":
    # elif p == r"{I_TABLE} : {_INDENT}{_NL} +<table class="lightweight(?:-table)?">(?:.|\n)+?</table>{_OUTDENT}":
    # elif p == r"{NOI} : StringValue of the {NONTERMINAL} of {NONTERMINAL} {VAR}":
    # elif p == r"{NUM_COMPARAND} : -1":
    # elif p == r"{NUM_COMPARAND} : \({SUM}\)":
    # elif p == r"{OPN_BEFORE_FOROF} : (?:the )?((?!Function|LexicalEnvironment|Realm|ScriptOrModule|VariableEnvironment)[A-Z]\w+)":
    # elif p == r"{OPN_BEFORE_PAREN} : (ForIn/Of(?:Head|Body)Evaluation|(?!Type\b)[A-Za-z]\w+)":
    # elif p == r"{OPN_BEFORE_PAREN} : {DOTTING}":
    # elif p == r"{OPN_BEFORE_PAREN} : {SAB_FUNCTION}":
    # elif p == r"{OPN_BEFORE_PAREN} : {VAR}":
    # elif p == r"{OPN_BEFORE_PAREN} : {VAR}\.([A-Z][A-Za-z]+)":
    # elif p == r"{RECORD_CONSTRUCTOR} : (?:the |a |a new )?(Record|Chosen Value Record|ExportEntry Record|ImportEntry Record|Completion|PropertyDescriptor|PendingJob|PromiseCapability|PromiseReaction|ReadModifyWriteSharedMemory|ReadSharedMemory|ResolvedBinding Record|Script Record|Source Text Module Record|WriteSharedMemory) ?{ ?{FIELDS} ?}":
    # elif p == r"{SAB_FUNCTION} : reads-bytes-from":
    # elif p == r"{SAB_RELATION} : agent-order":
    # elif p == r"{SAB_RELATION} : happens-before":
    # elif p == r"{SAB_RELATION} : host-synchronizes-with":
    # elif p == r"{SAB_RELATION} : is agent-order before":
    # elif p == r"{SAB_RELATION} : is memory-order before":
    # elif p == r"{SAB_RELATION} : reads-from":
    # elif p == r"{SAB_RELATION} : synchronizes-with":
    # elif p == r"{SETTABLE} : the {DSBN} field of {VAR}":
    # elif p == r"{STR_LITERAL} : \*"[^*"]*"\*":
    # elif p == r"{STR_LITERAL} : the String `","` \(a comma\)":
    # elif p == r"{STR_LITERAL} : the String `"-"`":
    # elif p == r"{STR_LITERAL} : the empty String":
    # elif p == r"{STR_LITERAL} : the empty String `""`":
    # elif p == r"{STR_LITERAL} : the empty String value":
    # elif p == r"{STR_LITERAL} : the empty string":
    # elif p == r"{STR_LITERAL} : the single-element String `","`": # todo: element of String
    # elif p == r"{STR_LITERAL} : the string `"(not-equal|ok|timed-out)"`":
    # elif p == r"{STR_LITERAL} : the string `":"`":
    # elif p == r"{TERMINAL} : `[a-z]+`":
    # elif p == r"{TERMINAL} : `\\\\`":
    # elif p == r"{TERM} : the number of code units in {VAR}":
    # elif p == r"{TYPE_NAME} : Boolean":
    # elif p == r"{TYPE_NAME} : Data Block":
    # elif p == r"{TYPE_NAME} : Null":
    # elif p == r"{TYPE_NAME} : Number":
    # elif p == r"{TYPE_NAME} : Object":
    # elif p == r"{TYPE_NAME} : Reference":
    # elif p == r"{TYPE_NAME} : Shared Data Block":
    # elif p == r"{TYPE_NAME} : String":
    # elif p == r"{TYPE_NAME} : Symbol":
    # elif p == r"{TYPE_NAME} : Undefined":
    # elif p == r"{CP_LITERAL} : &lt;BS&gt; U\+0008 \(BACKSPACE\)":
    # elif p == r"{CP_LITERAL} : U\+0000 \(NULL\)":
    # elif p == r"{ERROR_TYPE} : \*(TypeError|SyntaxError|RangeError|ReferenceError|URIError)\*":

    else:
        stderr()
        stderr("tc_expr:")
        stderr('    elif p == %s:' % escape(p))
        # pdb.set_trace()
        sys.exit(0)

# ------------------------------------------------------------------------------

def escape(s):
    if '"' in s:
        return '"' + s.replace('"', r'\"') + '"'
    else:
        return 'r"' + s + '"'

def same_source_text(a, b):
    return (a.source_text() == b.source_text())

# ------------------------------------------------------------------------------

def exes_in_exlist_opt(exlist_opt):
    assert exlist_opt.prod.lhs_s == '{EXLIST_OPT}'
    if exlist_opt.prod.rhs_s == '()':
        return []
    elif exlist_opt.prod.rhs_s == '{EXLIST}':
        [exlist] = exlist_opt.children
        return exes_in_exlist(exlist)
    else:
        assert 0, exlist_opt.prod.rhs_s

def exes_in_exlist(exlist):
    exes = []
    while True:
        assert exlist.prod.lhs_s == '{EXLIST}'
        if exlist.prod.rhs_s == '{EX}':
            [ex] = exlist.children
            exes.insert(0, ex)
            break
        elif exlist.prod.rhs_s == '{EXLIST}, {EX}':
            [inner_exlist, ex] = exlist.children
            exes.insert(0, ex)
            exlist = inner_exlist
        else:
            assert 0
    return exes

def tc_ao_invocation(callee_op_name, args, expr, env0):
    callee_op = operation_named_[callee_op_name]
    assert callee_op.kind == 'abstract operation'
    params = callee_op.parameters
    env1 = tc_args(params, args, env0, expr)
    return_type = callee_op.return_type
    return (return_type, env1)

def tc_sdo_invocation(op_name, main_arg, other_args, context, env0):
    op = operation_named_[op_name]
    assert op.kind == 'syntax-directed operation'

    env1 = env0.ensure_expr_is_of_type(main_arg, T_Parse_Node)
    # XXX expectation should be specific to what the callee accepts

    env2 = tc_args(op.parameters, other_args, env1, context)

    # seed:
    # if op_name == 'Evaluation': return (T_Tangible_, env0)
    # 'Contains': T_Boolean

    return (op.return_type, env2)

def with_fake_param_names(param_types):
    return [
        ('$%d' % (i+1), t )
        for (i, t) in enumerate(param_types)
    ]
        
def type_corresponding_to_comptype_literal(comptype_literal):
    assert isinstance(comptype_literal, ANode)

    if str(comptype_literal.prod) == '{LITERAL} : {COMPTYPE_LITERAL}':
        [comptype_literal] = comptype_literal.children

    assert comptype_literal.prod.lhs_s == '{COMPTYPE_LITERAL}'

    [chars] = comptype_literal.children
    t = {
        'normal'  : T_Normal,
        'continue': T_continue_,
        'break'   : T_break_,
        'return'  : T_return_,
        'throw'   : T_throw_,
    }[chars]
    return t

def tc_args( params, args, env0, context ):
    assert len(args) <= len(params)
    out_env = env0
    for ((param_name, param_type), arg) in zip_longest(params, args):

        if param_type == T_TBD:
            # Not much useful checking we can do.
            passed_part_of_param_type     = T_TBD
            not_passed_part_of_param_type = T_TBD
        else:
            (not_passed_part_of_param_type, passed_part_of_param_type) = param_type.split_by(T_not_passed)

        if arg is None:
            # No arg was passed to this parameter.
            if not_passed_part_of_param_type != T_0:
                # but the parameter is optional, so that's okay.
                pass
            else:
                # the parameter is not optional!
                add_pass_error(
                    context,
                    "No arg passed to non-optional param '%s'" % param_name
                )
        else:
            (arg_type, env1) = tc_expr(arg, env0)

            pt = passed_part_of_param_type

            env2 = env1 # overwritten in one case below:

            # Treat T_TBD like Top
            if pt == T_TBD:
                # This should only happen if the called operation
                # is in the same cluster as the calling operation.
                # (In particular, if the operation is calling itself.)
                #
                # Conceivably, we could go to the called operation and tell it
                # that this parameter must be able to accept arg_type.
                # However, let's assume that the current mechanisms will take care of it.
                # That is, by the end of this pass (on this cluster),
                # that pt will be refined,
                # and, in a subsequent pass, we'll be checking against that refined type.
                pass
            elif arg_type == T_TBD:
                env2 = env1.ensure_expr_is_of_type(arg, pt)
            elif arg_type.is_a_subtype_of_or_equal_to(pt):
                # normal case
                pass
            elif arg_type == T_List and isinstance(pt, ListType):
                # XXX: Still need this?
                # This happens when the arg is an List constructor with no items.
                # Not really worth complaining about.
                pass
            else:
                add_pass_error(
                    arg,
                    "arg %s has type %s, but param %s requires type %s"
                    % (arg.source_text(), arg_type, param_name, pt)
                )
                # The parameter-type might be too narrow,
                # or the arg-type might be too wide.
                # We don't know which is the problem.
                # So we just note the mismatch and go on. Hm.

            out_env = env_and(out_env, env2)

    return out_env

# ------------------------------------------------------------------------------

def is_simple_call(ex):
    prefix_paren = ex.is_a('{PREFIX_PAREN}')
    if prefix_paren is None: return None
    if prefix_paren.prod.rhs_s != '{OPN_BEFORE_PAREN}\({EXLIST_OPT}\)': return None
    [opn, exlist_opt] = prefix_paren.children

    if opn.prod.rhs_s != r'(ForIn/Of(?:Head|Body)Evaluation|(?!Type\b)[A-Za-z]\w+)': return None
    [op_name] = opn.children

    var = exlist_opt.is_a('{VAR}')
    if var is None: return None

    return (op_name, var)

# ------------------------------------------------------------------------------

def get_field_names(fields):
    return [
        dsbn_name
        for (dsbn_name, ex) in get_field_items(fields)
    ]

def get_field_items(fields):
    for field in get_fields(fields):
        assert str(field.prod) == '{FIELD} : {DSBN}: {EX}'
        [dsbn, ex] = field.children
        [dsbn_name] = dsbn.children
        yield (dsbn_name, ex)

def get_fields(fields):
    assert fields.prod.lhs_s == '{FIELDS}'
    if fields.prod.rhs_s == '{FIELDS}, {FIELD}':
        [prefields, field] = fields.children
        return get_fields(prefields) + [field]

    elif fields.prod.rhs_s == '{FIELD}':
        [field] = fields.children
        return [field]

    else:
        assert 0

# ------------------------------------------------------------------------------

fields_for_record_type_named_ = {

    'Property Descriptor': { # XXX not modelling this very well
        # table 2
        'Value'       : T_Tangible_,
        'Writable'    : T_Boolean,
        # table 3
        'Get'         : T_Object | T_Undefined, # | T_not_in_record
        'Set'         : T_Object | T_Undefined, # | T_not_in_record
        # common
        'Enumerable'  : T_Boolean,
        'Configurable': T_Boolean,
    },

    #? # 2651: Table 8: Completion Record Fields
    #? 'Completion Record': {
    #?     'Type'   : T_completion_kind_,
    #?     'Value'  : T_Tangible_ | T_empty_,
    #?     'Target' : T_String | T_empty_,
    #? },

    'Environment Record': {
    },

    # 5731: Table 16: Additional Fields of Function Environment Records
    'function Environment Record': {
        'ThisValue'        : T_Tangible_,
        'ThisBindingStatus': T_String, # enumeration
        'FunctionObject'   : T_function_object_,
        'HomeObject'       : T_Object | T_Undefined,
        'NewTarget'        : T_Object | T_Undefined,
    },

    # 5907: Table 18: Additional Fields of Global Environment Records
    'global Environment Record': {
        'ObjectRecord'     : T_object_Environment_Record,
        'GlobalThisValue'  : T_Object,
        'DeclarativeRecord': T_declarative_Environment_Record,
        'VarNames'         : ListType(T_String),
    },

    # 6561: Table 21: Realm Record Fields
    'Realm Record': {
        'Intrinsics'  : T_Intrinsics_Record,
        'GlobalObject': T_Object,
        'GlobalEnv'   : T_Lexical_Environment,
        'TemplateMap' : ListType(T_templateMap_entry_),
        'HostDefined' : T_host_defined_ | T_Undefined,
    },

    # 7212: NO TABLE
    'templateMap_entry_': {
        'Site'    : T_Parse_Node,
        'Array'   : T_Object,
    },

    # 7176: Agent Record Fields
    'Agent Record': {
        'LittleEndian': T_Boolean,
        'CanBlock'    : T_Boolean,
        'Signifier'   : T_agent_signifier_,
        'IsLockFree1' : T_Boolean,
        'IsLockFree2' : T_Boolean,
        'CandidateExecution': T_candidate_execution,
    },

    # 7343: Table 25: PendingJob Record Fields
    'PendingJob': {
        'Job'           : T_proc_,
        'Arguments'     : T_List,
        'Realm'         : T_Realm_Record,
        'ScriptOrModule': T_Script_Record | T_Module_Record,
        'HostDefined'   : T_host_defined_ | T_Undefined,
    },

    # 5515+5660: NO TABLE, not even a mention
    'iterator_record_': {
        'Iterator'  : T_Object, # iterator_object_ ?
        'NextMethod': T_function_object_,
        'Done'      : T_Boolean,
    },

    # 21275: NO TABLE, no mention
    'methodDef_record_': {
        'Closure' : T_function_object_,
        'Key'     : T_String | T_Symbol,
    },

    # 21832: Script Record Fields
    'Script Record': {
        'Realm'         : T_Realm_Record | T_Undefined,
        'Environment'   : T_Lexical_Environment | T_Undefined,
        'ECMAScriptCode': T_PTN_Script,
        'HostDefined'   : T_host_defined_ | T_Undefined,
    },

    # 22437: Table 36: Module Record Fields
    'Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Lexical_Environment | T_Undefined,
        'Namespace'       : T_Object | T_Undefined,
        'Status'          : T_String,
        'ErrorCompletion' : T_Abrupt | T_Undefined,
        'HostDefined'     : T_host_defined_ | T_Undefined,
    },

    'other Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Lexical_Environment | T_Undefined,
        'Namespace'       : T_Object | T_Undefined,
        'Status'          : T_String,
        'ErrorCompletion' : T_Abrupt | T_Undefined,
        'HostDefined'     : T_host_defined_ | T_Undefined,
    },

    # 23376
    'ResolvedBinding Record': {
        'Module'      : T_Module_Record,
        'BindingName' : T_String,
    },

    # 23406: Table 38: Additional Fields of Source Text Module Records
    'Source Text Module Record': {
        'Realm'           : T_Realm_Record | T_Undefined,
        'Environment'     : T_Lexical_Environment | T_Undefined,
        'Namespace'       : T_Object | T_Undefined,
        'Status'          : T_String,
        'ErrorCompletion' : T_Abrupt | T_Undefined,
        'HostDefined'     : T_host_defined_ | T_Undefined,
        #
        'ECMAScriptCode'       : T_Parse_Node,
        'RequestedModules'     : ListType(T_String),
        'ImportEntries'        : ListType(T_ImportEntry_Record),
        'LocalExportEntries'   : ListType(T_ExportEntry_Record),
        'IndirectExportEntries': ListType(T_ExportEntry_Record),
        'StarExportEntries'    : ListType(T_ExportEntry_Record),
        'Status'               : T_String,
        'EvaluationError'      : T_Abrupt | T_Undefined,
        'DFSIndex'             : T_Integer_ | T_Undefined,
        'DFSAncestorIndex'     : T_Integer_ | T_Undefined,
    },

    # 23490: Table 39: ImportEntry Record Fields
    'ImportEntry Record': {
        'ModuleRequest': T_String,
        'ImportName'   : T_String,
        'LocalName'    : T_String,
    },

    # 23627: Table 41: ExportEntry Record Fields
    'ExportEntry Record': {
        'ExportName'    : T_String, # | T_Null,
        'ModuleRequest' : T_String | T_Null,
        'ImportName'    : T_String | T_Null,
        'LocalName'     : T_String | T_Null,
    },

    # 24003
    'ExportResolveSet_Record_': {
        'Module'     : T_Module_Record,
        'ExportName' : T_String,
    },

    # 28088: table-44: GlobalSymbolRegistry Record Fields
    'GlobalSymbolRegistry Record': {
        'Key'   : T_String,
        'Symbol': T_Symbol,
    },

    # 38791: Table 57: PromiseCapability Record Fields
    'PromiseCapability Record': {
        'Promise' : T_Object | T_Undefined,
        'Resolve' : T_function_object_ | T_Undefined,
        'Reject'  : T_function_object_ | T_Undefined,
    },

    # 38864: Table 58: PromiseReaction Record Fields
    'PromiseReaction Record': {
        'Capability' : T_PromiseCapability_Record | T_Undefined,
        'Type'       : T_String,
        'Handler'    : T_function_object_ | T_Undefined,
    },

    # 39099: no table, no mention
    'MapData_record_': {
        'Key'   : T_Tangible_ | T_empty_,
        'Value' : T_Tangible_ | T_empty_,
    },

    # 39328: Agent Events Record Fields
    'Agent Events Record' : {
        'AgentSignifier'       : T_agent_signifier_,
        'EventList'            : ListType(T_event_),
        'AgentSynchronizesWith': ListType(T_pair_),
    },

    # 39380: Candidate Execution Record Fields
    'candidate execution': {
        'EventsRecords'       : ListType(T_Agent_Events_Record),
        'ChosenValues'        : ListType(T_Chosen_Value_Record),
        'AgentOrder'          : T_Relation,
        'ReadsBytesFrom'      : ProcType([T_event_], ListType(T_WriteSharedMemory_event | T_ReadModifyWriteSharedMemory_event)),
        'ReadsFrom'           : T_Relation,
        'HostSynchronizesWith': T_Relation,
        'SynchronizesWith'    : T_Relation,
        'HappensBefore'       : T_Relation,
    },

    # 39415: CreateResolvingFunctions NO TABLE, not even mentioned
    # 29803: `Promise.all` Resolve Element Functions NO TABLE, barely mentioned
    'boolean_value_record_': {
        'Value' : T_Boolean,
    },

    # 39438: CreateResolvingFunctions NO TABLE, not even mentioned
    'ResolvingFunctions_record_': {
        'Resolve' : T_function_object_,
        'Reject'  : T_function_object_,
    },

    # 39784: PerformPromiseAll NO TABLE, not even mentioned
    'integer_value_record_': {
        'Value' : T_Integer_,
    },

    # 40060 ...
    'Shared Data Block event': {
        'Order'       : T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
    },

    # repetitive, but easier than factoring out...
    'ReadSharedMemory event': {
        'Order'       : T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
    },

    'WriteSharedMemory event': {
        'Order'       : T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
        'Payload'     : ListType(T_Integer_),
    },

    'ReadModifyWriteSharedMemory event': {
        'Order'       : T_String,
        'NoTear'      : T_Boolean,
        'Block'       : T_Shared_Data_Block,
        'ByteIndex'   : T_Integer_,
        'ElementSize' : T_Integer_,
        'Payload'     : ListType(T_Integer_),
        'ModifyOp'    : T_bytes_combining_op_,
    },

    # 40224: Chosen Value Record Fields
    'Chosen Value Record': {
        'Event'       : T_Shared_Data_Block_event,
        'ChosenValue' : ListType(T_Integer_),
    },
    # 41899: AsyncGeneratorRequest Record Fields
    'AsyncGeneratorRequest Record': {
        'Completion' : T_Tangible_ | T_empty_ | T_Abrupt,
        'Capability' : T_PromiseCapability_Record,
    },

}


type_of_internal_thing_ = {

    # Ordinary Object Internal Methods and Internal Slots
    'Prototype'  : T_Object | T_Null,
    'Extensible' : T_Boolean,

    # 1188: Table 5: Essential Internal Methods
    # (Properly, this info *should* be taken from the results of STA.)
    'GetPrototypeOf'    : ProcType([                                             ], T_Object | T_Null                   | T_throw_),
    'SetPrototypeOf'    : ProcType([T_Object | T_Null                            ], T_Boolean                           | T_throw_),
    'IsExtensible'      : ProcType([                                             ], T_Boolean                           | T_throw_),
    'PreventExtensions' : ProcType([                                             ], T_Boolean                           | T_throw_),
    'GetOwnProperty'    : ProcType([T_String | T_Symbol                          ], T_Property_Descriptor | T_Undefined | T_throw_),
    'DefineOwnProperty' : ProcType([T_String | T_Symbol, T_Property_Descriptor   ], T_Boolean                           | T_throw_),
    'HasProperty'       : ProcType([T_String | T_Symbol                          ], T_Boolean                           | T_throw_),
    'Get'               : ProcType([T_String | T_Symbol, T_Tangible_             ], T_Tangible_                         | T_throw_),
    'Set'               : ProcType([T_String | T_Symbol, T_Tangible_, T_Tangible_], T_Boolean                           | T_throw_),
    'Delete'            : ProcType([T_String | T_Symbol                          ], T_Boolean                           | T_throw_),
    'OwnPropertyKeys'   : ProcType([                                             ], ListType(T_String | T_Symbol)       | T_throw_),

    # 1328: Table 6: Additional Essential Internal Methods of Function Objects
    'Call'              : ProcType([T_Tangible_, ListType(T_Tangible_)           ], T_Tangible_                         | T_throw_),
    'Construct'         : ProcType([ListType(T_Tangible_), T_Object              ], T_Object                            | T_throw_),

    # 4407
    'NumberData' : T_Number,
    # 4423
    'SymbolData' : T_Symbol,

    # 5253: NO TABLE, no mention
    'IteratedList'          : ListType(T_Tangible_),
    'ListIteratorNextIndex' : T_Integer_,

    # 8329: Table 27: Internal Slots of ECMAScript Function Objects
    'Environment'      : T_Lexical_Environment,
    'FormalParameters' : T_Parse_Node,
    'FunctionKind'     : T_String, # could be more specific
    'ECMAScriptCode'   : T_Parse_Node,
    'ConstructorKind'  : T_String, # could be more specific
    'Realm'            : T_Realm_Record,
    'ScriptOrModule'   : T_Script_Record | T_Module_Record | T_Null, # XXX must add Null to spec
    'ThisMode'         : T_this_mode,
    'Strict'           : T_Boolean,
    'HomeObject'       : T_Object,

    # 9078: Table 28: Internal Slots of Exotic Bound Function Objects
    'BoundTargetFunction': T_function_object_,
    'BoundThis'          : T_Tangible_,
    'BoundArguments'     : ListType(T_Tangible_),

    # 9373 NO TABLE
    'StringData' : T_String,

    # 9506: Arguments Exotic Objects NO TABLE
    'ParameterMap' : T_Object,

    # 9735: MakeArgGetter NO TABLE
    'Name' : T_String,
    'Env'  : T_Environment_Record,

    # 9806: Integer Indexed Exotic Objects NO TABLE
    'ViewedArrayBuffer' : T_ArrayBuffer_object_ | T_SharedArrayBuffer_object_, #?
    'ArrayLength'       : T_Integer_,
    'ByteOffset'        : T_Integer_,
    'TypedArrayName'    : T_String,

    # 10066: Table 29: Internal Slots of Module Namespace Exotic Objects
    'Module'     : T_Module_Record,
    'Exports'    : ListType(T_String),

    # 9.5 Proxy Object Internal Methods and Internal Slots
    'ProxyHandler' : T_Object | T_Null,
    'ProxyTarget'  : T_Object | T_Null,

    # 27137: Properties of Boolean Instances NO TABLE
    'BooleanData' : T_Boolean,

    # 30688
    'DateValue': T_Number,

    # 30738: Table 46: Internal Slots of String Iterator Instances
    'IteratedString' : T_String,
    'StringIteratorNextIndex': T_Integer_,

    # 32711: Properties of RegExp Instances NO TABLE
    'RegExpMatcher'  : ProcType([T_String, T_Integer_], T_MatchResult),
    'OriginalSource' : T_String,
    'OriginalFlags'  : T_String,

    # 34123: Table 48: Internal Slots of Array Iterator Instances
    'IteratedObject'         : T_Object,
    'ArrayIteratorNextIndex' : T_Integer_,
    'ArrayIterationKind'     : T_String,

    # 35373 + 37350 NO TABLE
    'ByteLength' : T_Integer_,

    # 35719: Table 50: Internal Slots of Map Iterator Instances
    'Map'              : T_Object,
    'MapNextIndex'     : T_Integer_,
    'MapIterationKind' : T_String,

    # 36073: Table 51: Internal Slots of Set Iterator Instances
    'IteratedSet'      : T_Object,
    'SetNextIndex'     : T_Integer_,
    'SetIterationKind' : T_String,

    # 36817: Properties of the ArrayBuffer Instances
    # 36973: Properties of the SharedArrayBuffer Instances
    # NO TABLE
    'ArrayBufferData': T_Data_Block | T_Shared_Data_Block | T_Null,
        # XXX but IsSharedArrayBuffer() ensures that ArrayBufferData is a Shared Data Block
    'ArrayBufferByteLength' : T_Integer_,
    'ArrayBufferDetachKey'  : T_Tangible_, # could be anything, really

    # 38581: Table 56: Internal Slots of Generator Instances
    'GeneratorState'  : T_Undefined | T_String,
    'GeneratorContext': T_execution_context,

    # 38914: 25.4.1.3.1 ish, NO TABLE
    'Promise'        : T_Object,
    'AlreadyResolved': T_boolean_value_record_,

    # 39021
    'MapData' : ListType(T_MapData_record_),

    # 39034: NO TABLE
    'Capability' : T_PromiseCapability_Record,

    # 39537: Table 59: Internal Slots of Promise Instances
    'PromiseState'           : T_String,
    'PromiseResult'          : T_Tangible_,
    'PromiseFulfillReactions': ListType(T_PromiseReaction_Record) | T_Undefined,
    'PromiseRejectReactions' : ListType(T_PromiseReaction_Record) | T_Undefined,
    'PromiseIsHandled'       : T_Boolean,

    # 39763
    'SetData'    : ListType(T_Tangible_ | T_empty_),

    # 39781 AsyncFunction Awaited Fulfilled/Rejected NO TABLE
    'AsyncContext' : T_execution_context,

    # 39817 `Promise.all` Resolve Element Functions
    'Index'             : T_Integer_,
    'Values'            : ListType(T_Tangible_),
    'Capability'        : T_PromiseCapability_Record,
    'RemainingElements' : T_integer_value_record_,
    'AlreadyCalled'     : T_boolean_value_record_,

    # 40093:
    'WeakMapData' : ListType(T_MapData_record_),

    # 40188: NO TABLE
    'Done'              : T_Boolean,

    # 40254:
    'WeakSetData' : ListType(T_Tangible_ | T_empty_),

    # 41310: Table N: Internal Slots of Async-from-Sync Iterator Instances
    'SyncIteratorRecord' : T_iterator_record_,

    # 41869: Table N: Internal Slots of AsyncGenerator Instances
    'AsyncGeneratorState'   : T_Undefined | T_String,
    'AsyncGeneratorContext' : T_execution_context,
    'AsyncGeneratorQueue'   : ListType(T_AsyncGeneratorRequest_Record),

    # 42071 mention, NO TABLE
    'Generator' : T_AsyncGenerator_object_,

    # 44654 mention
    'Constructor' : T_constructor_object_,
    'OnFinally'   : T_function_object_,

    # 45286 mention
    'RevocableProxy' : T_Proxy_exotic_object_ | T_Null,
}

main()

# vim: sw=4 ts=4 expandtab