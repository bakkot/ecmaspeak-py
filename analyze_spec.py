#!/usr/bin/python3

# ecmaspeak-py/analyze_spec.py:
# Perform an initial static analysis of the spec.
#
# Copyright (C) 2018  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, re, pdb
from collections import defaultdict, OrderedDict

import HTML, Section, emu_grammars
import shared
from shared import stderr, header, msg_at_posn, spec

def main():
    if len(sys.argv) != 3:
        stderr("usage: %s <output-dir> <spec.html>" % sys.argv[0])
        sys.exit(1)

    outdir = sys.argv[1]
    spec_path = sys.argv[2]

    shared.register_output_dir(outdir)

    # kludgey to assign to another module's global:
    shared.g_warnings_f = shared.open_for_output('warnings')

    spec.read_source_file(spec_path)

    spec.doc_node = HTML.parse_and_validate()

    # It feels like it would make more sense to check characters and indentation
    # before paring/checking markup, because they're more 'primitive' than markup.
    # But when it comes to fixing errors, you should make sure
    # you've got the markup correct before fiddling with indentation.
    # So to encourage that, have markup errors appear before indentation errors,
    # i.e. run the markup checks before indentation checks.
    # (Not sure about characters.)
    check_indentation()
    check_trailing_whitespace()
    check_characters()

    check_ids()

    check_tables()
    Section.make_and_check_sections()
    emu_grammars.do_stuff_with_grammars()
    check_sdo_coverage()

    spec.save()

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def expand_imports(text):
    def repl_import(mo):
        (import_start, href, import_end) = mo.groups()
        t = open(href,'r').read()
        return import_start + t + import_end
    return re.sub(
        r'(<emu-import href="([^"]+)">)(</emu-import>)',
        repl_import,
        text
    )

def handle_insdel(text):

    # If a <del> element encloses all the non-whitespace content of a line,
    # delete the whole line.
    text = re.sub(r'\n *<del>[^<>]*</del> *(?=\n)', '', text)

    # Similarly of it encloses the body of an algorithm-step.
    text = re.sub(r'\n *1\. <del>.*</del>(?=\n)', '', text)
    # Insufficient to use "<del>[^<>]*</del>" because of steps with <emu-xref>
    # "<del>.*</del>" would fail if more than one <del> on a line,
    # but haven't seen that yet.

    # Otherwise, delete just the <del> element.
    text = re.sub(r'<del>.*?</del>', '', text)

    # And dissolve the <ins> </ins> tags.
    text = re.sub(r'</?ins>', '', text)

    return text

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_indentation():

    # ------------------------------------------------------------------------------

    class Block:
        def __init__(self, parent, ind, head_line_csp, head_line):
            self.parent = parent
            if parent: parent.children.append(self)
            self.ind = ind
            self.head_line_csp = head_line_csp
            self.head_line = head_line
            # These will get set later:
            self.children = []
            self.tail_line_csp = None
            self.tail_line = None
            self.next_line_num = None

        def is_root(self):
            assert (self.parent is None) == (self.ind == -2) == (self.head_line == '')
            return (self.parent is None)

        def each_descendant_that_startswith(self, st):
            if self.head_line.startswith(st):
                yield self
            for child in self.children:
                for d in child.each_descendant_that_startswith(st):
                    yield d

        def source_text(self):
            return (
                (' '*self.ind) + self.head_line + '\n'
                +
                ''.join(
                    child.source_text()
                    for child in self.children
                )
                +
                (
                    (' '*self.ind) + self.tail_line + '\n'
                    if
                    self.tail_line is not None
                    else
                    ''
                )
            )

    indented_line_reo = re.compile(r'(?m)^( *)(.*)$')

    def blockify(start, end, report_errors):

        line_ = []
        for mo in indented_line_reo.finditer(spec.text, start, end):
            ind = mo.end(1) - mo.start(1)
            csp = mo.start(2)
            content = mo.group(2)
            if 0:
                if ind % 2 != 0:
                    stderr("Warning: odd indentation (%d): %s" % (ind, content))
                # It'll be flagged below anyhow
            line_.append( (ind, csp, content) )

        # "CSP" = "content-start position"
        # i.e. the position (within spec.text)
        # of the start of content (end of indentation) of some line.

        line_num = 1

        def complete_block(parent):
            # Gather the children of `parent`, if any,
            # and its tail-line, if any.
            # After this function returns,
            # line_[line_num - 1] will be the next line after `parent`.

            nonlocal line_, line_num

            if parent.head_line == '<pre>':
                in_a_pre = True
                expected_end_tag = '</pre>'
            elif parent.head_line == '<pre><code class="javascript">':
                in_a_pre = True
                expected_end_tag = '</code></pre>'
            else:
                in_a_pre = False
                mo = re.match(r'^<([\w-]+)', parent.head_line)
                if mo:
                    # Note that this also matches if the head_line is (e.g.) <p>...</p>,
                    # when we shouldn't be looking for an end tag on a subsequent line.
                    # However, unless the file's indentation is off,
                    # the question won't arise.
                    # (We have to be loose because of
                    #     <emu-eqn>Foo()..
                    #     </emu-eqn>
                    element_name = mo.group(1)
                    expected_end_tag = '</%s>' % element_name
                else:
                    expected_end_tag = None

            while True:
                if line_num > len(line_):
                    break

                (ind, csp, linebody) = line_[line_num - 1]

                if in_a_pre:
                    # In a <pre>, child-lines don't follow the normal indentation rules.
                    # Also, we don't bother to structure them in a hierarchy,
                    # even though they might be nicely indented
                    # (relative to each other).
                    if ind == parent.ind and linebody == expected_end_tag:
                        # the <pre> is ending
                        parent.tail_line_csp = csp
                        parent.tail_line = linebody
                        line_num += 1
                        break
                    else:
                        # the <pre> continues
                        child = Block(parent, ind, csp, linebody)
                        line_num += 1

                else:
                    if linebody == '':
                        # This is a blank line
                        if line_num == len(line_):
                            # It's the last line,
                            # so don't bother creating a Block for it.
                            pass
                        else:
                            child = Block(parent, ind, csp, linebody)
                            # It can't have children or a tail-line,
                            # so calling complete_block() would just confuse things.
                        line_num += 1

                    elif ind > parent.ind:
                        # This line is indented wrt the parent.
                        if ind != parent.ind + 2 and report_errors:
                            msg_at_posn(csp, "expected indent=%d, got %d" %
                                (parent.ind+2, ind)
                            )

                        # It is the start of a child of the parent.
                        child = Block(parent, ind, csp, linebody)
                        line_num += 1
                        complete_block(child)

                    elif ind == parent.ind:
                        # This is either the tail-line of the parent
                        # or the start of a sibling of the parent.
                        if linebody.startswith('</'):
                            # Tail-line!
                            if linebody != expected_end_tag and report_errors:
                                msg_at_posn(csp, "expected '%s', got '%s'" %
                                    (expected_end_tag, linebody)
                                )
                            parent.tail_line_csp = csp
                            parent.tail_line = linebody
                            line_num += 1
                            break
                        else:
                            # start of sibling of parent
                            break

                    elif ind < parent.ind:
                        break

                    else:
                        assert 0

            parent.next_line_num = line_num
            return

        root = Block(None, -2, 0, '')
        complete_block(root)
        assert line_num == 1 + len(line_)
        return root

    # -------------------------------

    stderr("check_indentation...")
    header("checking indentation...")
    blockify(0, len(spec.text), True)

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_trailing_whitespace():
    stderr("checking trailing whitespace...")
    header("checking trailing whitespace...")
    for mo in re.finditer(r'(?m)[ \t]+$', spec.text):
        posn = mo.start()
        msg_at_posn(posn, "trailing whitespace")

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_characters():
    stderr("checking characters...")
    header("checking characters...")
    for mo in re.finditer(r'[^\n -~]', spec.text):
        posn = mo.start()
        character = spec.text[posn]
        if character in ascii_replacement:
            suggestion = ": maybe change to %s" % ascii_replacement[character]
        else:
            suggestion = ''
        msg_at_posn(posn, "non-ASCII character U+%04x%s" %
            (ord(character), suggestion) )

ascii_replacement = {
    '\u00ae': '&reg;',    # REGISTERED SIGN
    '\u00ab': '&laquo;',  # LEFT-POINTING DOUBLE ANGLE QUOTATION MARK
    '\u00bb': '&raquo;',  # RIGHT-POINTING DOUBLE ANGLE QUOTATION MARK
    '\u2019': "'",        # RIGHT SINGLE QUOTATION MARK
    '\u2026': '&hellip;', # HORIZONTAL ELLIPSIS
    '\u2265': '&ge;',     # GREATER-THAN OR EQUAL TO
}

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_ids():
    header("checking ids...")

    node_with_id_ = OrderedDict()

    def gather_def_ids(node):
        if 'id' in node.attrs:
            defid = node.attrs['id']

            if defid in node_with_id_:
                msg_at_posn(node.start_posn, f"duplicate id: '{defid}'")

            node_with_id_[defid] = node

        for child in node.children:
            gather_def_ids(child)
    
    gather_def_ids(spec.doc_node)

    # -------------------------------------------------------------

    refids = set()

    def check_ref_ids(refnode):
        if refnode.element_name == 'emu-xref':
            href = refnode.attrs['href']
            assert href.startswith('#')
            refid = href[1:]
            refids.add(refid)

            if refid in node_with_id_:

                defnode = node_with_id_[refid]
                if defnode.element_name in ['emu-clause', 'emu-annex', 'emu-table']:
                    pass
                elif defnode.element_name == 'dfn':
                    deftext = defnode.inner_source_text()
                    reftext = refnode.inner_source_text()
                    assert deftext != ''
                    if reftext != '' and reftext.lower() != deftext.lower():
                        # Auto-linking would fail to make `reftext` into a link?
                        # So we have to use an emu-xref?
                        pass
                    else:
                        msg_at_posn(refnode.start_posn, f"emu-xref used when auto-linking would work: '{refid}'")
                else:
                    assert 0, defnode.element_name

            else:
                if refid in [
                    'table-binary-unicode-properties',
                    'table-nonbinary-unicode-properties',
                    'table-unicode-general-category-values',
                    'table-unicode-script-values',
                ]:
                    # Those ids are declared in emu-imported files.
                    pass

                elif refid in [
                    'prod-annexB-LegacyOctalEscapeSequence',
                    'prod-annexB-LegacyOctalIntegerLiteral',
                    'prod-annexB-NonOctalDecimalIntegerLiteral',
                ]:
                    # These don't exist in the source file,
                    # but are generated during the rendering process?
                    pass

                else:
                    msg_at_posn(refnode.start_posn, f"emu-xref refers to nonexistent id: {refid}")

        for child in refnode.children:
            check_ref_ids(child)
    
    check_ref_ids(spec.doc_node)

    # -------------------------------------------------------------

    for (id, defnode) in node_with_id_.items():
        if id in refids: continue

        # `id` was not referenced.

        if id in ['metadata-block', 'ecma-logo']:
            # Actually, it *is* referenced, but from the CSS.
            continue

        if defnode.element_name in ['emu-intro', 'emu-clause', 'emu-annex']:
            # It's okay if the id isn't referenced:
            # it's more there for the ToC and for inbound URLs.
            continue

        if defnode.element_name in ['emu-figure', 'emu-table']:
            # The text might refer to it as "the following figure/table",
            # so don't expect an exolicit reference to the id.
            # So you could ask, why bother giving an id then?
            # I suppose for inbound URLs, and consistency?
            continue

        if defnode.element_name in ['dfn', 'emu-eqn']:
            # It's likely that the rendering process will create references
            # to this id.
            continue

        msg_at_posn(defnode.start_posn, f"id declared but not referenced: '{id}'")

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_tables():
    stderr('check_tables...')
    header("checking tables...")
    for et in spec.doc_node.each_descendant_named('emu-table'):
        a_caption = et.attrs.get('caption', None)
        caption_children = [c for c in et.each_child_named('emu-caption')]
        if len(caption_children) == 0:
            e_caption = None
        elif len(caption_children) == 1:
            [emu_caption] = caption_children
            e_caption = emu_caption.inner_source_text().strip()
        else:
            assert 0
        # ----
        if a_caption and not e_caption:
            caption = a_caption
        elif e_caption and not a_caption:
            caption = e_caption
        else:
            assert 0, (a_caption, e_caption)

        if 'id' not in et.attrs:
            msg_at_posn(et.start_posn, f'no id attribute for table with caption "{caption}"')

        header_tr = [tr for tr in et.each_descendant_named('tr')][0]
        header_line = '; '.join(th.inner_source_text().strip() for th in header_tr.each_descendant_named('th'))
        if 'Field' in caption:
            # print(header_line, ':', caption)
            if re.match(r'^(.+) Fields$', caption):
                pass
            elif re.match(r'^Additional Fields of (.+)$', caption):
                pass
            else:
                assert 0, caption

        elif 'Slot' in caption:
            if re.match(r'^Internal Slots of (.+)$', caption):
                pass
            else:
                assert 0

        elif 'Method' in caption:
            if 'Internal Methods' in caption:
                assert caption in ['Essential Internal Methods', 'Additional Essential Internal Methods of Function Objects']
                assert header_line == 'Internal Method; Signature; Description'
            elif 'Records' in caption:
                assert re.fullmatch(r'(Abstract|Additional) Methods of .+ Records', caption)
                assert header_line == 'Method; Purpose'
            elif caption == 'Proxy Handler Methods':
                assert header_line == 'Internal Method; Handler Method'
            else:
                assert 0

        elif 'Properties' in caption:
            assert re.fullmatch(r'<i>\w+</i> Interface( (Required|Optional))? Properties', caption)
            assert header_line == 'Property; Value; Requirements'

        else:
            # print('>>>', header_line, '---', caption)
            pass

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

def check_sdo_coverage():
    global sdo_coverage_map
    sdo_coverage_map = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))

    collect_sdo_coverage_info()
    analyze_sdo_coverage_info()

# ------------------------------------------------------------------------------

def collect_sdo_coverage_info():
    for s in spec.doc_node.each_descendant_that_is_a_section():
        if s.section_kind == 'syntax_directed_operation':
            if s.section_num.startswith('B.'):
                # Taking Annex B into account is difficult,
                # because it modifies the main-body grammar,
                # so RHS-indexes aren't always the same.
                # XXX For now, just skip it.
                continue

            if s.section_title == 'Static Semantics: HasCallInTailPosition':
                assert len(s.block_children) == 2
                assert s.block_children[0].element_name == 'p'
                assert s.block_children[1].element_name == 'emu-note'
                assert len(s.section_children) == 2
                collect_sdo_coverage_info_for_section(s.section_children[0], 'HasCallInTailPosition')
                collect_sdo_coverage_info_for_section(s.section_children[1], 'HasCallInTailPosition')

            elif s.section_title == 'Static Semantics: TV and TRV':
                # Each rule specifies while SDO(s) it pertains to.
                collect_sdo_coverage_info_for_section(s, None)

            elif s.parent.section_title == 'Pattern Semantics':
                collect_sdo_coverage_info_for_section(s, 'regexp-eval')

            else:
                mo = re.fullmatch('(Static|Runtime) Semantics: (\S+)', s.section_title)
                assert mo
                collect_sdo_coverage_info_for_section(s, mo.group(2))

def collect_sdo_coverage_info_for_section(section, sdo_name):            

    # XXX: The following code overlaps
    # add_defns_from_sdo_section() in STA.py.
    # Probably it would make more sense to be doing this over there.

    # cen = "child element names"
    cen_list = [
        c.element_name
        for c in section.block_children
    ]
    cen_set = set(cen_list)
    cen_str = ' '.join(cen_list)

    if 'ul' in cen_set:
        assert cen_set <= set(['ul', 'p', 'emu-table', 'emu-note'])
        # Each <li> in the <ul> is an "inline SDO".

        for ul in section.block_children:
            if ul.element_name != 'ul': continue
            for li in ul.children:
                if li.element_name != 'li': continue

                li_ist = li.inner_source_text().strip()
                if re.match(r'it is not `0`|there is a nonzero digit', li_ist):
                    # This is the <ul> at the end of 
                    # 7.1.3.1.1 Runtime Semantics: MV
                    # and
                    # 11.8.3.1 Static Semantics: MV
                    # We're not interested in it.
                    # print(section.section_num, section.section_title, section.section_id)
                    continue

                if li_ist == 'The TRV of a |HexDigit| is the SV of the |SourceCharacter| that is that |HexDigit|.':
                    # XXX not sure how to handle this yet. For now, ignore it.
                    continue

                (emu_grammars, text) = extract_grammars(li)

                assert emu_grammars

                if re.fullmatch(r'The TV and TRV of <G> is .+', text):
                    sdo_names = ['TV', 'TRV']
                else:
                    mo = re.fullmatch(r'The (\w+) of <G>( or of <G>)* is .+', text)
                    assert mo
                    sdo_names = [mo.group(1)]

                for sdo_name in sdo_names:
                    for emu_grammar in emu_grammars:
                        collect_sdo_coverage_info_for_emu_grammar(sdo_name, emu_grammar)

    elif 'emu-grammar' in cen_set:
        assert cen_set <= set(['emu-grammar', 'emu-alg', 'emu-note', 'emu-see-also-para', 'emu-table', 'p'])
        # Each <emu-grammar> + <emu-alg> pair in an SDO unit.

        for (i,c) in enumerate(section.block_children):
            if c.element_name == 'emu-grammar':
                assert section.block_children[i+1].element_name in ['emu-alg', 'p']
                collect_sdo_coverage_info_for_emu_grammar(sdo_name, c)

    elif 'emu-alg' in cen_set:
        assert cen_set <= set(['emu-alg', 'p', 'emu-note'])
        # Each <p> + <emu-alg> pair is an SDO unit.
        assert sdo_name in ['Evaluation', 'regexp-eval']

        # print(cen_str)
        for c in section.block_children:
            if c.element_name == 'p':
                (emu_grammars, text) = extract_grammars(c)
                if text.startswith('With parameter'):
                    # ignore it
                    pass
                elif text in [
                    'The production <G> evaluates as follows:',
                    'The production <G>, where @ is one of the bitwise operators in the productions above, is evaluated as follows:',
                    'The production <G> evaluates by returning the CharSet containing all Unicode code points included in the CharSet returned by |UnicodePropertyValueExpression|.',
                    'The production <G> evaluates by returning the CharSet containing all Unicode code points not included in the CharSet returned by |UnicodePropertyValueExpression|.',
                ]:
                    [emu_grammar] = emu_grammars
                    collect_sdo_coverage_info_for_emu_grammar(sdo_name, emu_grammar)
                else:
                    assert 0, text

    else:
        print(section.section_num, section.section_title, section.section_id)
        print(cen_str)
        assert 0

def extract_grammars(x):
    emu_grammars = []
    text = ''
    for c in x.children:
        if c.element_name == 'emu-grammar':
            emu_grammars.append(c)
            text += '<G>'
        else:
            text += c.source_text()
    return (emu_grammars, text.strip())

def collect_sdo_coverage_info_for_emu_grammar(sdo_name, emu_grammar):
    assert type(sdo_name) == str
    assert emu_grammar.element_name == 'emu-grammar'

    if emu_grammar.attrs.get('type', 'reference') == 'example':
        assert emu_grammar.inner_source_text() == 'A : A @ B'
        # skip it?
        return

    for (lhs_nt, def_i, optionals) in emu_grammar.summary:
        sdo_coverage_map[sdo_name][lhs_nt][def_i].append(optionals)

# ------------------------------------------------------------------------------

def analyze_sdo_coverage_info():
    coverage_f = shared.open_for_output('sdo_coverage')
    def put(*args): print(*args, file=coverage_f)

    for (sdo_name, coverage_info_for_this_sdo) in sorted(sdo_coverage_map.items()):

        if sdo_name == 'Contains':
            # XXX can we do anything useful here?
            # we could check for conflicting defs
            continue

        nt_queue = sorted(coverage_info_for_this_sdo.keys())
        def queue_ensure(nt):
            if nt not in nt_queue: nt_queue.append(nt)

        for lhs_nt in nt_queue:
            # print('    ', lhs_nt)

            nt_info = emu_grammars.info_for_nt_[lhs_nt]
            assert 'A' in nt_info.def_occs
            (_, _, def_rhss) = nt_info.def_occs['A']

            for (def_i, def_rhs) in enumerate(def_rhss):
                GNTs = [r for r in def_rhs if r.T == 'GNT']
                oGNTs = [gnt for gnt in GNTs if gnt.o]
                nGNTs = [gnt for gnt in GNTs if not gnt.o]

                for opt_combo in each_opt_combo(oGNTs):
                    opt_combo_str = ''.join(omreq[0] for (nt, omreq) in opt_combo)
                    rules = sdo_rules_that_handle(sdo_name, lhs_nt, def_i, opt_combo)
                    if len(rules) == 1:
                        # great
                        pass
                    elif len(rules) > 1:
                        put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} {opt_combo_str} is handled by {len(rules)} rules!")
                    elif is_sdo_coverage_exception(sdo_name, lhs_nt, def_i):
                        # okay
                        pass
                    else:
                        nts = [gnt.n for gnt in nGNTs] + required_nts_in(opt_combo)
                        if len(nts) == 1:
                            # The rule for chain productions applies.
                            # So recurse on the rhs non-terminal.
                            [nt] = nts

                            # DEBUG:
                            # put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} chains to {nt}")
                            # That creates a lot of output, but it's really useful
                            # when you're trying to figure out why "needs a rule" messages appear.

                            queue_ensure(nt)
                        else:
                            put(f"{sdo_name} for {lhs_nt} rhs+{def_i+1} {opt_combo_str} needs a rule")

    coverage_f.close()

def each_opt_combo(oGNTs):
    N = len(oGNTs)
    if N == 0:
        yield []
    elif N == 1:
        [a] = oGNTs
        yield [(a.n, 'omitted' )]
        yield [(a.n, 'required')]
    elif N == 2:
        [a, b] = oGNTs
        yield [(a.n, 'omitted' ), (b.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'required')]
    elif N == 3:
        [a, b, c] = oGNTs
        yield [(a.n, 'omitted' ), (b.n, 'omitted' ), (c.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'omitted' ), (c.n, 'required')]
        yield [(a.n, 'omitted' ), (b.n, 'required'), (c.n, 'omitted' )]
        yield [(a.n, 'omitted' ), (b.n, 'required'), (c.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'omitted' ), (c.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'omitted' ), (c.n, 'required')]
        yield [(a.n, 'required'), (b.n, 'required'), (c.n, 'omitted' )]
        yield [(a.n, 'required'), (b.n, 'required'), (c.n, 'required')]
    else:
        assert 0

def required_nts_in(opt_combo):
    return [nt for (nt, omreq) in opt_combo if omreq == 'required']

def sdo_rules_that_handle(sdo_name, lhs_nt, def_i, opt_combo):
    coverage_info_for_this_sdo = sdo_coverage_map[sdo_name]
    coverage_info_for_this_nt = coverage_info_for_this_sdo[lhs_nt]
    if def_i not in coverage_info_for_this_nt: return []
    list_of_opt_covers = coverage_info_for_this_nt[def_i]
    covers = []
    for opt_cover in list_of_opt_covers:
        # print(opt_cover, covers_opt_combo(opt_cover, opt_combo))
        if covers_opt_combo(opt_cover, opt_combo):
            covers.append(opt_cover)
    return covers

def covers_opt_combo(opt_cover, opt_combo):
    assert len(opt_cover) == len(opt_combo)
    for (cover_item, combo_item) in zip(opt_cover, opt_combo):
        assert cover_item[0] == combo_item[0]
        assert cover_item[1] in ['omitted', 'required', 'either']
        assert combo_item[1] in ['omitted', 'required']
        if cover_item[1] == combo_item[1]:
            # easy
            pass
        elif cover_item[1] == 'either':
            # covers either
            pass
        else:
            # incompatible
            return False
    return True

def is_sdo_coverage_exception(sdo_name, lhs_nt, def_i):
    # Looking at the productions that share a LHS
    # (or equivalently, the RHSs of a multi-production),
    # it's typically the case that if an SDO can be invoked on one,
    # then it can be invoked on all.
    # And thus, if you see an SDO defined on one,
    # you should expect to see it defined on all,
    # either explicitly, or implicitly via chain productions.
    #
    # This function identifies exceptions to that rule of thumb.

    if sdo_name == 'CharacterValue' and lhs_nt == 'ClassEscape' and def_i == 2:
        # Invocations of this SDO on ClassAtom and ClassAtomNoDash
        # are guarded by `IsCharacterClass ... is *false*`.
        # This excludes the `ClassEscape :: CharacterClassEscape` production.
        return True

    if (
        sdo_name == 'CoveredParenthesizedExpression'
        and
        lhs_nt == 'CoverParenthesizedExpressionAndArrowParameterList'
        and
        def_i != 0
    ):
        # For this SDO, we're guaranteed (by early error) that rhs must be def_i == 0,
        # so the SDO doesn't need to be defined for def_i != 0.
        return True

    if sdo_name == 'DefineMethod' and lhs_nt == 'MethodDefinition' and def_i != 0:
        # "Early Error rules ensure that there is only one method definition named `"constructor"`
        # and that it is not an accessor property or generator definition."
        # (or AsyncMethod)
        # See SpecialMethod.
        return True

    if sdo_name == 'Evaluation' and lhs_nt == 'ClassDeclaration' and def_i == 1:
        # "ClassDeclaration : `class` ClassTail</emu-grammar>
        # only occurs as part of an |ExportDeclaration| and is never directly evaluated."
        return True

    if sdo_name == 'HasName':
        # Invocations of this SDO are guarded by `IsFunctionDefinition of _expr_ is *true*`,
        # so the SDO doesn't need to be defined for most kinds of expr.
        # Assume that it's defined for all that need it.
        return True

    if sdo_name == 'IsConstantDeclaration' and lhs_nt == 'ExportDeclaration' and def_i in [0,1,2,3]:
        # LexicallyScopedDeclarations skips these, so IsConstantDeclaration won't be invoked on them.
        return True

    if (
        sdo_name in ['PropName', 'PropertyDefinitionEvaluation']
        and 
        lhs_nt == 'PropertyDefinition'
        and
        def_i == 1
    ):
        # "Use of |CoverInitializedName| results in an early Syntax Error in normal contexts..."
        return True

    # ----------

    if (
        sdo_name == 'Evaluation'
        and
        lhs_nt in [
            'BitwiseANDExpression',
            'BitwiseXORExpression',
            'BitwiseORExpression',
        ]
        and
        def_i == 1
    ):
        # This is handled by the stupid "A : A @ B" rule.
        return True

    return False

# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
# XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

if 1:
    main()
else:
    import cProfile
    cProfile.run('main()', '_prof')
    # python3 -m pstats
    # read _prof
    # sort time
    # stats 10

# vim: sw=4 ts=4 expandtab columns=86