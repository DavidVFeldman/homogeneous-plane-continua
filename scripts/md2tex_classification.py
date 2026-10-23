#!/usr/bin/env python3
"""Convert doc/exposition/classification-path.md to LaTeX (pdflatex-compatible, ASCII output)."""
import re, sys

SRC = sys.argv[1] if len(sys.argv) > 1 else 'doc/exposition/classification-path.md'
DST = sys.argv[2] if len(sys.argv) > 2 else 'doc/exposition/classification-path.tex'

GREEK = {
    'α': r'\alpha', 'β': r'\beta', 'γ': r'\gamma', 'δ': r'\delta', 'ε': r'\varepsilon',
    'ζ': r'\zeta', 'η': r'\eta', 'θ': r'\theta', 'κ': r'\kappa', 'λ': r'\lambda',
    'μ': r'\mu', 'ν': r'\nu', 'ξ': r'\xi', 'π': r'\pi', 'ρ': r'\rho', 'σ': r'\sigma',
    'τ': r'\tau', 'φ': r'\varphi', 'χ': r'\chi', 'ψ': r'\psi', 'ω': r'\omega',
    'Γ': r'\Gamma', 'Δ': r'\Delta', 'Θ': r'\Theta', 'Λ': r'\Lambda', 'Σ': r'\sum',
    'Φ': r'\Phi', 'Ψ': r'\Psi', 'Ω': r'\Omega', 'Π': r'\Pi',
}
SPECIAL_LETTERS = {
    'ℝ': r'\mathbb{R}', 'ℂ': r'\mathbb{C}', 'ℤ': r'\mathbb{Z}', 'ℕ': r'\mathbb{N}',
    'ℚ': r'\mathbb{Q}', '𝒫': r'\mathcal{P}', '𝔇': r'\mathfrak{D}', '𝒦': r'\mathcal{K}',
    'ℓ': r'\ell', '∅': r'\emptyset', '∞': r'\infty',
}
SUBS = {'₀': '0', '₁': '1', '₂': '2', '₃': '3', '₄': '4', '₅': '5', '₆': '6', '₇': '7',
        '₈': '8', '₉': '9', '₊': '+', '₋': '-', 'ᵢ': 'i', 'ⱼ': 'j', 'ₙ': 'n', 'ₖ': 'k'}
SUPS = {'⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁻': '-', '⁺': '+', 'ᶜ': 'c',
        'ⁿ': 'n'}
OPS = {
    '→': r'\to', '⊆': r'\subseteq', '∈': r'\in', '∖': r'\setminus', '∪': r'\cup',
    '−': '-', '×': r'\times', '≠': r'\neq', '∩': r'\cap', '≥': r'\geq', '≤': r'\leq',
    '⇒': r'\Rightarrow', '·': r'\cdot', '∘': r'\circ', '⊇': r'\supseteq', '⊂': r'\subset',
    '⋂': r'\bigcap', '⋃': r'\bigcup', '⊊': r'\subsetneq', '∋': r'\ni', '∌': r'\not\ni',
    '∉': r'\notin', '≅': r'\cong', '⊄': r'\not\subset', '⊔': r'\sqcup', '↦': r'\mapsto',
    '±': r'\pm', '⇐': r'\Leftarrow', '=': '=', '<': '<', '>': '>', '+': '+', '/': '/',
    '|': '|', '≈': r'\approx', '⊕': r'\oplus',
}
NUMOPS = None  # filled below
FUNCS = {'exp': r'\exp', 'closure': r'\operatorname{closure}', 'Cl': r'\operatorname{Cl}',
         'diam': r'\operatorname{diam}', 'dist': r'\operatorname{dist}', 'sup': r'\sup',
         'log': r'\log', 'id': r'\mathrm{id}', 'inf': r'\inf'}
NUMOPS = set(OPS) - set('⇒⇐')
TEXT_LABEL_WORDS = {'Theorem', 'Theorems', 'Lemma', 'Lemmas', 'Axiom', 'Proposition',
                    'Corollary', 'Part', 'Claim', 'Case', 'Step', 'Section', 'Condition'}

MATHLETTER = 'A-Za-z' + ''.join(GREEK) + ''.join(SPECIAL_LETTERS)
WORDCH = 'A-Za-z0-9' + ''.join(GREEK) + ''.join(SPECIAL_LETTERS) + 'öéèüäáíó'
SUBSUP = ''.join(SUBS) + ''.join(SUPS) + '′'
BR = r'\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}'
SUFFIX = rf"(?:[{SUBSUP}]|'(?![A-Za-z])|_{BR}|_[A-Za-z0-9{''.join(GREEK)}]|\^{BR}|\^[A-Za-z0-9])"

TOKEN_RE = re.compile(
    rf"(?P<ph>\x00\d+\x00)"
    rf"|(?P<bold>\*\*)|(?P<em>\*)"
    rf"|(?P<word>\d+(?:\.\d+)+(?![0-9A-Za-z])|[{WORDCH}]+'s(?![A-Za-z])|[{WORDCH}]+(?:{SUFFIX})*)"
    rf"|(?P<supstd>[{SUBSUP}]+)"
    rf"|(?P<space>\s+)"
    rf"|(?P<op>[⋂⋃](?:_{BR}|_[A-Za-z0-9])?|[{re.escape(''.join(OPS))}])"
    rf"|(?P<open>[(\[{{])|(?P<close>[)\]}}])"
    rf"|(?P<other>.)"
)


class Tok:
    def __init__(self, kind, text, sub=None):
        self.kind = kind      # see classify
        self.text = text
        self.sub = sub        # for groups
        self.cat = None       # M, O, N, S, B, C(colon), E(ellipsis)

    def __repr__(self):
        return f'{self.kind}:{self.text!r}:{self.cat}'


def split_word(w):
    if re.fullmatch(r'\d+(\.\d+)+', w):
        return w, ''
    m = re.match(rf"([{WORDCH}]+)((?:{SUFFIX})*)$", w)
    return m.group(1), m.group(2)


def render_suffix(suf):
    out = ''
    subs, sups, primes = [], [], ''
    i = 0
    while i < len(suf):
        c = suf[i]
        if c in SUBS:
            subs.append(SUBS[c]); i += 1
        elif c in SUPS:
            sups.append(SUPS[c]); i += 1
        elif c in "′'":
            primes += "'"; i += 1
        elif c in '_^':
            if suf[i + 1] == '{':
                depth, j = 0, i + 1
                while True:
                    if suf[j] == '{': depth += 1
                    elif suf[j] == '}':
                        depth -= 1
                        if depth == 0: break
                    j += 1
                inner = math_str(suf[i + 2:j])
                i = j + 1
            else:
                inner = math_str(suf[i + 1]); i += 2
            (subs if c == '_' else sups).append(inner)
        else:
            raise ValueError(f'bad suffix {suf!r}')
    out = primes
    if subs:
        s = ''.join(subs)
        out += '_' + (s if len(s) == 1 else '{' + s + '}')
    if sups:
        s = ''.join(sups)
        out += '^' + (s if len(s) == 1 else '{' + s + '}')
    return out


def letter_tex(c):
    if c in GREEK: return GREEK[c]
    if c in SPECIAL_LETTERS: return SPECIAL_LETTERS[c]
    return c


def math_str(s):
    """Render a string that is known to be entirely mathematical."""
    toks = tokenize(s)
    return render_math(toks)


def tokenize(s):
    toks = []
    for m in TOKEN_RE.finditer(s):
        k = m.lastgroup
        toks.append(Tok(k, m.group(k)))
    return toks


MATHWORDS = {'AB', 'ABCDA', 'QN'}


def is_math_word(core):
    if core in MATHWORDS:
        return True
    if len(core) == 1 and (core in GREEK or core in SPECIAL_LETTERS or core.isascii() and core.isalpha()):
        return True
    if any(c in GREEK or c in SPECIAL_LETTERS for c in core) and len(core) <= 6:
        return True
    return False


def render_math(toks):
    out = []
    for t in toks:
        if t.kind == 'group':
            o, inner, c = t.sub
            ot = r'\{' if o.text == '{' else o.text
            ct = r'\}' if c.text == '}' else c.text
            out.append(ot + render_math(inner) + ct)
        elif t.kind == 'word':
            core, suf = split_word(t.text)
            if core in FUNCS:
                out.append(FUNCS[core] + ' ')
                if suf: out.append(render_suffix(suf))
            elif core.isdigit() or re.fullmatch(r'\d+(\.\d+)+|\d+[a-z]', core):
                out.append(core + render_suffix(suf))
            elif is_math_word(core):
                lt = ''.join(letter_tex(c) + (' ' if letter_tex(c).startswith('\\') else '') for c in core)
                if suf:
                    lt = lt.rstrip()
                    r = render_suffix(suf)
                    lt += r
                    lt = '{' + lt + '}' if False else lt
                out.append(lt)
            else:
                out.append(r'\text{' + t.text + '}')
        elif t.kind == 'supstd':
            out.append(render_suffix(t.text))
        elif t.kind == 'op':
            o = OPS[t.text[0]]
            if len(t.text) > 1:
                out.append(o + render_suffix(t.text[1:]) + ' ')
            else:
                out.append(o + (' ' if o.startswith('\\') else ''))
        elif t.kind == 'space':
            out.append(' ')
        elif t.kind == 'open':
            out.append(r'\{' if t.text == '{' else t.text)
        elif t.kind == 'close':
            out.append(r'\}' if t.text == '}' else t.text)
        elif t.kind == 'other':
            c = t.text
            if c == '…': out.append(r'\dots ')
            elif c in ',.:;': out.append(c)
            elif c in ('\u2019',): out.append("'")
            else: raise ValueError(f'unexpected char in math: {c!r}')
        else:
            raise ValueError(f'unexpected token in math: {t}')
    s = ''.join(out)
    s = re.sub(r' +', ' ', s)
    s = s.replace(' }', '}').replace(' _', '_').replace(' ^', '^')
    return s.strip()


def prev_sig(toks, i):
    j = i - 1
    while j >= 0 and toks[j].kind in ('space', 'bold', 'em'):
        j -= 1
    return toks[j] if j >= 0 else None


def next_sig(toks, i):
    j = i + 1
    while j < len(toks) and toks[j].kind in ('space', 'bold', 'em'):
        j += 1
    return toks[j] if j < len(toks) else None


def classify(toks, sentence_start_at_0=True):
    for i, t in enumerate(toks):
        k = t.kind
        if k == 'word' and re.fullmatch(r'\d+(\.\d+)+', t.text):
            t.cat = 'N'
        elif k == 'word' and t.text.endswith("'s"):
            t.cat = 'B'
        elif k == 'word':
            core, suf = split_word(t.text)
            if core.isdigit():
                t.cat = 'N' if not suf else 'M'
            elif core in FUNCS:
                nxt = toks[i + 1] if i + 1 < len(toks) else None
                t.cat = 'M' if (nxt is not None and nxt.kind == 'group' and nxt.cat == 'M') else 'B'
            elif is_math_word(core):
                t.cat = 'M'
                if core in ('a', 'I') and not suf:
                    t.cat = 'B'
                    if core == 'a' and not sentence_start_at_0:
                        t.cat = 'M'
                    if core == 'a':
                        pp, nn = prev_sig(toks, i), next_sig(toks, i)
                        if (pp is not None and pp.kind == 'op') or (nn is not None and nn.kind == 'op'):
                            t.cat = 'M'
                p = prev_sig(toks, i)
                if core == 'A' and not suf:
                    nx = next_sig(toks, i)
                    sent_start = (p is None and sentence_start_at_0) or (
                        p is not None and p.kind == 'other' and p.text in '.:!?')
                    if sent_start and nx is not None and nx.kind == 'word' and nx.text[0].islower() \
                            and nx.text not in ('is', 'and', 'or', 'to', 'of', 'has', 'with'):
                        t.cat = 'B'
                if not suf and core.isascii() and p is not None and p.kind == 'word' and p.text in TEXT_LABEL_WORDS:
                    t.cat = 'B'
            else:
                t.cat = 'B'
        elif k == 'supstd':
            t.cat = 'O'
        elif k == 'op':
            t.cat = 'O'
        elif k == 'space':
            t.cat = 'S'
        elif k == 'group':
            pass  # set at construction
        elif k == 'other' and t.text == ':':
            t.cat = 'C' if (i > 0 and toks[i - 1].kind == 'space') else 'B'
        elif k == 'other' and t.text == '…':
            t.cat = 'E'
        else:
            t.cat = 'B'
    return toks


def build_groups(toks):
    """Replace balanced bracket groups whose contents are purely mathematical by group tokens."""
    stack = [[]]
    opens = []
    for t in toks:
        if t.kind == 'open':
            opens.append(t)
            stack.append([])
        elif t.kind == 'close' and opens:
            inner = stack.pop()
            o = opens.pop()
            classify(inner, sentence_start_at_0=False)
            ok = all(x.cat in ('M', 'O', 'N', 'S', 'C', 'E', 'G') or
                     (x.kind == 'other' and x.text in ',.;')
                     for x in inner)
            has_math = any(x.cat in ('M', 'O') for x in inner)
            has_num = any(x.cat == 'N' for x in inner)
            if ok and (has_math or has_num):
                g = Tok('group', '', (o, inner, t))
                g.cat = 'M' if has_math else 'G'
                stack[-1].append(g)
            else:
                stack[-1].append(o)
                stack[-1].extend(inner)
                stack[-1].append(t)
        else:
            stack[-1].append(t)
    while opens:
        inner = stack.pop()
        o = opens.pop()
        stack[-1].append(o)
        stack[-1].extend(inner)
    return stack[0]


def find_runs(toks):
    runs = []
    i, n = 0, len(toks)
    while i < n:
        if toks[i].cat in ('M', 'O'):
            j = i
            while j < n and toks[j].cat in ('M', 'O', 'N', 'S', 'C', 'E', 'G'):
                j += 1
            runs.append([i, j])
            i = j
        else:
            i += 1
    # extend backwards over numbers followed by an operator: "2 ≤ n"
    out = []
    for a, b in runs:
        # trim trailing
        while b > a:
            last = toks[b - 1]
            if last.cat in ('S', 'C', 'E'):
                b -= 1; continue
            if last.cat in ('N', 'G'):
                k = b - 2
                if last.cat == 'G' and k >= a and toks[k].cat == 'M':
                    break
                while k >= a and toks[k].cat == 'S': k -= 1
                if k >= a and toks[k].cat == 'O' and toks[k].text[0] in NUMOPS:
                    break
                b -= 1; continue
            break
        # extend backwards to include a number that precedes an operator
        if toks[a].cat == 'O' and toks[a].text[0] in NUMOPS:
            k = a - 1
            while k >= 0 and toks[k].cat == 'S': k -= 1
            if k >= 0 and toks[k].cat in ('N', 'G') and (not out or out[-1][1] <= k):
                a = k
        if b > a:
            seg = toks[a:b]
            if any(x.cat == 'M' for x in seg) or any(x.kind == 'op' and x.text in OPS and not x.text.isascii() for x in seg) \
                    or any(x.kind == 'supstd' for x in seg):
                out.append([a, b])
    return out


class TextState:
    def __init__(self):
        self.dq_open = False


def render_text_tok(t, st):
    k = t.kind
    if k == 'word':
        w = t.text
        w = w.replace('ö', r'\"o').replace('é', r"\'e").replace('ü', r'\"u')
        return w
    if k == 'space':
        return ' '
    if k == 'open':
        return r'\{' if t.text == '{' else t.text
    if k == 'close':
        return r'\}' if t.text == '}' else t.text
    if k == 'group':
        o, inner, c = t.sub
        return render_text_tok(o, st) + ''.join(render_text_tok(x, st) for x in inner) + render_text_tok(c, st)
    if k == 'op':
        return '$' + OPS[t.text] + '$'
    if k == 'supstd':
        return '$' + render_suffix(t.text) + '$'
    c = t.text
    m = {'–': '--', '—': '---', '§': r'\S{}', '…': r'\dots{}', '¶': r'\P{}', '¾': r'$\tfrac34$',
         '\u2019': "'", '\u2018': '`', '&': r'\&', '%': r'\%', '#': r'\#', '$': r'\$', '~': r'\textasciitilde{}',
         '_': r'\_', '\\': r'\textbackslash{}'}
    if c == '"':
        st.dq_open = not st.dq_open
        return '``' if st.dq_open else "''"
    if c in m:
        return m[c]
    if c in GREEK or c in SPECIAL_LETTERS:
        return '$' + letter_tex(c) + '$'
    if not c.isascii():
        raise ValueError(f'unhandled char {c!r}')
    return c


def lean_escape(s):
    out = []
    for c in s:
        if c == '_': out.append(r'\_\hspace{0pt}')
        elif c == '.': out.append(r'.\hspace{0pt}')
        elif c in '{}': out.append('\\' + c)
        elif c in '#$%&': out.append('\\' + c)
        elif c == '~': out.append(r'\textasciitilde{}')
        elif c == '^': out.append(r'\textasciicircum{}')
        elif c == '\\': out.append(r'\textbackslash{}')
        elif c in SUBS: out.append('$_{' + SUBS[c] + '}$')
        elif c in SUPS: out.append('$^{' + SUPS[c] + '}$')
        elif c in "′": out.append("$'$")
        elif c in GREEK or c in SPECIAL_LETTERS: out.append('$' + letter_tex(c) + '$')
        elif c in OPS and not c.isascii(): out.append('$' + OPS[c] + '$')
        elif c == '–': out.append('--')
        elif c == '…': out.append(r'\dots{}')
        elif c == '§': out.append(r'\S{}')
        elif not c.isascii(): raise ValueError(f'unhandled char in code {c!r} in {s!r}')
        else: out.append(c)
    return r'\lean{' + ''.join(out) + '}'


ABBREV = [('u.s.c.', 'u.s.c.'), ('e.g.', 'e.g.'), ('i.e.', 'i.e.'), ('cf.', 'cf.')]


def conv(text):
    phs = []

    def ph(s):
        phs.append(s)
        return f'\x00{len(phs) - 1}\x00'

    text = re.sub(r'`([^`]+)`', lambda m: ph(lean_escape(m.group(1))), text)
    text = re.sub(r'\bp\. (?=\d)', lambda m: ph('p.~'), text)
    for a, b in ABBREV:
        text = text.replace(a, ph(b + r'\@'))
    # abbreviations such as O–T, H–O
    text = re.sub(r"\b([A-Z])–([A-Z])\b('s)?", lambda m: ph(m.group(1) + '--' + m.group(2) + (m.group(3) or '')), text)
    toks = tokenize(text)
    toks = build_groups(toks)
    classify(toks)
    for i, t in enumerate(toks):
        if t.kind == 'group' and t.cat == 'M':
            o, inner, c = t.sub
            if o.text == '(' and len(inner) == 1 and inner[0].kind == 'word' and len(inner[0].text) == 1:
                prev = toks[i - 1] if i > 0 else None
                if prev is None or prev.kind not in ('word', 'group', 'op', 'supstd'):
                    t.cat = 'B'
    runs = find_runs(toks)
    st = TextState()
    out = []
    bold_open = em_open = False
    idx = 0
    ri = 0
    while idx < len(toks):
        if ri < len(runs) and runs[ri][0] == idx:
            a, b = runs[ri]
            out.append('$' + render_math(toks[a:b]) + '$')
            idx = b
            ri += 1
            continue
        t = toks[idx]
        if t.kind == 'bold':
            out.append('}' if bold_open else r'\textbf{')
            bold_open = not bold_open
        elif t.kind == 'em':
            out.append('}' if em_open else r'\emph{')
            em_open = not em_open
        elif t.kind == 'ph':
            out.append(t.text)
        else:
            out.append(render_text_tok(t, st))
        idx += 1
    if bold_open or em_open:
        raise ValueError(f'unbalanced emphasis in: {text[:80]!r}')
    s = ''.join(out)
    s = re.sub(r'\x00(\d+)\x00', lambda m: phs[int(m.group(1))], s)
    s = re.sub(r'\x00(\d+)\x00', lambda m: phs[int(m.group(1))], s)
    return s


ASCII_ART = {'⇒': '=>', '–': '-', '…': '...', '→': '->'}

PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb}
\usepackage{enumitem}
\usepackage[hidelinks]{hyperref}

\newcommand{\lean}[1]{\texttt{#1}}
\setlist{itemsep=2pt,topsep=4pt}
\setlength{\parindent}{0pt}
\setlength{\parskip}{5pt plus 1pt}
\sloppy

"""


def main():
    lines = open(SRC, encoding='utf-8').read().split('\n')
    out = [PREAMBLE]
    i = 0
    # title
    assert lines[0].startswith('# ')
    out.append(r'\title{' + conv(lines[0][2:]) + '}\n\\author{}\n\\date{}\n\n\\begin{document}\n\\maketitle\n\n')
    i = 1
    para = []
    list_kind = None   # 'itemize' or 'enumerate'
    item = None        # list of lines of current item
    toc_done = False

    def flush_para():
        nonlocal para
        if para:
            out.append(conv(' '.join(l.strip() for l in para)) + '\n\n')
            para = []

    def flush_item():
        nonlocal item
        if item is not None:
            label, ls = item
            body = conv(' '.join(l.strip() for l in ls))
            if label is None:
                out.append(r'  \item ' + body + '\n')
            else:
                out.append(r'  \item[' + label + '] ' + body + '\n')
            item = None

    def close_list():
        nonlocal list_kind
        flush_item()
        if list_kind:
            out.append(r'\end{' + list_kind + '}\n\n')
            list_kind = None

    while i < len(lines):
        line = lines[i]
        mb = re.match(r'^\* (.*)$', line)
        mn = re.match(r'^(\d+)\. (.*)$', line)
        if line.startswith('```'):
            flush_para(); close_list()
            j = i + 1
            art = []
            while not lines[j].startswith('```'):
                l = lines[j]
                for a, b in ASCII_ART.items():
                    l = l.replace(a, b)
                assert l.isascii(), l
                art.append(l)
                j += 1
            out.append('{\\footnotesize\n\\begin{verbatim}\n' + '\n'.join(art) + '\n\\end{verbatim}\n}\n\n')
            i = j + 1
            continue
        if line.strip() == '':
            flush_para()
            # a blank line ends a list unless the next nonblank line continues it
            if list_kind:
                k = i + 1
                while k < len(lines) and lines[k].strip() == '': k += 1
                nxt = lines[k] if k < len(lines) else ''
                same = (list_kind == 'itemize' and re.match(r'^\* ', nxt)) or \
                       (list_kind == 'enumerate' and re.match(r'^\d+\. ', nxt))
                if not same:
                    close_list()
                else:
                    flush_item()
            i += 1
            continue
        if line.strip() == '---':
            flush_para(); close_list()
            out.append('\\bigskip\n\n')
            i += 1
            continue
        if line.startswith('#'):
            flush_para(); close_list()
            m = re.match(r'^(#+) (.*)$', line)
            level, title = len(m.group(1)), m.group(2)
            t = conv(title)
            if not toc_done and level <= 2:
                out.append('\\tableofcontents\n\n')
                toc_done = True
            if level == 1:
                out.append('\\part*{' + t + '}\n\\addcontentsline{toc}{part}{' + t + '}\n\n')
            elif level == 2:
                out.append('\\section*{' + t + '}\n\\addcontentsline{toc}{section}{' + t + '}\n\n')
            else:
                out.append('\\subsection*{' + t + '}\n\n')
            i += 1
            continue
        if mb or mn:
            flush_para()
            kind = 'itemize' if mb else 'enumerate'
            if list_kind != kind:
                close_list()
                out.append(r'\begin{' + kind + '}\n')
                list_kind = kind
            flush_item()
            if mb:
                item = (None, [mb.group(1)])
            else:
                item = (mn.group(1) + '.', [mn.group(2)])
            i += 1
            continue
        if item is not None:
            item[1].append(line)
            i += 1
            continue
        para.append(line)
        i += 1
    flush_para(); close_list()
    out.append('\\end{document}\n')
    res = ''.join(out)
    bad = [c for c in res if not c.isascii()]
    if bad:
        raise SystemExit(f'non-ascii output: {set(bad)}')
    open(DST, 'w').write(res)


if __name__ == '__main__':
    main()
