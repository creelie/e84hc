#!/usr/bin/env python3
"""make_computations.py -- build COMPUTATIONS.md at the root of the archive.

The sources are items.tex (the computations, items (I) to (LXXVIII)), lean.tex
(the Lean certificate and its table of theorems) and item_labels.json (for
each item, the labels of the results of the paper that cite it).  Every
cross-reference is resolved to the numbering of the compiled paper through
tex/main.aux, so run this after the paper has been built:

    cd code/computations && python3 make_computations.py
"""
import os, re, json
HERE = os.path.dirname(os.path.abspath(__file__))
SP = HERE + '/'
TEX = os.path.join(HERE, '..', '..', 'tex') + '/'
ROOT = os.path.join(HERE, '..', '..') + '/'
aux = open(TEX + 'main.aux').read()
num, typ = {}, {}
for m in re.finditer(r'\\newlabel\{([^}@]+)\}\{\{([^}]*)\}', aux):
    num[m.group(1)] = m.group(2)
for m in re.finditer(r'\\newlabel\{([^}]+)@cref\}\{\{\[([^\]]*)\]', aux):
    typ[m.group(1)] = m.group(2)
NAMES = {'theorem': 'Theorem', 'lemma': 'Lemma', 'proposition': 'Proposition',
         'corollary': 'Corollary', 'remark': 'Remark', 'definition': 'Definition',
         'section': 'Section', 'subsection': 'Section', 'subsubsection': 'Section',
         'equation': 'equation', 'figure': 'Figure', 'table': 'Table',
         'appendix': 'Appendix', 'setupenv': 'Setup', 'setup': 'Setup',
         'notation': 'Notation', 'question': 'Question', 'example': 'Example',
         'enumi': 'item', 'part': 'Part', 'conjecture': 'Conjecture',
         'construction': 'Construction', 'subappendix': 'Appendix'}
missing = set()
def ref(lab):
    lab = lab.strip()
    if lab not in num:
        missing.add(lab); return '[%s]' % lab
    t = NAMES.get(typ.get(lab, ''), typ.get(lab, '').capitalize() or 'result')
    if t == 'equation':
        return '(%s)' % num[lab]
    return '%s %s' % (t, num[lab])
def cref(m):
    return ', '.join(ref(l) for l in m.group(1).split(','))
MAC = {r'\QQ': r'\mathbb{Q}', r'\ZZ': r'\mathbb{Z}', r'\RR': r'\mathbb{R}',
       r'\CC': r'\mathbb{C}', r'\PP': r'\mathbb{P}', r'\NN': r'\mathbb{N}',
       r'\Av': r'A^{\vee}', r'\Kx': r'K^{\times}', r'\HW': 'W',
       r'\Hdg': r'\mathrm{Hdg}', r'\NS': r'\mathrm{NS}', r'\Nm': r'\mathrm{N}',
       r'\cl': r'\mathrm{cl}', r'\Cn': r'\mathrm{Cn}'}
for c in 'PFEGOLHIKADVSXZQ':
    MAC['\\c' + c] = r'\mathcal{%s}' % c
OPS = ['CH', 'ch', 'td', 'rk', 'End', 'Hom', 'Ext', 'Pic', 'Hilb', 'Res', 'MT',
       'Hg', 'Gal', 'coker', 'id', 'Spec', 'Supp', 'codim', 'Sec', 'Tr', 'GU',
       'GL', 'SL', 'SU', 'SO', 'Sp', 'ob', 'Ann']
def convert(s):
    s = re.sub(r'(?<!\\)%.*', '', s)
    s = re.sub(r'\\[Cc]ref\{([^}]*)\}', cref, s)
    s = re.sub(r'\\eqref\{([^}]*)\}', lambda m: ref(m.group(1)), s)
    s = re.sub(r'\\ref\{([^}]*)\}', lambda m: num.get(m.group(1), m.group(1)), s)
    s = re.sub(r'\\cite\[([^\]]*)\]\{([^}]*)\}', r'[\2, \1]', s)
    s = re.sub(r'\\cite\{([^}]*)\}', r'[\1]', s)
    s = re.sub(r'\\emph\{((?:[^{}]|\{[^{}]*\})*)\}', r'*\1*', s)
    s = re.sub(r'\\textup\{([^{}]*)\}', r'\1', s)
    s = re.sub(r'\\texttt\{([^{}]*)\}', r'`\1`', s)
    s = s.replace('~', ' ').replace("``", '"').replace("''", '"')
    s = s.replace(r'\bbar', r'\overline').replace(r'\image', r'\operatorname{im}')
    for k in sorted(MAC, key=len, reverse=True):
        s = re.sub(re.escape(k) + r'(?![A-Za-z])', lambda m, v=MAC[k]: v, s)
    for o in OPS:
        s = re.sub(r'\\' + o + r'(?![A-Za-z])', lambda m, o=o: r'\operatorname{%s}' % o, s)
    s = re.sub(r'\\label\{[^}]*\}', '', s)
    s = s.replace(r"\'e", 'é').replace(r'\"a', 'ä').replace(r'\"o', 'ö').replace(r'\"u', 'ü').replace(r"\`e", 'è').replace(r'\^o','ô')
    s = s.replace('--', '–')
    return s
ROM = []
def roman(n):
    vals = [(1000,'M'),(900,'CM'),(500,'D'),(400,'CD'),(100,'C'),(90,'XC'),(50,'L'),(40,'XL'),(10,'X'),(9,'IX'),(5,'V'),(4,'IV'),(1,'I')]
    r = ''
    for v, c in vals:
        while n >= v: r += c; n -= v
    return r
item_labels = json.load(open(SP + 'item_labels.json'))
D = open(SP + 'items.tex').read()
body = D[D.index(r'\begin{enumerate}[label=\textup{(\Roman*)}'):]
body = body[body.index('\n') + 1:]
end = body.rfind(r'\end{enumerate}')
intro_end = body[end + len(r'\end{enumerate}'):]
body = body[:end]
# split top-level items (nested enumerates are rare; keep them as text)
parts, depth, cur = [], 0, ''
for line in body.split('\n'):
    if re.match(r'\s*\\begin\{(enumerate|itemize)\}', line): depth += 1
    if re.match(r'\s*\\end\{(enumerate|itemize)\}', line): depth -= 1
    if depth == 0 and line.startswith(r'\item'):
        if cur.strip(): parts.append(cur)
        cur = line[len(r'\item'):] + '\n'
    else:
        cur += line + '\n'
if cur.strip(): parts.append(cur)
out = []
out.append('# Computations\n')
out.append('This document accompanies the paper *Algebraic Loci of Weil Classes '
           'on Abelian Varieties*, whose LaTeX source is in `tex/`. The paper '
           'cites the programs of this archive '
           'as [BMB26]. Below, each computation is listed under the item number '
           'that the programs, `code/verify_all.py` and the README use, with the '
           'results of the paper that it checks. Theorem, section and equation '
           'numbers refer to the compiled paper `tex/main.pdf`.\n')
pre = D[:D.index(r'\begin{enumerate}[label=\textup{(\Roman*)}')]
pre = pre[pre.index('\n') + 1:]
out.append(convert(pre).strip() + '\n')
out.append('## Index: results of the paper and the items that check them\n')
rev = {}
for it, labs in item_labels.items():
    for l in labs:
        rev.setdefault(l, []).append(it)
def keyf(l):
    n = num.get(l, '999')
    return [int(x) if x.isdigit() else 1000 + ord(x[0]) for x in re.split(r'[.]', n)]
rows = []
for l in sorted(rev, key=keyf):
    rows.append('| %s | %s |' % (ref(l), ', '.join('(%s)' % i for i in sorted(set(rev[l]), key=lambda r: [k for k in range(1,200) if roman(k)==r][0]))))
out.append('| result | items |\n| --- | --- |\n' + '\n'.join(rows) + '\n')
out.append('## The items\n')
for k, p in enumerate(parts, 1):
    r = roman(k)
    t = convert(p).strip()
    m = re.match(r'\*([^*]+)\*\s*(.*)', t, re.S)
    title, text = (re.sub(r'\s+', ' ', m.group(1)).strip().rstrip('.'), m.group(2)) if m else ('', t)
    text = re.sub(r'\n\s*', ' ', text)
    out.append('### (%s) %s\n' % (r, title))
    cited = [l for l, its in rev.items() if r in its]
    if cited:
        out.append('Checks: ' + ', '.join(ref(l) for l in sorted(cited, key=keyf)) + '.\n')
    out.append(text.strip() + '\n')
if intro_end.strip():
    out.append(re.sub(r'\n\s*', ' ', convert(intro_end)).strip() + '\n')
E = open(SP + 'lean.tex').read()
E = E[E.index('\n') + 1:]
lt0 = E.index('\\begingroup') if '\\begingroup' in E[:E.index('\\begin{longtable}')] else E.index('\\begin{longtable}')
lt1 = E.index('\\end{longtable}') + len('\\end{longtable}')
if E[lt1:lt1 + 20].lstrip().startswith('\\endgroup'):
    lt1 = E.index('\\endgroup', lt1) + len('\\endgroup')
tab = E[lt0:lt1]
rows = tab[tab.index('\\endlastfoot') + len('\\endlastfoot'):tab.index('\\end{longtable}')]
mdrows = []
for r in re.split(r'\\\\\s*\n', rows):
    r = ' '.join(r.split())
    if '&' not in r:
        continue
    a, b = r.split('&', 1)
    a = a.replace('\\allowbreak', '').replace('}\\texttt{', '')
    mdrows.append('| %s | %s |' % (convert(a).strip().replace('\\_', '_'), convert(b).strip().rstrip('\\').strip()))
E = E[:lt0] + '\n\nTABLEPLACEHOLDER\n\n' + E[lt1:]
E = E.replace('\\allowbreak', '').replace('}\\texttt{', '')
E = convert(E)
E = re.sub(r'\\begin\{(enumerate|itemize|description)\}(\[[^\]]*\])?', '', E)
E = re.sub(r'\\end\{(enumerate|itemize|description)\}', '', E)
E = re.sub(r'\\item(\[[^\]]*\])?\s*', '\n- ', E)
E = re.sub(r'\\(sub)*section\*?\{([^}]*)\}', r'\n### \2\n', E)
E = re.sub(r'\n(?!- |\n|###|\|)\s*', ' ', E)
out.append('## The Lean certificate\n')
E = E.replace('TABLEPLACEHOLDER', '\n| theorem | statement |\n| --- | --- |\n' + '\n'.join(mdrows) + '\n')
out.append(E.strip() + '\n')
txt = '\n'.join(out)
txt = re.sub(r'\\begin\{(enumerate|itemize)\}(\[[^\]]*\])?', '', txt)
txt = re.sub(r'\\end\{(enumerate|itemize)\}', '', txt)
txt = re.sub(r'\\item(\[[^\]]*\])?', '\n  -', txt)
txt = txt.replace('[sec:verification]', 'the items above').replace('[tab:lean]', 'the table below')
txt = re.sub(r'`([^`]*)`', lambda m: '`' + m.group(1).replace('\\_', '_') + '`', txt)
open(ROOT + 'COMPUTATIONS.md', 'w').write(txt)
print(len(parts), 'items; missing labels:', sorted(missing)[:40], len(missing))
