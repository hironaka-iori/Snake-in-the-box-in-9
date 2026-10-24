"""Verify the revised source, its retained claims, witnesses, and references."""
from pathlib import Path
from collections import Counter
import hashlib, json, re, subprocess
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
BASE = '1977ccdd66b020e1ae44dfe2910c30fed9ab90ce'
paper = ROOT/'paper/snake9_research.tex'
editor = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
old = subprocess.check_output(['git','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode().replace('\r\n','\n')
new = paper.read_text(encoding='utf-8')
assert paper.read_bytes() == editor.read_bytes()
assert old.split(r'\begin{abstract}')[0] == new.split(r'\begin{abstract}')[0]
pattern = r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
statements = [m.group().replace('on the same 44064 states','on the 44064 states just defined') for m in re.finditer(pattern,old,re.S)]
for statement in statements: assert statement in new, statement[:100]
labels = re.findall(r'\\label\{([^}]+)\}',new)
assert len(labels) == len(set(labels))
assert set(re.findall(r'\\label\{([^}]+)\}',old)) <= set(labels)
assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',new)) <= set(labels)
cites = {k for g in re.findall(r'\\cite\{([^}]+)\}',new) for k in g.split(',')}
assert cites <= set(re.findall(r'\\bibitem\{([^}]+)\}',new))
stack = []
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
    if m[1] == 'begin': stack.append(m[2])
    else: assert stack and stack.pop() == m[2], (m.start(),m[2])
assert not stack
clean = re.sub(r'\\url\{[^}]*\}',r'\\url{URL}',new)
clean = re.sub(r'(?<!\\)%[^\n]*','',clean)
clean = re.sub(r'\\[{}$%]','',clean)
level = 0
for c in clean:
    if c == '{': level += 1
    elif c == '}': level -= 1
    assert level >= 0
assert level == 0 and clean.count('$')%2 == 0
for a,b in [(r'\[',r'\]'),(r'\(',r'\)')]: assert clean.count(a) == clean.count(b)
assert '.lean' not in new
catalogue = new.split(r'\label{tab:exclusion-catalogue}')[1].split(r'\end{longtable}')[0]
rows = re.findall(r'^\d+ & \$\(([^)]+)\)\$ & \$\(([^)]+)\)\$\\\\$',catalogue,re.M)
keys = [[[int(x) for x in a.split(',')],[int(x) for x in b.split(',')]] for a,b in rows]
assert keys == json.loads((ROOT/'milestones/37-logical-paper-rewrite/data/exclusion-catalogue.json').read_text())

# Preserve the transition words exactly and recheck all eight printed snakes.
quotes = lambda s: re.findall(r'\\begin\{quote\}\\small\\ttfamily\s*(.*?)\\end\{quote\}',s,re.S)
assert quotes(old) == quotes(new)
settings = [(9,0,191),(9,193,143),(9,77,138),(9,0,93),(8,0,98),(9,145,137),(8,0,96),(8,0,94)]
assert len(quotes(new)) == len(settings)
pair_checks = 0
for text,(n,start,length) in zip(quotes(new),settings):
    ds = [int(x) for x in re.findall(r'\d',text)]
    assert len(ds) == length and max(ds)<n
    vertices = [start]
    for d in ds: vertices.append(vertices[-1]^(1<<d))
    assert len(set(vertices)) == len(vertices)
    for j in range(len(vertices)):
        for i in range(j):
            assert ((vertices[i]^vertices[j]).bit_count()==1) == (j-i==1)
            pair_checks += 1

# Forest listing and blocker arrays remain unchanged despite the appendix move.
forest = lambda s: s.split(r'\subsection{A radius-three linear forest}')[1].split(r'\end{align*}')[0]
assert forest(old) == forest(new)
for snippet in ['(19,37,13,13,27,19,189,43,91)', '(1,33,51,91,45,1,91,81,45)', '(25,19,43,27,19,61,21,23,91)']:
    assert snippet in new
result = dict(status='PASS', baseline_commit=BASE, prior_statements_preserved=len(statements),
    current_statements=len(list(re.finditer(pattern,new,re.S))), labels=len(labels),
    exclusion_rows=len(keys), printed_snakes_rechecked=len(settings), vertex_pairs_checked=pair_checks,
    metadata_preserved=True, editor_identical=True, all_references_resolve=True,
    paper_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),
    scope='Source integrity and printed-witness verification. Full archived 236 proof not rebuilt; rendered pages not visually inspected.')
(HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
