"""Check statement preservation, printed witnesses and all new manuscript tables."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
BASE='6d7adc034da38b71fe6210acf5442255a7a52771'
paper=ROOT/'paper/snake9_research.tex';new=paper.read_text(encoding='utf-8')
old=subprocess.check_output(['git','-c','core.commitGraph=false','show',BASE+':paper/snake9_research.tex'],cwd=ROOT).decode().replace('\r\n','\n')
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
statements=[m.group() for m in re.finditer(pattern,old,re.S)]
for statement in statements:
    expected=statement.replace('The current exploratory graph contains a 25-step cycle','The earlier exploratory graph described in this appendix contains a 25-step cycle')
    assert expected in new,statement[:140]
labels=re.findall(r'\\label\{([^}]+)\}',new);assert len(labels)==len(set(labels))
assert set(re.findall(r'\\label\{([^}]+)\}',old))<=set(labels)
assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',new))<=set(labels)
cites={k for g in re.findall(r'\\cite\{([^}]+)\}',new) for k in g.split(',')}
assert cites<=set(re.findall(r'\\bibitem\{([^}]+)\}',new))
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
    if m[1]=='begin':stack.append(m[2])
    else:assert stack and stack.pop()==m[2],m[2]
assert not stack and '.lean' not in new and 'sorryAx' not in new
clean=re.sub(r'\\url\{[^}]*\}',r'\\url{URL}',new)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean);clean=re.sub(r'\\[{}$%]','',clean)
level=0
for c in clean:
    if c=='{':level+=1
    elif c=='}':level-=1
    assert level>=0
assert level==0 and clean.count('$')%2==0
for a,b in [(r'\[',r'\]'),(r'\(',r'\)')]:assert clean.count(a)==clean.count(b)
catalogue=lambda s:s.split(r'\label{tab:exclusion-catalogue}')[1].split(r'\end{longtable}')[0]
assert catalogue(old)==catalogue(new)
# Reuse the earlier complete printed-witness checker without repeating its graph replay.
prior=(ROOT/'milestones/56-packing-limit-and-revision/scripts/verify.py').read_text()
fragment=prior[prior.index('quotes=lambda'):prior.index('# Check the cycle')]
exec(compile(fragment,'printed-witness-check','exec'))
assert pairs==118673
pack=json.loads((ROOT/'milestones/65-count-saturation-share/data/compact-certificates.json').read_text())['rows']
used=json.loads((ROOT/'milestones/65-count-saturation-share/data/verification.json').read_text())['upper_premises_used']
share_block=new.split(r'\label{thm:saturated-shares}')[1].split(r'\end{theorem}')[0]
for record in pack:
    if record['mode']!='share':continue
    i=record['edge'];r=json.loads((ROOT/f'milestones/65-count-saturation-share/data/cases/e{i:03d}.json').read_text())
    caps=r',\ '.join('A_{'+str(k+5)+'}\\le'+str(r['constraints'][k]['hi']) for k in used[str(i)])
    assert '$'+''.join(map(str,r['directions']))+'$ & $'+caps+'$ & '+str(record['lower'])+r'\\' in share_block
local_rows=[([0,1,2,3,0,4,3,2,5,4,3],10,[6,33,39],[(2,5),(0,1),(0,2)]),
    ([0,1,2,3,4,5,3,2,0,1,3],8,[17,27,33],[(1,5),(3,5),(1,4)]),
    ([0,1,2,3,4,5,3,2,0,5,3],10,[6,17,23],[(2,4),(0,1),(0,2)])]
for ds,j,D,ps in local_rows:
    W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    assert '$'+','.join(map(str,W))+'$' in new
    assert all(W[j]^(1<<a)^(1<<b)==v and not {a,b}&{ds[j-1],ds[j]} for v,(a,b) in zip(D,ps))
    for q in D:
        T=set(W)|{q};assert any(sum((v^z).bit_count()==1 for z in T)>=3 for v in T)
assert Fraction(18823,38)-Fraction(9891,20)==Fraction(301,380)
assert Fraction(9961,2400)-Fraction(1991,480)==Fraction(1,400)
assert 1099680*38+8*18823+23459==41961883 and 18823+4200*38==178423
assert 178423*235<=41961883<178423*236
analyses=[json.loads((HERE/f'data/{name}-analysis.json').read_text()) for name in ['terminal','shares','pressured']]
assert all(r['integer_mean']=='18823/38' and r['potential_range']==23459 and len(r['cycle'])==38 for r in analyses)
family=json.loads((HERE/'data/critical-family.json').read_text());assert (family['critical_states'],family['critical_edges'])==(70,99)
out=dict(status='PASS',baseline_commit=BASE,paper_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),
    prior_statements=len(statements),current_statements=len(list(re.finditer(pattern,new,re.S))),
    prior_statement_changes='Only the historical graph referent in the zero-credit proposition; mathematical content unchanged.',
    labels=len(labels),printed_snakes=13,vertex_pair_checks=pairs,metadata_preserved=True,editor_identical=True,
    references_resolved=True,share_table_rows=9,direct_corner_rows=3,
    scope='Source, metadata, mathematical table arithmetic, all printed paths and archive comparisons. Compilation and visual inspection are separate checks.')
(HERE/'data/paper-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
