"""Verify preservation, witnesses, references, new arithmetic and source receipts."""
from pathlib import Path
from fractions import Fraction
import hashlib, itertools, json, re

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
paper=ROOT/'paper/snake9_research.tex'
old=(HERE/'data/paper-before.tex.snapshot').read_text(encoding='utf-8')
new=paper.read_text(encoding='utf-8')
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
statements=[m.group() for m in re.finditer(pattern,old,re.S)]
for statement in statements:assert statement in new,statement[:150]
labels=re.findall(r'\\label\{([^}]+)\}',new)
assert len(labels)==len(set(labels))
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
prior=(ROOT/'milestones/56-packing-limit-and-revision/scripts/verify.py').read_text()
fragment=prior[prior.index('quotes=lambda'):prior.index('# Check the cycle')]
exec(compile(fragment,'printed-witness-check','exec'))
assert pairs==118673
assert 4+3*4+1+4==21
assert 5*221136-4200-120*21==1098960
assert (132+74)*6**5==1601856
comparison=[]
for mean,R,quotient in [(480,536,Fraction(10609,45)),(483,551,Fraction(157625,669)),(496,600,Fraction(137941,587))]:
    value=Fraction(1098960+8*mean+R,mean+4200)
    assert value==quotient
    comparison.append(dict(mean=mean,range=R,bound=str(value),integer_bound=value.numerator//value.denominator))
assert 227*496-111960-600==32
assert sum([616,496,376])==3*496
assert 227*496-632==111960
assert [row['integer_bound'] for row in comparison]==[235,235,234]
# Reproduce the complete small direction classification independently.
def rgs(prefix,n):
    if len(prefix)==n:
        yield prefix; return
    for x in range(max(prefix,default=-1)+2):yield from rgs(prefix+[x],n)
def canonical(ds):
    d={};out=[]
    for x in ds:
        if x not in d:d[x]=len(d)
        out.append(d[x])
    return tuple(out)
def induced(ds):
    vs=[0]
    for d in ds:vs.append(vs[-1]^(1<<d))
    return all((vs[i]^vs[j]).bit_count()>(1 if j-i>1 else 0) for j in range(len(vs)) for i in range(j))
words=list(rgs([],6));good=[ds for ds in words if induced(ds)]
reps=sorted({min(canonical(ds),canonical(ds[::-1])) for ds in good})
assert len(words)==203 and len(good)==12
assert [''.join(map(str,r)) for r in reps]==['012031','012032','012034','012301','012304','012310','012314','012340','012345']
sources=[
 'milestones/67-critical-family-charge/data/lean-audit.json',
 'milestones/73-countfree-share-catalogue/data/integration-audit.json',
 'milestones/73-countfree-share-catalogue/data/proved-model.json',
 'milestones/73-countfree-share-catalogue/data/assumed-012310x12-model.json',
 'milestones/74-graph-interpretation-audit/data/potential-obstruction-proof.json',
 'milestones/74-graph-interpretation-audit/optimization/data/verification.json',
 'milestones/75-exact-history-bridge/history/data/proof-audit.json',
 'milestones/75-exact-history-bridge/lookup/data/proof-audit.json',
 'milestones/75-exact-history-bridge/numeric/data/proof-audit.json']
receipt_hashes={s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources}
record=dict(status='PASS_SOURCE_AND_MATHEMATICAL_CHECKS',paper_sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),
 previous_statements=len(statements),current_statements=len(list(re.finditer(pattern,new,re.S))),
 prior_statement_changes=0,labels=len(labels),printed_snakes=13,vertex_pair_checks=pairs,
 metadata_preserved=True,editor_identical=True,references_resolved=True,old_exclusion_table_preserved=True,
 comparisons=comparison,small_direction_classification=dict(candidates=203,induced=12,reversal_classes=9),
 cited_receipt_hashes=receipt_hashes,
 scope='Source, metadata, all printed paths, new arithmetic and small shape enumeration. Existing Lean receipts reused; no new full proof-chain rebuild. Editor compilation and visual layout are separate checks.')
(HERE/'data/verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='cited_receipt_hashes'},indent=2))
