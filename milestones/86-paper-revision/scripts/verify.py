"""Check the revised paper's exact preservation boundaries and mathematical data."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paper=ROOT/'paper/snake9_research.tex'
old=(HERE/'data/paper-before.tex.snapshot').read_text(encoding='utf-8')
new=paper.read_text(encoding='utf-8')
revision=json.loads((HERE/'data/revision.json').read_text())
assert sha(paper)==revision['paper_sha256']
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
statements=[m.group() for m in re.finditer(pattern,old,re.S)]
changed=[]
for statement in statements:
    if statement not in new:
        assert r'\label{thm:countfree-completed}' in statement,statement[:150]
        changed.append('thm:countfree-completed')
assert changed==revision['changed_prior_statement_labels']
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
# The entire original appendix is unchanged, apart from added bibliography entries.
body=lambda s:s.split(r'\appendix',1)[1].split(r'\begin{thebibliography}',1)[0]
assert body(old)==body(new)
prior=(ROOT/'milestones/56-packing-limit-and-revision/scripts/verify.py').read_text()
fragment=prior[prior.index('quotes=lambda'):prior.index('# Check the cycle')]
exec(compile(fragment,'printed-witness-check','exec'))
assert pairs==118673
assert 4+3*4+1+4==21
assert 5*221136-4200-120*21==1098960
assert (132+74)*6**5==1601856
comparison=[]
for p,d,R,quotient in [(480,1,536,Fraction(10609,45)),(483,1,551,Fraction(157625,669)),
                       (9259,19,11301,Fraction(20965613,89059)),(496,1,600,Fraction(137941,587))]:
    value=Fraction(1098960*d+8*p+R,p+4200*d);assert value==quotient
    comparison.append(dict(mean=str(Fraction(p,d)),potential_range=str(Fraction(R,d)),bound=str(value),integer_bound=value.numerator//value.denominator))
assert [r['integer_bound'] for r in comparison]==[235,235,235,234]
assert 227*496-111960-600==32
assert 111960-227*483==2319
assert 111960*19-227*9259==25447
assert sum([252,480,600,600])==4*483 and (1932+56)==4*497
assert 1287+732-641==1378 and 505*6**6==23561280
target_block=new.split('Shape & Target for $H$')[1].split(r'\end{tabular}')[0]
assert target_block.count('Pending')==5 and target_block.count('Checked')==4
assert r'$012310$ & 12 & Checked' in target_block
assert 'six pending' not in new.split(r'\appendix')[0].lower()
assert not (ROOT/'milestones/73-countfree-share-catalogue/cases/case7302/data/proof-audit.json').exists(),'Refresh paper: case7302 has finished'
# Freeze every reused record; the complete prior dependency closures are not rebuilt here.
sources=[
 'milestones/77-direction-state-coverage/data/proof-summary.json',
 'milestones/78-numeric-history-transition/data/proof-summary.json',
 'milestones/79-retained-edge-guards/data/proof-summary.json',
 'milestones/80-012310-share-closure/data/checkpoint.json',
 'milestones/81-recovered-short-rule-retention/data/proof-summary.json',
 'milestones/82-unsaturated-cycle-obstruction/data/graph-audit.json',
 'milestones/82-unsaturated-cycle-obstruction/data/lean-audit.json',
 'milestones/82-unsaturated-cycle-obstruction/data/target-sensitivity.json',
 'milestones/83-012034-share-certificate/data/comparison-audit.json',
 'milestones/83-012034-share-certificate/data/lean-audit.json',
 'milestones/84-history-exclusion-retention/data/proof-summary.json',
 'milestones/85-reference-catalogue-union/data/proof-summary.json',
 'milestones/73-countfree-share-catalogue/cases/case7305/data/proof-audit.json',
 'milestones/73-countfree-share-catalogue/data/proved-model.json',
 'milestones/73-countfree-share-catalogue/data/integration-audit.json']
receipt_hashes={rel:sha(ROOT/rel) for rel in sources}
newlogic=json.loads((HERE/'data/logic-audit.json').read_text());assert newlogic['status']=='PASS_PAPER86_LOGIC'
for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','object_sha256'),('logs','.log','log_sha256')]:
    assert sha(HERE/folder/('RevisionLogic'+ext))==newlogic[key]
assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in newlogic['theorem_audits'])
bonuslogic=json.loads((HERE/'data/bonus-audit.json').read_text());assert bonuslogic['status']=='PASS_PAPER86_LOGIC'
for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','object_sha256'),('logs','.log','log_sha256')]:
    assert sha(HERE/folder/('BonusCriterion'+ext))==bonuslogic[key]
assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in bonuslogic['theorem_audits'])
for milestone,source in [('82-unsaturated-cycle-obstruction','UnsaturatedCycle'),('83-012034-share-certificate','ConditionalTarget')]:
    base=ROOT/'milestones'/milestone;r=json.loads((base/'data/lean-audit.json').read_text())
    for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','object_sha256'),('logs','.log','log_sha256')]:
        assert sha(base/folder/(source+ext))==r[key]
record=dict(status='PASS_PAPER86_SOURCE_AND_MATHEMATICS',paper_sha256=sha(paper),
    previous_statements=len(statements),current_statements=len(list(re.finditer(pattern,new,re.S))),
    changed_prior_statement_labels=changed,labels=len(labels),printed_snakes=13,vertex_pair_checks=pairs,
    metadata_preserved=True,editor_identical=True,references_resolved=True,appendix_body_preserved=True,
    old_exclusion_table_preserved=True,comparisons=comparison,target_completed=4,target_pending=5,
    cited_receipt_hashes=receipt_hashes,new_logic_audit_sha256=sha(HERE/'data/logic-audit.json'),
    bonus_audit_sha256=sha(HERE/'data/bonus-audit.json'),new_lean_checks=14,
    scope='Source structure, exact preservation, all printed paths, arithmetic and cited-record hashes. New abstract logic checked; existing proof receipts reused. No clean full project rebuild. Editor compilation and page layout are separate gates.')
(HERE/'data/verification.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='cited_receipt_hashes'},indent=2))
