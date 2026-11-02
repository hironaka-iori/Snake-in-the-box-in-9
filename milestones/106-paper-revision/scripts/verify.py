"""Audit manuscript preservation, printed witnesses, arithmetic and cited receipts."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re,zipfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paper=ROOT/'paper/snake9_research.tex'
with zipfile.ZipFile(HERE/'data/paper-before.zip') as z:raw=z.read('snake9_research.tex')
old=raw.decode('utf-8').replace('\r\n','\n');new=paper.read_text(encoding='utf-8')
revision=read(HERE/'data/revision.json')
assert sha(paper)==revision['paper_sha256']
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
prior=[m.group() for m in re.finditer(pattern,old,re.S)]
current=[m.group() for m in re.finditer(pattern,new,re.S)]
changed=[];removed=[]
for statement in prior:
    if statement in new:continue
    label=re.search(r'\\label\{([^}]+)\}',statement)
    if statement.startswith(r'\begin{definition}'):
        removed.append(label[1] if label else 'unlabelled_endpoint_blocking')
        body=re.sub(r'^\\begin\{definition\}(?:\[[^]]+\])?','',statement)
        body=body.removesuffix(r'\end{definition}').strip()
        assert body in new
    else:
        assert label and label[1] in revision['changed_prior_statement_labels']
        changed.append(label[1])
assert len(prior)==134 and len(current)==135
assert changed==revision['changed_prior_statement_labels']
assert removed==revision['removed_definition_environments']
assert old.count(r'\begin{definition}')==3 and new.count(r'\begin{definition}')==1
added=[s for s in current if s not in prior and not any(r'\label{'+x+'}' in s for x in changed)]
assert [re.search(r'\\label\{([^}]+)\}',s)[1] for s in added]==revision['added_statement_labels']
refmarker=r'\clearpage'+'\n'+r'\addcontentsline{toc}{section}{References}'
assert old.split(r'\appendix',1)[1].split(refmarker,1)[0]==new.split(r'\appendix',1)[1].split(refmarker,1)[0]
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
assert r'\mathsf C_{235}' not in new and r'\mathsf C_{236}' not in new
clean=re.sub(r'\\url\{[^}]*\}',r'\\url{URL}',new)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean);clean=re.sub(r'\\[{}$%]','',clean)
level=0
for c in clean:
    if c=='{':level+=1
    elif c=='}':level-=1
    assert level>=0
assert level==0 and clean.count('$')%2==0
for a,b in [(r'\[',r'\]'),(r'\(',r'\)')]:assert clean.count(a)==clean.count(b)
previous=(ROOT/'milestones/56-packing-limit-and-revision/scripts/verify.py').read_text()
fragment=previous[previous.index('quotes=lambda'):previous.index('# Check the cycle')]
exec(compile(fragment,'printed-witness-check','exec'))
assert pairs==118673

# Parse the new mathematical data from the saved manuscript itself.
table=new.split('Six-transition shape & Completed floor & Conditional floor',1)[1].split(r'\end{tabular}',1)[0]
floors=[(a,int(b),int(c)) for a,b,c in re.findall(r'\$(\d{6})\$ & (\d+) & (\d+)',table)]
assert floors==[('012031',16,16),('012032',0,16),('012034',0,18),('012301',0,16),('012304',16,16),('012310',12,12),('012314',16,16),('012340',0,16),('012345',12,16)]
table=new.split('Shape & Floor & Walk length $k$ & Weight $C$ & $496k-C$',1)[1].split(r'\end{tabular}',1)[0]
walks=[(a,*map(int,[b,c,d,e])) for a,b,c,d,e in re.findall(r'\$(\d{6})\$ & (\d+) & (\d+) & (\d+) & (\d+)',table)]
assert walks==[('012032',15,69,33592,632),('012034',17,51,24663,633),('012301',15,94,45992,632),('012340',15,77,37560,632),('012345',15,36,17224,632)]
for _,_,k,C,deficit in walks:assert k<=227 and 496*k-C==deficit and (227-k)*496+C<=111960
assert 1098960+8*483+551==1103375<4683*236
assert 1098960+8*496+602==1103530<4696*235
assert 227*496-111960-602==30
assert Fraction(1103530,4696)==Fraction(551765,2348)
assert 7*496-2872==600!=602
assert 4+3*4+1+4==21 and 5*221136-4200-120*21==1098960

# Reused proof receipts: verify exact checked source, object, log and dependency bytes.
receipts={};counts={}
def audit(base,name):
    p=base/'data'/(name+'-audit.json');r=read(p)
    assert r['exit_code']==0 and r['status'].startswith('PASS_'),name
    assert sha(base/'lean'/(name+'.lean'))==r['source_sha256'],name
    assert sha(base/'build'/(name+'.olean'))==r.get('olean_sha256',r.get('object_sha256')),name
    assert sha(base/r.get('log','logs/'+name+'.log'))==r['log_sha256'],name
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for path,digest in r.get('dependencies',{}).items():assert sha(ROOT/path)==digest,path
    receipts[p.relative_to(ROOT).as_posix()]=sha(p)
    return len(r['theorem_audits'])
base=ROOT/'milestones/98-concrete-weight-integration'
summary=read(base/'data/proof-summary.json');total=0
for row in summary['modules']:total+=audit(base,row['module'])
assert total==80;counts['98']=total
counts['105']=audit(ROOT/'milestones/105-reference-proof-closure','ReferenceAssembly105')
assert counts['105']==5
counts['104_general_assembly']=audit(ROOT/'milestones/104-complete-potential-batch','GraphAssembly104')
for name in ['CompletedPotential99','ConditionalPotential99','PotentialChecker99','ConcreteAssembly99']:
    counts[name]=audit(ROOT/'milestones/99-defined-potential-certificates',name)
for path in ['milestones/96-paper-revision/data/verification.json','milestones/97-geometric-credit-integration/data/checkpoint.json','milestones/97-geometric-credit-integration/data/proof-summary.json','milestones/97-geometric-credit-integration/floor-sensitivity/verification.json','milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/verification.json','milestones/99-defined-potential-certificates/data/proof-summary.json','milestones/105-reference-proof-closure/data/proof-summary.json','milestones/105-reference-proof-closure/data/source-selection.json']:
    receipts[path]=sha(ROOT/path)
result=dict(status='PASS_PAPER106_SOURCE_AND_MATHEMATICAL_DATA',paper_sha256=sha(paper),
    prior_statements=len(prior),current_statements=len(current),unchanged_prior_statements=130,
    changed_prior_statement_labels=changed,definition_environments_removed=removed,named_definitions=1,new_definitions=0,
    added_statement_labels=revision['added_statement_labels'],metadata_preserved=True,all_appendices_preserved=True,
    editor_identical=True,labels=len(labels),references_resolved=True,printed_snakes=13,vertex_pair_checks=pairs,
    parsed_floors=floors,parsed_obstruction_walks=walks,reused_theorem_audit_counts=counts,reused_receipt_hashes=receipts,
    new_lean_checks=0,scope='Exact source preservation, mathematical tables, printed witnesses and reused proof receipts; no new bound, full potential closure, complete dependency rebuild, successful TeX compilation or visual PDF review.')
(HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k not in ['reused_receipt_hashes','parsed_floors','parsed_obstruction_walks']},indent=2))
