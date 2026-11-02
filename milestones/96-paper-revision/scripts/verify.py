"""Check preservation, printed witnesses, new catalogue and reused proof evidence."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re,zipfile

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
paper=ROOT/'paper/snake9_research.tex'
with zipfile.ZipFile(HERE/'data/paper-before.zip') as z: raw=z.read('snake9_research.tex')
old=raw.decode('utf-8').replace('\r\n','\n'); new=paper.read_text(encoding='utf-8')
revision=read(HERE/'data/revision.json')
assert sha(paper)==revision['paper_sha256']
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
statements=[m.group() for m in re.finditer(pattern,old,re.S)]
current=[m.group() for m in re.finditer(pattern,new,re.S)]
assert len(statements)==130 and len(current)==134
assert all(s in new for s in statements)
added=[s for s in current if s not in statements]
assert [re.search(r'\\label\{([^}]+)\}',s)[1] for s in added]==revision['added_statement_labels']
assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}')==3
labels=re.findall(r'\\label\{([^}]+)\}',new)
assert len(labels)==len(set(labels))
assert set(re.findall(r'\\label\{([^}]+)\}',old))<=set(labels)
assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',new))<=set(labels)
cites={k for g in re.findall(r'\\cite\{([^}]+)\}',new) for k in g.split(',')}
assert cites<=set(re.findall(r'\\bibitem\{([^}]+)\}',new))
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
    if m[1]=='begin': stack.append(m[2])
    else: assert stack and stack.pop()==m[2],m[2]
assert not stack and '.lean' not in new and 'sorryAx' not in new
clean=re.sub(r'\\url\{[^}]*\}',r'\\url{URL}',new)
clean=re.sub(r'(?<!\\)%[^\n]*','',clean); clean=re.sub(r'\\[{}$%]','',clean)
level=0
for c in clean:
    if c=='{': level+=1
    elif c=='}': level-=1
    assert level>=0
assert level==0 and clean.count('$')%2==0
for a,b in [(r'\[',r'\]'),(r'\(',r'\)')]: assert clean.count(a)==clean.count(b)
catalogue=lambda s:s.split(r'\label{tab:exclusion-catalogue}')[1].split(r'\end{longtable}')[0]
assert catalogue(old)==catalogue(new)
reference_marker=r'\clearpage'+'\n'+r'\addcontentsline{toc}{section}{References}'
assert old.split(r'\appendix',1)[1].split(reference_marker,1)[0]==new.split(r'\appendix',1)[1].split(r'\section{Complete history-share catalogue}',1)[0]
prior=(ROOT/'milestones/56-packing-limit-and-revision/scripts/verify.py').read_text()
fragment=prior[prior.index('quotes=lambda'):prior.index('# Check the cycle')]
exec(compile(fragment,'printed-witness-check','exec'))
assert pairs==118673

# Independently parse the emitted TeX, including the actual index in every cap.
table=new.split(r'\label{tab:history-share-catalogue}',1)[1].split(r'\end{longtable}',1)[0]
parsed=[]
for line in table.splitlines():
    if not re.match(r'^\d+ & ',line): continue
    fields=line.removesuffix('\\\\').split(' & ')
    assert len(fields)==5
    words=[list(map(int,w)) for w in re.findall(r'\\mathtt\{(\d+)\}',fields[1])]
    caps={str(int(k)-5):int(v) for k,v in re.findall(r'\\alpha_\{s\+(\d+)\}\\le(\d+)',fields[2])}
    assert caps or fields[2]=='None'
    parsed.append(dict(row=int(fields[0]),variants=words,caps=caps,geometric_lower=int(fields[3]),stronger=None if fields[4]=='--' else int(fields[4])))
rows=read(ROOT/'milestones/94-history-share-dispatch/data/variants.json')['rows']
assert len(parsed)==len(rows)==55
for i,(a,b) in enumerate(zip(parsed,rows)):
    assert a==dict(row=i+1,variants=b['variants'],caps=b['caps'],geometric_lower=b['geometric_lower'],stronger=b['lower'] if b['caps'] else None)
    assert all(v<6 for v in a['caps'].values())
assert sum(len(r['variants']) for r in parsed)==69
assert sum(len(r['variants'])==1 for r in parsed)==41
assert sum(len(r['variants'])==2 for r in parsed)==14
assert sum(bool(r['caps']) for r in parsed)==8

comparisons=[]
for profile,M,k,C,R,quotient,cl,cw in [
 ('completed',Fraction(483),9,3796,Fraction(551),Fraction(157625,669),4,1932),
 ('additional012034',Fraction(9259,19),31,14512,Fraction(11301,19),Fraction(20965613,89059),19,9259),
 ('full-conditional',Fraction(496),7,2872,Fraction(600),Fraction(137941,587),3,1488)]:
    assert R==k*M-C and M==Fraction(cw,cl)
    value=(1098960+8*M+R)/(4200+M)
    assert value==quotient and k+8<=value
    certificate=read(ROOT/f'milestones/93-defined-graph-potential/data/{profile}-range-certificate.json')
    assert certificate['path_edges']==k and certificate['path_weight']==C
    assert certificate['cycle_edges']==cl and certificate['cycle_weight']==cw
    comparisons.append(dict(profile=profile,mean=str(M),range=str(R),bound=str(value),integer_bound=value.numerator//value.denominator))
assert [r['integer_bound'] for r in comparisons]==[235,235,234]
assert 227*496-111960-600==32
assert 4+3*4+1+4==21 and 5*221136-4200-120*21==1098960
assert (132+74)*6**5==1601856 and 4740419+206589==4947008
target=new.split('Shape & Target for $H$')[1].split(r'\end{tabular}')[0]
assert target.count('Pending')==5 and target.count('Checked')==4
assert not (ROOT/'milestones/73-countfree-share-catalogue/cases/case7302/data/proof-audit.json').exists()

# Recheck exact successful receipt/source/object/log bytes, without rebuilding.
receipts={}; counts={}
def audit(base,name):
    p=base/'data'/(name+'-audit.json'); r=read(p)
    assert r['exit_code']==0 and r['status'].startswith('PASS_'),name
    assert sha(base/'lean'/(name+'.lean'))==r['source_sha256'],name
    assert sha(base/'build'/(name+'.olean'))==r.get('olean_sha256',r.get('object_sha256')),name
    log=base/r.get('log','logs/'+name+'.log')
    assert sha(log)==r['log_sha256'],name
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits'])
    for path,digest in r.get('dependencies',{}).items(): assert sha(ROOT/path)==digest,path
    receipts[p.relative_to(ROOT).as_posix()]=sha(p)
    return len(r['theorem_audits'])
for number,folder,expected in [(94,'94-history-share-dispatch',73),(95,'95-history-credit-integration',923)]:
    base=ROOT/'milestones'/folder; summary=read(base/'data/proof-summary.json'); total=0
    for row in summary['modules']:
        p=ROOT/row['receipt']; assert sha(p)==row['receipt_sha256']
        total+=audit(base,row['module'])
    assert total==expected==summary['theorem_audits']; counts[str(number)]=total
    receipts[(base/'data/proof-summary.json').relative_to(ROOT).as_posix()]=sha(base/'data/proof-summary.json')
counts['93']=audit(ROOT/'milestones/93-defined-graph-potential','PotentialComparison')
counts['92']=audit(ROOT/'milestones/92-full-witness-batch','DefinedProofGraph')+audit(ROOT/'milestones/92-full-witness-batch','ContextAssignment')
assert counts['93']==7
for path in ['milestones/93-defined-graph-potential/data/range-certificate-review.json','milestones/95-history-credit-integration/data/source-audit.json','milestones/95-history-credit-integration/data/credit-literal-audit.json','milestones/86-paper-revision/data/verification.json']:
    receipts[path]=sha(ROOT/path)
result=dict(status='PASS_PAPER96_SOURCE_AND_MATHEMATICAL_DATA',paper_sha256=sha(paper),previous_statements=130,current_statements=134,changed_prior_statements=0,added_named_definitions=0,existing_definitions=3,labels=len(labels),metadata_preserved=True,editor_identical=True,original_appendix_preserved=True,old_exclusion_table_preserved=True,references_resolved=True,printed_snakes=13,vertex_pair_checks=pairs,history_table_rows=55,history_table_words=69,history_table_capped_rows=8,comparisons=comparisons,reused_theorem_audit_counts=counts,reused_receipt_hashes=receipts,new_lean_checks=0,scope='Source preservation, printed paths, catalogue, exact arithmetic and existing successful proof receipts. No new Lean theorem, independent full dependency rebuild, successful TeX compilation or page-layout review.')
(HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='reused_receipt_hashes'},indent=2))
