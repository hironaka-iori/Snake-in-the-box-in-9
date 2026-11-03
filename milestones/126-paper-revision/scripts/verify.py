"""Check revised manuscript, printed constructions, arithmetic, and reused receipts."""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re,zipfile
H=Path(__file__).resolve().parents[1];R=H.parents[1];ROOT=R
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
 p=Path(p)
 if p not in cache:cache[p]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[p]
paper=R/'paper/snake9_research.tex'
with zipfile.ZipFile(H/'data/paper-before.zip') as z:raw=z.read('snake9_research.tex')
old=raw.decode('utf-8').replace('\r\n','\n');new=paper.read_text(encoding='utf-8')
assert paper.read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
assert old.split(r'\begin{abstract}')[0]==new.split(r'\begin{abstract}')[0]
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition)\}.*?\\end\{\1\}'
prior=[m.group() for m in re.finditer(pattern,old,re.S)];current=[m.group() for m in re.finditer(pattern,new,re.S)]
changed=[s for s in prior if s not in new]
assert len(prior)==138 and len(current)==145
allowed={'prop:boundary21','thm:share120','prop:mixed-common-budget'}
assert {re.search(r'\\label\{([^}]+)\}',s)[1] for s in changed}==allowed
assert old.count(r'\begin{definition}')==new.count(r'\begin{definition}')==1
refmarker=r'\clearpage'+'\n'+r'\addcontentsline{toc}{section}{References}'
appendix=old.split(r'\appendix',1)[1].split(refmarker,1)[0]
assert new.split(r'\appendix',1)[1].startswith(appendix)
labels=re.findall(r'\\label\{([^}]+)\}',new);bibs=re.findall(r'\\bibitem\{([^}]+)\}',new)
assert len(labels)==len(set(labels)) and len(bibs)==len(set(bibs))
assert set(re.findall(r'\\label\{([^}]+)\}',old))<=set(labels)
assert set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',new))<=set(labels)
assert {k for g in re.findall(r'\\cite\{([^}]+)\}',new) for k in g.split(',')}<=set(bibs)
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',new):
 if m[1]=='begin':stack.append(m[2])
 else:assert stack and stack.pop()==m[2]
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
# The old checker reads eleven transition strings plus two vertex lists.
previous=(R/'milestones/56-packing-limit-and-revision/scripts/verify.py').read_text()
fragment=previous[previous.index('quotes=lambda'):previous.index('# Check the cycle')]
exec(compile(fragment,'printed-witness-check','exec'))
assert pairs==118673
block=new.split(r'\label{app:pair-012032-witnesses}',1)[1].split(refmarker,1)[0]
quotes_new=re.findall(r'\\begin\{quote\}\\ttfamily\\small\s*(.*?)\\end\{quote\}',block,re.S)
paths=read(R/'milestones/121-replacement-window-pressure/data/boundary-paths.json')['paths']
assert len(quotes_new)==len(paths)==3
for chunk,row in zip(quotes_new,paths):
 ds=[int(x) for x in re.findall(r'\d',chunk)];vs=[row['order'][0]]
 for d in ds:vs.append(vs[-1]^(1<<d))
 assert vs==row['order'];pairs+=check_path(vs,9);S=set(vs);r=row['start']
 counts=[sum(all(w not in S for w in [vs[r+k]^(1<<a),vs[r+k]^(1<<b),vs[r+k]^(1<<a)^(1<<b)]) for a,b in itertools.combinations(range(9),2)) for k in range(1,6)]
 assert counts==row['counts'] and [counts[1],counts[3]]==row['pair']
 assert all((vs[e]^vs[r+k]).bit_count()==2 for e in [0,len(vs)-1] for k in [2,4])
assert pairs==148857
assert 39*25-235+8==748 and 36*235-8431==29
assert 38*25-229+8==729 and 38*26-229+8==767
assert 39*24-235+8==709 and 39*23-235+8==670
assert 36*235+744+12==9216 and 36*235+705+50==9215
assert (9214-36*234-764)//2==13
assert 1378-20==1358 and 85+19+1==105 and 85+38+3==126
assert Fraction(1098960*6+8*2915+3460,4200*6+2915)==Fraction(1324108,5623)
assert Fraction(1098960+8*496+602,4200+496)==Fraction(551765,2348)
assert 111960*6-227*2915==10055
assert Fraction(1323416,5623)>235 and Fraction(137866,587)>234
assert 4683114-10082==4673032
# Reuse complete pinned reviews. Recheck their receipt/source/object/log bytes;
# this is not a fresh Lean run or independent clean dependency rebuild.
review_paths=[
 '120-nine-transition-window/data/final-receipt-review.json',
 '121-replacement-window-pressure/data/final-receipt-review.json',
 '122-endpoint-equality/data/proof-review.json',
 '123-six-count-recovery/data/proof-review.json',
 '124-six-count-cycle-pressure/data/proof-review.json',
 '125-critical-six-count/data/proof-review.json',
 '125-critical-six-count/data/proof-supplement.json']
rows=[];source_pins={};report_count=0
for rp in review_paths:
 p=R/'milestones'/rp;j=read(p);assert j['status'].startswith('PASS_')
 source_pins[p.relative_to(R).as_posix()]=sha(p)
 for entry in j.get('modules',[j.get('module')]):
  assert isinstance(entry,dict)
  rec=R/entry['receipt'];assert sha(rec)==entry['receipt_sha256'];q=read(rec);base=rec.parents[1]
  assert q['exit_code']==0 and not q.get('timeout',False) and q['status'].startswith('PASS_')
  name=q['module'];rel=Path(*name.split('.'))
  candidates=[base/'lean'/(name+'.lean'),base/'lean'/rel.with_suffix('.lean')]
  sources=[s for s in candidates if s.exists() and sha(s)==q['source_sha256']]
  assert sources,('source',name)
  source=sources[0];obj=next((base/d/rel.with_suffix('.olean') for d in ['build-isolated','build'] if (base/d/rel.with_suffix('.olean')).exists()),None)
  assert obj and sha(obj)==q['olean_sha256']==entry['object_sha256'],('object',name)
  log=base/q['log'];snap=base/q['source_snapshot']
  assert sha(log)==q['log_sha256']==entry['log_sha256']
  assert sha(snap)==sha(source)==entry['source_sha256']
  assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['theorem_audits'])
  report_count+=len(q['theorem_audits'])
  for f in [rec,source,obj,log,snap]:source_pins[f.relative_to(R).as_posix()]=sha(f)
  rows.append(dict(module=name,receipt=rec.relative_to(R).as_posix()))
# Additional complete witness supporting the falsified five-count candidate.
p=R/'milestones/119-shared-five-count-pressure/data/Counterexample119-audit.json';q=read(p);base=p.parents[1]
assert q['exit_code']==0 and not q['timeout']
for f,d in [(base/'lean/Counterexample119.lean',q['source_sha256']),(base/'build-geometry/Counterexample119.olean',q['olean_sha256']),(base/q['log'],q['log_sha256'])]:
 assert sha(f)==d;source_pins[f.relative_to(R).as_posix()]=d
source_pins[p.relative_to(R).as_posix()]=sha(p)
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['theorem_audits'])
report_count+=len(q['theorem_audits']);rows.append(dict(module=q['module'],receipt=p.relative_to(R).as_posix()))
for rp in ['117-cycle-sum-refinement/data/middle5-outer16/results.json','119-shared-five-count-pressure/data/full-critical23/results.json','120-nine-transition-window/data/outer3/results.json','121-replacement-window-pressure/data/pair-graph/results.json','124-six-count-cycle-pressure/data/graph-26-25-25/results.json','125-critical-six-count/data/next-encoding-task.json']:
 p=R/'milestones'/rp;source_pins[p.relative_to(R).as_posix()]=sha(p)
out=dict(status='PASS_REVISED_SOURCE_WITNESSES_ARITHMETIC_AND_REUSED_RECEIPTS',paper_sha256=sha(paper),prior_statements=138,current_statements=145,unchanged_prior_statements=135,clarified_prior_statement_labels=sorted(allowed),added_statements=7,named_definitions=1,new_definitions=0,metadata_preserved=True,prior_appendices_preserved=True,editor_identical=True,printed_snakes=16,vertex_pair_checks=pairs,labels=len(labels),references=len(bibs),references_resolved=True,reused_modules=len(rows),printed_axiom_reports=report_count,new_lean_checks=0,source_pins=source_pins,receipts=rows,scope='Manuscript checks and reused evidence. No new unconditional bound, new solver run, fresh Lean compilation, full graph scan or independent contributor-proof rebuild. Ordinary empty-square conversion checked mathematically; existing Lean statements use four anchored occurrences per square. PDF compilation failed before TeX in the Windows helper.')
(H/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['source_pins','receipts']},indent=2))
