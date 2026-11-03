"""Freeze checked counterexamples without promoting the written geometric bound."""
from pathlib import Path
from itertools import combinations
import ast,datetime,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pins(rows):
 for n,d in rows.items():
  p=Path(n);assert sha(p if p.is_absolute() else R/p)==d,n
reports=[]
for name,count in [('Witness133',8),('BalancedWitness133',8),('IntervalPacking133',2),('OccurrenceArithmetic133',2)]:
 q=read(H/'data'/(name+'-audit.json'));assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout')
 source=H/'lean'/(name+'.lean');assert sha(source)==q['source_sha256']
 assert sha(Path(q['log']).parent/'source.lean.txt')==q['source_sha256']
 assert sha(Path(q['log']).parent/'checker.py.txt')==q['checker_sha256']
 for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
 pins(q['dependencies']);assert len(q['axioms'])==count
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8'))
 reports.extend(q['axioms'])
for folder,name,m,r,pair in [('probe-endpoint18','Witness133',149,130,[6,3]),
 ('probe-balanced','BalancedWitness133',133,27,[4,5])]:
 f=H/'work'/folder;j=read(f/'actual-path.json');q=read(f/'independent-path-review.json')
 source=(H/'lean'/(name+'.lean')).read_text(encoding='utf-8')
 values=ast.literal_eval(re.search(r'def values : Array Nat := #(\[[^\n]*\])',source).group(1))
 assert values==j['ordered_path'] and len(values)==m+1 and len(set(values))==m+1
 assert all(0<=v<512 for v in values) and values[r:r+7]==[0,1,3,7,6,14,10]
 assert j['edges']==m and j['window_start']==r and j['pair_sum']==9
 assert [j['counts'][i]['alpha'] for i in [1,3]]==pair
 assert sha(f/'actual-path.json')==q['witness_sha256'] and sha(f/'final.cnf')==q['final_cnf_sha256']
 assert q['status'].startswith('PASS_INDEPENDENT') and q['unordered_pairs_checked']==m*(m+1)//2
for folder,expected in [('probe-endpoint0','UNSAT_UNCERTIFIED'),
 ('probe-endpoint18','ACTUAL_ODD_ENDPOINT18_PATH_CHECKED'),('probe-balanced','ACTUAL_ODD_BALANCED_PAIR_PATH_CHECKED')]:
 f=H/'work'/folder;w=read(f/'worker-status.json');assert w['status']==expected
 assert sha(f/'final.cnf')==w['final_cnf_sha256'] and sha(f/'probe.exact.py')==w['script_sha256']
 pins(w['source_files_sha256'])
 p=H/'data/preparation.json' if folder=='probe-endpoint0' else f/'preparation.json'
 assert sha(p)==w['preparation_sha256']
 assert not (f/'probe.lock').exists()
boundary=read(H/'work/probe-endpoint0/worker-status.json')
assert boundary['models']==0 and boundary['cycle_cuts']==[]
geo=read(H/'data/occurrence-geometry.json')
assert geo['status']=='WRITTEN_GEOMETRIC_BOUND_WITH_BOUNDED_NATIVE_CHECKS'
assert geo['result']['one_endpoint_max']==12 and geo['result']['without_counted_boundary_window_max']==11
assert not geo['result']['lean_checked'] and not geo['result']['new_global_length_bound']
for n,row in geo['source_pins'].items():assert sha(R/n)==row['sha256']
assert sha(geo['audit_report']['path'])==geo['audit_report']['sha256']
# Reproduce the small integer reduction and exceptional double count.
cases=[]
for a in range(1,8):
 for k in range(a,9):
  for t in range(29):
   if min(7*a-a*(a-1)//2-t-2*k+1,k*(5-a+t)-t+2)>=13:cases.append([a,k,t])
assert cases==[[5,5,3]]
A=set(range(5));B=set(range(5,8));edges=[e for e in combinations(range(8),2) if A.intersection(e)]
checked=0
for missing in combinations(edges,3):
 d={u:sum(u in e for e in missing) for u in A}
 s={u:sum(u in e and bool(B.intersection(e)) for e in missing) for u in A}
 assert sum(d[u]+s[u] for u in A)==6
 assert sum(s[u]==3 for u in A)<=1
 checked+=1
assert checked==2300
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
 assert sha(paper)==sha(editor)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
 verification=dict(status='PASS_CHECKED_COUNTEREXAMPLES_AND_CONDITIONAL_OCCURRENCE_LEMMAS',
  recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),checked_witness_lengths=[149,133],
  checked_pair_counts=[[6,3],[4,5]],axiom_reports=len(reports),
  native_boundary_exclusion_certified=False,actual_occurrence_bound_lean_checked=False,
  written_per_endpoint_bound=12,written_without_boundary_bound=11,
  interval_union_lemma_lean_checked=True,conditional_integer_reduction_lean_checked=True,
  exceptional_missing_edge_cases_reproduced=checked,new_global_length_bound=False,
  scope='Two actual counterexamples are proved. The occurrence argument has a written proof and checked sublemmas; its actual-snake geometric transfer remains pending.')
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='ce0b3c6a405a793662c304f5648f1b85c98ecce2',
  prior_checkpoint_sha256=sha(R/'milestones/132-odd-pair-endpoint/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),batch_observation_sha256=sha(H/'data/batch-observation.json'),
  current_interval=[191,235],interval_scope='Maintained contributor result with incomplete independent upper-proof rebuild.',
  paper_revision=126,next_paper_revision=136,paper_sha256=sha(paper),
  selected_next_task='Complete the actual-snake geometric transfer for the written per-endpoint occurrence bound.')
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts
  and p.suffix not in ['.tmp','.lock','.pending'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
  'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_COUNTEREXAMPLES_AND_OCCURRENCE_DERIVATION133',files=rows,
  excluded_live_outputs='Other milestones remain live locally; frozen observations are included.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for x in j['files']:
 p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()}
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
if '--stage' in sys.argv:
 assert not subprocess.check_output(g+['diff','--cached','--name-only'],cwd=R).strip()
 p=H/'data/stage-paths.nul';p.write_bytes(b''.join(n.encode()+b'\0' for n in sorted(names)))
 subprocess.run(g+['add','-f','--pathspec-from-file='+str(p),'--pathspec-file-nul'],cwd=R,check=True)
if '--staged' in sys.argv:
 actual=set(subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).decode().strip('\0').split('\0'));assert actual==names
 proc=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for n in sorted(names):
  proc.stdin.write((':'+n+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().decode().split();assert header[1]=='blob'
  b=proc.stdout.read(int(header[2]));assert proc.stdout.read(1)==b'\n'
  expected=(R/n).read_bytes()
  if not n.startswith('milestones/133-endpoint-occurrences/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),
 bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,axiom_reports=len(reports),
 actual_occurrence_bound_lean_checked=False,new_global_length_bound=False)))
