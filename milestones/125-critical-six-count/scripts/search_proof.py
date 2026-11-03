"""Changed full-Q9 search: CaDiCaL2.1.2 with LRAT and symmetry images of saved cycle cuts."""
from pathlib import Path
from itertools import combinations,permutations
import argparse,datetime,hashlib,importlib.util,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--cap',type=int,required=True);ap.add_argument('--seconds',type=int,default=120)
ap.add_argument('--extra-cuts');ap.add_argument('--suffix',default='orbit');args=ap.parse_args()
assert args.cap in [22,23,24] and 0<args.seconds<=180
assert args.suffix.isalnum()
sys.dont_write_bytecode=True
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'milestones/28-direct-share-certificates/scripts'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding,is_cycle_set
from wincert import window_from_dirs
from direct import census
source=R/'milestones/124-six-count-cycle-pressure/data/probes/0120324-universal-total24-resume.json'
prior=read(source);assert prior['status']=='UNKNOWN' and len(prior['cycle_cuts'])==8
dirs=[0,1,2,0,3,2,4];assert prior['directions']==dirs
name=f'0120324-total{args.cap}-{args.suffix}'
work=H/'work'/name;work.mkdir();(H/'data/probes').mkdir(exist_ok=True)
pins={p.relative_to(R).as_posix():sha(p) for p in [source,R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',R/'milestones/10-window-aggregate/scripts/wincert.py',R/'milestones/28-direct-share-certificates/scripts/direct.py']}
for p,d in prior['source_files_sha256'].items():assert sha(R/p)==d
cuts=set();provenance=[]
seeds=list(prior['cycle_cuts'])
if args.extra_cuts:
 p=R/args.extra_cuts;j=read(p);assert j['status']=='NATIVE_CYCLIC_MODEL'
 pins[p.relative_to(R).as_posix()]=sha(p);seeds+=j['census']['cycles']
for index,cut in enumerate(seeds):
 assert is_cycle_set(cut)
 for perm in permutations(range(5,9)):
  image=tuple(sorted((v&31)|sum(((v>>a)&1)<<b for a,b in zip(range(5,9),perm)) for v in cut))
  assert is_cycle_set(image)
  if image not in cuts:provenance.append(dict(seed=index,permutation=list(perm),vertices=list(image)))
  cuts.add(image)
cuts=[list(c) for c in sorted(cuts)]
enc=TaggedEncoding(window_from_dirs(dirs),[(0,21)]*6,radius=9)
lits=[]
for i in range(1,7):
 c=enc.window[i];used={dirs[i-1],dirs[i]}
 lits += [-enc.var[c^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if a not in used and b not in used]
lits.sort();assert len(lits)==126 and len(set(lits))==100
enc.atmost(lits,args.cap,('unproved_sum',))
for cut in cuts:enc.add([-enc.var[v] for v in cut],('cut',))
cnf=work/'full.cnf';raw=work/'full.raw.lrat';trim=work/'full.trim.lrat'
cnf.write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode())
case=dict(name=name,directions=dirs,window=enc.window,bounds=[[0,21]]*6,positions=list(range(6)),cap=args.cap,radius=9,
 cycle_cuts=cuts,seed_cuts=seeds,cut_provenance=provenance,literal_occurrences=126,distinct_literals=100,
 variables=enc.nv,clauses=len(enc.clauses),source_files_sha256=pins,script_sha256=sha(Path(__file__)))
probe=H/'data/probes'/(name+'.json')
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
out=dict(command=command,solver_sha256=sha(exe),cnf_sha256=sha(cnf),timeout_seconds=args.seconds,
 script_sha256=sha(Path(__file__)),status='RUNNING',pid=os.getpid(),source_files_sha256=pins,cycle_cuts=cuts,
 started_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
record=H/'data'/(name+'-solver.json');assert not record.exists()
stdout=H/'logs'/(name+'-solver.stdout.txt');stderr=H/'logs'/(name+'-solver.stderr.txt')
start=time.monotonic();record.write_text(json.dumps(out,indent=2)+'\n')
with stdout.open('wb') as so,stderr.open('wb') as se:
 proc=subprocess.Popen(command,stdout=so,stderr=se)
 out['solver_pid']=proc.pid;record.write_text(json.dumps(out,indent=2)+'\n')
 try:
  code=proc.wait(timeout=args.seconds);text=stdout.read_text(errors='replace')
  out.update(exit_code=code,status='NATIVE_UNSAT_LEAN_PENDING' if code==20 and 's UNSATISFIABLE' in text else 'NATIVE_SAT' if code==10 and 's SATISFIABLE' in text else 'FAILED')
 except subprocess.TimeoutExpired:
  proc.kill();proc.wait(timeout=15);out.update(status='TIMEOUT',exit_code=proc.returncode)
out.update(seconds=time.monotonic()-start,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),raw_sha256=sha(raw),raw_bytes=raw.stat().st_size)
case.update(status=out['status'],selected=None,census=None)
if out['status']=='NATIVE_SAT':
 vals=[int(v) for line in stdout.read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'];assigned=set(vals)
 assert all(any(x in assigned for x in clause) for clause in enc.clauses)
 selected={v for v in enc.ball if enc.var[v] in assigned};report=census(selected,9,enc.window[1:-1]);report.pop('degree')
 assert sum(report['alpha'])<=args.cap
 case.update(status='NATIVE_CYCLIC_MODEL' if report['cycles'] else 'SAT_FULL_PATH_CANDIDATE',selected=sorted(selected),census=report)
case.update(solver_record=record.relative_to(R).as_posix())
probe.write_text(json.dumps(case,indent=2)+'\n');out['probe_sha256']=sha(probe)
record.write_text(json.dumps(out,indent=2)+'\n')
print(name,out['status'],'cuts',len(cuts),'seconds',round(out['seconds'],3),flush=True)
if case['census']:print('MODEL',case['status'],case['census']['alpha'],'cycles',len(case['census']['cycles']),flush=True)
if out['status']!='NATIVE_UNSAT_LEAN_PENDING':sys.exit(0)
path=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
sp=importlib.util.spec_from_file_location('trim125',path);gen=importlib.util.module_from_spec(sp);sp.loader.exec_module(gen)
nl,nh,ids=gen.trim_lrat(str(raw),str(trim),len(enc.clauses));core=work/'core.cnf'
core.write_bytes((f'p cnf {enc.nv} {len(ids)}\n'+''.join(' '.join(map(str,enc.clauses[i-1]))+' 0\n' for i in ids)).encode())
meta=dict(status='TRIMMED_OVER_HINT_LIMIT_NOT_REPLAYED',window=enc.window,bounds=case['bounds'],directions=dirs,radius=9,
 cycle_cuts=cuts,positions=case['positions'],sum_cap=args.cap,sum_counter=len(enc.ctrs)-1,literal_occurrences=126,distinct_literals=100,
 variables=enc.nv,clauses=len(enc.clauses),core_ids=ids,core_clauses=len(ids),lemmas=nl,hints=nh,
 cnf_sha256=sha(cnf),core_sha256=sha(core),lrat_sha256=sha(trim),probe_sha256=sha(probe),trimming_generator_sha256=sha(path),
 script_sha256=sha(Path(__file__)),source_files_sha256=pins,solver_record_sha256=sha(record))
if nh<=2_000_000:
 db={i:enc.clauses[i-1] for i in ids};last=len(enc.clauses);added=hints=0
 with trim.open() as f:
  for line in f:
   row=list(map(int,line.split()));z=row.index(0,1);cid,clause,hs=row[0],row[1:z],row[z+1:-1]
   assert row[-1]==0 and cid>last and all(0<h<cid for h in hs)
   assigned={-x for x in clause};contradiction=any(-x in assigned for x in assigned)
   for h in hs:
    premise=db[h]
    if contradiction or any(x in assigned for x in premise):continue
    rest={x for x in premise if -x not in assigned};assert len(rest)<=1
    if not rest:contradiction=True
    else:assigned.add(next(iter(rest)))
   assert contradiction;db[cid]=clause;last=cid;added+=1;hints+=len(hs)
 assert db[last]==[] and added==nl and hints==nh
 meta['status']='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING'
for p,d in pins.items():assert sha(R/p)==d
meta['scope']='Full-cube formula and native certificate only. Concrete semantics, Lean replay and actual-snake transfer remain pending.'
(H/'data'/(name+'-certificate.json')).write_text(json.dumps(meta,indent=2)+'\n')
print(meta['status'],len(ids),'inputs',nl,'deductions',nh,'hints',flush=True)
