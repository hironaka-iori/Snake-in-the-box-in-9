"""Fresh certificate for the broad three-count restriction, including saved cycle cuts."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_lean_sat as satgen
from wincert import window_from_dirs
def load(path,name):
    sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
case=read(HERE/'data/probes/012031-outer3-radius3.json');assert case['status']=='UNSAT_UNCERTIFIED'
enc=satgen.TaggedEncoding(window_from_dirs(case['directions']),[tuple(b) for b in case['bounds']],radius=3)
for cut in case['cycle_cuts']:
    assert satgen.is_cycle_set(cut) and all(v in enc.var for v in cut)
    enc.add([-enc.var[v] for v in cut],('cut',))
work=HERE/'work/outer3333';work.mkdir(exist_ok=True);name='outer3333';mod='Outer3333'
cnf=work/(name+'.cnf');cnf.write_bytes((f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode())
raw=work/'raw.lrat';rp=HERE/'data/outer3333-solver.json';assert not rp.exists() and not raw.exists()
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
args=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)];start=time.monotonic()
out=dict(command=args,solver_sha256=sha(exe),cnf_sha256=sha(cnf),timeout_seconds=60)
try:
    p=subprocess.run(args,capture_output=True,text=True,timeout=60)
    (HERE/'logs/outer3333-solver.stdout.txt').write_text(p.stdout);(HERE/'logs/outer3333-solver.stderr.txt').write_text(p.stderr)
    out.update(status='NATIVE_UNSAT_LEAN_PENDING' if p.returncode==20 and 's UNSATISFIABLE' in p.stdout else 'FAILED',exit_code=p.returncode,seconds=time.monotonic()-start)
except subprocess.TimeoutExpired as exc:out.update(status='TIMEOUT',seconds=time.monotonic()-start)
finally:
    if raw.exists():out['raw_sha256']=sha(raw)
    rp.write_text(json.dumps(out,indent=2)+'\n')
assert out['status']=='NATIVE_UNSAT_LEAN_PENDING',out
old=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts'
gen=load(old/'gen_lean_core.py','gcore120');trim=work/(name+'.lrat')
nl,nh,ids=gen.trim_lrat(str(raw),str(trim),len(enc.clauses))
assert enc.nv<2400
meta=dict(module='LocalWindowCnf.'+mod,dirs=case['directions'],window=enc.window,bounds=case['bounds'],radius=3,cnf_clauses=len(enc.clauses),core_ids=ids)
(HERE/'data/meta').mkdir(exist_ok=True);(HERE/'data/meta'/(name+'.json')).write_text(json.dumps(meta,indent=2)+'\n')
generated=HERE/'generated';(generated/'LocalWindowCnf').mkdir(parents=True,exist_ok=True)
body=',\n  '.join(str([satgen.code(v) for v in enc.clauses[i-1]]) for i in ids)
src=f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
def window : List Nat := winOf {case['directions']}
def bounds : List (Nat × Nat) := {[tuple(b) for b in case['bounds']]}
def raw : List (List Nat) := [
  {body}]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
'''
(generated/'LocalWindowCnf'/(mod+'.lean')).write_text(src,encoding='utf-8')
satgen.LEAN=str(generated);satgen.write_module(name,mod,meta,enc,[enc.tags[i-1] for i in ids])
lr=load(old/'gen_lean_lrat.py','glrat120');lr.set_width(13,fast=True,off=2400);lr.DATA_DEF='noncomputable def'
stats=lr.export(name,str(work),6000,2,1,True,str(generated),str(HERE/'data/meta'))
mods=['LocalWindowCnf.'+mod,'LocalWindowSat.'+mod]
mods+=['LocalWindowUnsat.'+mod+'.Data'+str(i) for i in range(stats['segments']+1)]
mods+=['LocalWindowUnsat.'+mod+'.Check'+str(i+1) for i in range(stats['check_modules'])]
mods+=['LocalWindowUnsat.'+mod];ports=[]
for module in mods:
    p=generated/(module.replace('.','/')+'.lean');txt=p.read_text()
    dest=HERE/'lean/Recovered120'/p.relative_to(generated);dest.parent.mkdir(parents=True,exist_ok=True)
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.'+mod+r'(?:\.[A-Za-z0-9]+)?)$',r'import Recovered120.\1',txt,flags=re.M)
    dest.write_text(changed,encoding='utf-8');assert re.sub(r'^import Recovered120\.',r'import ',changed,flags=re.M)==txt
    ports.append(dict(original=p.relative_to(HERE).as_posix(),source_sha256=sha(p),isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest)))
pins={p.relative_to(ROOT).as_posix():sha(p) for p in [old/'gen_lean_core.py',old/'gen_lean_lrat.py',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',ROOT/'milestones/10-window-aggregate/scripts/wincert.py']}
out=dict(status='GENERATED_NOT_CHECKED',modules=['Recovered120.'+m for m in mods],ports=ports,generation=stats,
    core_clauses=len(ids),variables=enc.nv,clauses=len(enc.clauses),lemmas=nl,hints=nh,lrat_sha256=sha(trim),cnf_sha256=sha(cnf),
    cycle_cuts=case['cycle_cuts'],source_files_sha256=pins,script_sha256=sha(Path(__file__)))
(HERE/'data/outer3333-plan.json').write_text(json.dumps(out,indent=2)+'\n')
print('Generated',len(mods),'modules,',len(ids),'core clauses,',nl,'deductions,',nh,'hints',flush=True)
