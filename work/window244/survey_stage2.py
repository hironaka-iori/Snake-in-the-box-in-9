"""Independent radius-three census, with exact per-solve model snapshots.

Executable evidence only: never establishes a geometric exclusion in Lean.
All cases have one worker, seed 41, and a total 120-second case budget.
"""
import argparse,hashlib,importlib.util,itertools,json,os,pathlib,sys,time
from datetime import datetime,timezone
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244/stage2';OUT.mkdir(parents=True,exist_ok=True)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--solver-packages',type=pathlib.Path)
args=parser.parse_args()
if args.solver_packages:sys.path.insert(0,str(args.solver_packages.resolve()))
sys.path.insert(0,str(ROOT/'milestones/07-window-223/scripts'))
import ortools
import local_window_search as window
from ortools.sat.python import cp_model
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def save(path,value):
    tmp=path.with_suffix('.tmp');tmp.write_bytes((json.dumps(value,indent=2)+'\n').encode());tmp.replace(path)
gate=json.loads((ROOT/'outputs/window244/final-verification.json').read_text())
assert gate['status']=='VERIFIED_191_244'
assert sha(ROOT/'outputs/window244/final-reproduction-manifest.json')==gate['manifest_sha256']
guard=(OUT/'survey.lock').open('a+b');guard.write(b'0');guard.flush();guard.seek(0)
if os.name=='nt':
    import msvcrt
    msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
else:
    import fcntl
    fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
patterns=[p for p in itertools.product(range(1,8),repeat=3)
          if sum(p)<=9 and p<=p[::-1]
          and all(not ((a==1 and b<4) or (b==1 and a<4)) for a,b in zip(p,p[1:]))]
assert len(patterns)==24
sources=[pathlib.Path(__file__),pathlib.Path(window.__file__),
         ROOT/'work/exact_search.py',ROOT/'work/low_singleton_radius3.py']
identity=dict(code_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in sources},
              solver='OR-Tools CP-SAT',solver_version=ortools.__version__,
              workers=1,seed=41,case_seconds_limit=120,radius=3)
manifest=OUT/'survey.json'
state=json.loads(manifest.read_text()) if manifest.exists() else dict(cases={})
if 'identity' in state:assert state['identity']==identity,'Code/version changed: retain this census and use a new output directory'
state.update(identity=identity,status='RUNNING',pid=os.getpid(),
             started_utc=state.get('started_utc',now()),patterns=patterns,
             scope='SOLVER_ONLY; UNKNOWN never excludes a pattern',total_cases=48)
state.pop('error',None);save(manifest,state)
original_solve=cp_model.CpSolver.solve
try:
    for pattern in patterns:
        for shape in ['repeated','distinct']:
            key=''.join(map(str,pattern))+'-'+shape
            output=OUT/(key+'.json')
            if key in state['cases']:
                assert sha(output)==state['cases'][key]['result_sha256']
                continue
            state.update(active=key);save(manifest,state)
            traces=[]
            def recorded_solve(solver,model,*a,**kw):
                i=len(traces);base=OUT/(key+f'-solve{i:02d}')
                model_file=base.with_suffix('.pbtxt');model_file.write_bytes(str(model.proto).encode())
                solver.parameters.log_search_progress=True
                solver.parameters.log_to_stdout=False
                parameters_file=base.with_suffix('.parameters.txt')
                parameters_file.write_bytes(str(solver.parameters).encode())
                started=now();tick=time.monotonic()
                with base.with_suffix('.log').open('w',encoding='utf-8') as log:
                    solver.log_callback=lambda message:log.write(message)
                    status=original_solve(solver,model,*a,**kw)
                traces.append(dict(model=model_file.name,model_sha256=sha(model_file),
                    parameters=parameters_file.name,parameters_sha256=sha(parameters_file),
                    solver_log=base.with_suffix('.log').name,
                    log_sha256=sha(base.with_suffix('.log')),started_utc=started,
                    elapsed_seconds=time.monotonic()-tick,status=solver.status_name(status)))
                return status
            cp_model.CpSolver.solve=recorded_solve
            result=window.run(3,shape,pattern,120)
            cp_model.CpSolver.solve=original_solve
            result.update(identity=identity,solve_traces=traces,evidence_level='SOLVER_ONLY')
            save(output,result)
            state['cases'][key]=dict(status=result['status'],result_sha256=sha(output),
                elapsed_seconds=result['elapsed_seconds'],solve_count=len(traces))
            save(manifest,state);print(key,result['status'],round(result['elapsed_seconds'],2),flush=True)
    excluded=[p for p in patterns if all(state['cases'][''.join(map(str,p))+'-'+s]['status']=='INFEASIBLE' for s in ['repeated','distinct'])]
    state.update(status='COMPLETED_SOLVER_ONLY',active=None,completed_utc=now(),
        both_shapes_infeasible=excluded,
        unknown_cases=[k for k,v in state['cases'].items() if v['status']=='UNKNOWN'])
    save(manifest,state)
except BaseException as exc:
    state.update(status='FAILED',error=str(exc));save(manifest,state);raise
finally:
    cp_model.CpSolver.solve=original_solve
    guard.close()
