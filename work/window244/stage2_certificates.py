"""Proof-logging solves for one minimum five-pattern set; no Lean claim.

The chosen set reuses 232/414 for a possible intermediate 243 bound, then
adds 141/224/323 for the numerically sufficient 242 set. Each actual solve
records its input/solver/code hashes, version, seed, threads, limit and time.
"""
import argparse,hashlib,json,os,pathlib,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244/stage2/certificates';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'milestones/07-window-223/scripts'))
from window_cnf import encode
from audit_window_encoding import replay
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--solver',type=pathlib.Path,required=True)
args=parser.parse_args();solver=args.solver.resolve()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,s):
    tmp=p.with_suffix('.tmp');tmp.write_bytes((json.dumps(s,indent=2)+'\n').encode());tmp.replace(p)
guard=(OUT/'build.lock').open('a+b');guard.write(b'0');guard.flush();guard.seek(0)
if os.name=='nt':
    import msvcrt
    msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
else:
    import fcntl
    fcntl.flock(guard,fcntl.LOCK_EX|fcntl.LOCK_NB)
minimum=json.loads((OUT.parent/'minimal-patterns.json').read_text())
chosen=[(2,3,2),(4,1,4),(1,4,1),(2,2,4),(3,2,3)]
assert any(set(map(tuple,s['patterns']))==set(chosen) for s in minimum['minimum_sets']['242']['sets'])
identity=dict(solver=str(solver),solver_sha256=sha(solver),
    version=subprocess.check_output([str(solver),'--version'],text=True).strip(),
    seed=41,threads=1,seconds_limit=120,wall_kill_seconds=120,
    code_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in
        [pathlib.Path(__file__),ROOT/'milestones/07-window-223/scripts/window_cnf.py',
         ROOT/'milestones/07-window-223/scripts/audit_window_encoding.py']})
manifest=OUT/'manifest.json'
state=json.loads(manifest.read_text()) if manifest.exists() else dict(cases={})
if 'identity' in state:assert state['identity']==identity,'Preserve previous run and use a new directory after code/version changes'
state.update(status='RUNNING',pid=os.getpid(),identity=identity,
             chosen_patterns=chosen,scope='SOLVER_AND_EXECUTABLE_REPLAY_ONLY')
state.pop('error',None);save(manifest,state)
try:
    for pattern in chosen:
        for shape in ['repeated','distinct']:
            key=''.join(map(str,pattern))+'-'+shape
            if key in state['cases']:
                prior=state['cases'][key]
                if prior.get('replay_status')=='PASSED':
                    assert sha(OUT/(key+'_core.json'))==prior['core_sha256']
                    continue
            case=json.loads((OUT.parent/(key+'.json')).read_text())
            assert case['status']=='INFEASIBLE'
            model=encode(case,True);prefix=OUT/key
            modelpath=prefix.with_suffix('.json');save(modelpath,model)
            cnf=prefix.with_suffix('.cnf');proof=prefix.with_suffix('.lrat')
            cnf.write_bytes((f'p cnf {max(model["variables"].values())} {len(model["clauses"])}\n'+
                ''.join(' '.join(map(str,c))+' 0\n' for c in model['clauses'])).encode())
            # The Lean-bundled Windows executable has no POSIX -t alarm option.
            # Apply the recorded wall limit externally instead.
            command=[str(solver),'--lrat','--no-binary','--seed=41',str(cnf),str(proof)]
            rec=dict(command=command,cnf_sha256=sha(cnf),model_sha256=sha(modelpath),
                census_result_sha256=sha(OUT.parent/(key+'.json')),status='RUNNING')
            state.update(active=key);state['cases'][key]=rec;save(manifest,state)
            tick=time.monotonic()
            try:
                with prefix.with_suffix('.log').open('w',encoding='utf-8') as log:
                    result=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=120)
                rec.update(exit_code=result.returncode,status={20:'UNSAT',10:'SAT',0:'UNKNOWN'}.get(result.returncode,'ERROR'))
            except subprocess.TimeoutExpired:
                rec.update(exit_code=None,status='UNKNOWN_WALL_TIMEOUT')
            rec.update(elapsed_seconds=time.monotonic()-tick,log_sha256=sha(prefix.with_suffix('.log')))
            save(manifest,state)
            if rec['status']!='UNSAT':raise RuntimeError(f'{key}: {rec["status"]}; no exclusion inferred')
            rec['independent_replay']=replay(str(prefix))
            # Backward core trimming, separate from the deletion-aware replay above.
            actions={}
            for line in proof.read_text().splitlines():
                fields=line.split()
                if fields[1]=='d':continue
                values=list(map(int,fields));z=values.index(0)
                clause,hints=values[1:z],values[z+1:-1]
                assert all(i>0 for i in hints),'Only RUP supported by this exporter'
                actions[values[0]]=(clause,hints)
            last=max(actions);assert actions[last][0]==[]
            used=set();pending=[last]
            while pending:
                cid=pending.pop()
                if cid in used:continue
                used.add(cid)
                if cid in actions:pending.extend(actions[cid][1])
            count=len(model['clauses'])
            inputs=sorted(i for i in used if i<=count)
            added=sorted(i for i in used if i>count)
            mapping={old:new for new,old in enumerate(inputs+added,1)}
            db={mapping[i]:model['clauses'][i-1] for i in inputs};steps=[]
            for cid in added:
                clause,hints=actions[cid];hh=[mapping[i] for i in hints]
                assigned=set(-v for v in clause);closed=False
                for h in hh:
                    needed=[v for v in db[h] if -v not in assigned]
                    assert not any(v in assigned for v in needed)
                    if not needed:closed=True;break
                    assert len(needed)==1
                    assigned.add(needed[0])
                assert closed
                db[mapping[cid]]=clause;steps.append((mapping[cid],clause,hh))
            core=dict(clauses=[model['clauses'][i-1] for i in inputs],
                reasons=[model['reasons'][i-1] for i in inputs],
                original_clause_indices=inputs,proof=steps)
            corepath=OUT/(key+'_core.json');save(corepath,core)
            rec.update(replay_status='PASSED',core_sha256=sha(corepath),
                core_clauses=len(inputs),core_steps=len(steps),lrat_sha256=sha(proof))
            save(manifest,state)
            print(key,'REPLAYED',len(inputs),'clauses',len(steps),'steps',flush=True)
    state.update(status='PASSED_EXECUTABLE_REPLAY_ONLY',active=None);save(manifest,state)
except BaseException as exc:
    state.update(status='FAILED',error=str(exc));save(manifest,state);raise
finally:guard.close()
