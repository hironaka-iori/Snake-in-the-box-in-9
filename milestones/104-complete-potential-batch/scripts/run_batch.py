"""Resume the complete sequential batch; receipts, never generated files, count as proofs."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, subprocess, sys, time

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('--max-groups',type=int,default=0);args=parser.parse_args()
plan=read(HERE/'data/plan.json');plan_hash=sha(HERE/'data/plan.json')
checker_hash=sha(HERE/'scripts/check.py');generator_hash=sha(HERE/'scripts/generate.py')
lock=HERE/'data/batch.lock';progress=HERE/'data/batch-progress.json'
run=str(time.time_ns());log=HERE/'logs'/('batch-'+run+'.log')
with lock.open('x') as out:json.dump(dict(pid=os.getpid(),log=str(log)),out)
state=dict(status='STARTING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    plan_sha256=plan_hash,checker_sha256=checker_hash,generator_sha256=generator_hash,
    selected=[],active=None,remaining_groups=len(plan['groups']),complete_graph_potential_certificates_checked=False)
child=None

def save():
    counts={p:sum(x['profile']==p for x in plan['existing']) for p in ['completed','conditional']}
    for g in state['selected']:counts[g['profile']]+=len(g['contexts'])
    state['contexts_checked_by_profile']=counts
    state['contexts_remaining_by_profile']={p:791-n for p,n in counts.items()}
    state['remaining_groups']=len(plan['groups'])-len(state['selected'])
    state['updated_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    tmp=progress.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2)+'\n');os.replace(tmp,progress)

def receipt(name):
    path=HERE/'data'/(name+'-audit.json')
    if not path.exists():return None
    r=read(path)
    assert r['status']=='PASS_COMPLETE_BATCH_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(HERE/'lean'/(name+'.lean'))==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/'build'/(name+'.olean'))==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits'])
    return r

def check(name):
    global child
    r=receipt(name)
    if r:return r
    assert sha(HERE/'scripts/check.py')==checker_hash
    assert sha(HERE/'scripts/generate.py')==generator_hash and sha(HERE/'data/plan.json')==plan_hash
    before=set((HERE/'logs').glob(name+'-*-record.json'))
    with log.open('a',encoding='utf-8') as out:
        child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(HERE/'scripts/check.py'),name],stdout=out,stderr=subprocess.STDOUT)
        state['active']=dict(module=name,checker_pid=child.pid);save()
        code=child.wait();child=None
    state['active']=None;save()
    if code==0:
        r=receipt(name);assert r is not None;return r
    fresh=set((HERE/'logs').glob(name+'-*-record.json'))-before
    assert len(fresh)==1,('Checker failed before a completed compile record',name,str(log))
    r=read(fresh.pop())
    if r['timeout']:return None
    raise RuntimeError(('Lean error; inspect the preserved log before resuming',name,r['log']))

save()
try:
    for path,digest in plan['inputs_sha256'].items():assert sha(ROOT/path)==digest,path
    env=read(HERE/'data/environment.json')
    for kind in ['sources','receipts','objects']:
        for path,digest in env[kind].items():assert sha(ROOT/path)==digest,path
    assert check('GraphAssembly104') is not None
    state['status']='RUNNING';save();fresh_count=0
    for g in plan['groups']:
        for v in g['variants']:
            assert sha(HERE/'lean'/(v['module']+'.lean'))==v['source_sha256']
        cached=next(((v,receipt(v['module'])) for v in g['variants'] if (HERE/'data'/(v['module']+'-audit.json')).exists()),None)
        if cached:v,r=cached
        else:
            r=None
            for v in g['variants']:
                r=check(v['module'])
                if r is not None:break
            if r is None:raise RuntimeError(('Both methods exceeded their limits',g['profile'],g['index']))
            fresh_count+=1
        expected={f"Snake9.{v['module']}.{g['profile']}_context_{d}_{q}" for d,q in g['contexts']}
        assert expected<={a['theorem'] for a in r['theorem_audits']}
        row=dict(profile=g['profile'],index=g['index'],module=v['module'],method=v['method'],
            contexts=g['contexts'],seconds=r['seconds'],receipt_sha256=sha(HERE/'data'/(v['module']+'-audit.json')))
        state['selected'].append(row);save()
        print('CHECKED',v['module'],len(g['contexts']),'contexts;',state['contexts_checked_by_profile'],flush=True)
        if args.max_groups and fresh_count>=args.max_groups:
            state['status']='STOPPED_AT_REQUESTED_BATCH_LIMIT';break
    else:
        state['status']='ASSEMBLING';save()
        assert sha(HERE/'scripts/generate.py')==generator_hash
        with log.open('a',encoding='utf-8') as out:
            subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/generate.py'),'--assemble'],stdout=out,stderr=subprocess.STDOUT,check=True)
        assert check('AllCompleted104') is not None
        assert check('AllConditional104') is not None
        state.update(status='PASS_COMPLETE_GRAPH_POTENTIAL_CERTIFICATES',complete_graph_potential_certificates_checked=True)
except BaseException as exc:
    if child is not None and child.poll() is None:
        subprocess.run(['taskkill','/PID',str(child.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=False)
        child.wait(timeout=30);child=None
    state.update(status='STOPPED',exception=repr(exc),active=None);raise
finally:
    state['stopped_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();lock.unlink()
