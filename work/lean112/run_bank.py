"""Resumable full KEEP=112 proof build. Counts only audited bank theorems."""
import argparse,concurrent.futures,hashlib,json,msvcrt,os,re,subprocess,sys,threading,time,traceback
from pathlib import Path
from service import ROOT,OUT,HERE,read,save,event,now
from export_local_rup import emit as emit_boolean
from generate_cover import emit as emit_cover,aggregate

BANK=HERE/'bank'
LEAN=ROOT.parent/'Snake in the Box/work/research_20261015/proof/dependencies/lean-4.19.0-windows/bin/lean.exe'
SEARCH=[BANK,HERE,ROOT/'work/lean/sat-first-checked',ROOT/'work/final_lean/.lake/build/lib/lean']
ENV=os.environ.copy();ENV['LEAN_PATH']=';'.join(map(str,SEARCH))
LOGS=OUT/'bank-logs';LOGS.mkdir(exist_ok=True)
LOCK=threading.RLock()
AXIOMS={'propext','Classical.choice','Quot.sound'}
records=read(OUT/'bank-module-checks.json',{}).get('modules',{})
state=read(OUT/'bank-proof.json',dict(status='IN_PROGRESS',entries={},representatives={},failures={},active={}))
state.setdefault('active',{})
state.setdefault('failures',{})
cover=read(OUT/'cover.json')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def src(name):
    for folder in [BANK,HERE,ROOT/'work/final_lean']:
        path=folder/(name+'.lean')
        if path.exists():return path
    raise FileNotFoundError(name)
def obj(name):
    for folder in SEARCH:
        path=folder/(name+'.olean')
        if path.exists():return path
    raise FileNotFoundError(name)
def imports(path):
    result={}
    for name in re.findall(r'^import (\w+)\s*$',path.read_text(encoding='utf-8'),re.M):
        if name=='Std':continue
        try:result[name]=sha(obj(name))
        except FileNotFoundError:pass
    return result
def publish():
    save('bank-proof.json',state)
    done=set(map(int,state['entries']))
    first=read(OUT/'first-geometric-proof.json',{})
    if first.get('status')=='PASSED_FIRST_GEOMETRIC_ENTRY':done.add(0)
    r=read(OUT/'reasoning.json',{})
    active=list(state['active'].values())
    detail=f'完整入口 {len(done)}/262；已完成代表区域 {len(state["representatives"])}/86。'
    if active:detail+=' 当前核验：'+'、'.join(active)+ '。每个模块完成即保存。'
    if state['failures']:detail+=f' 有 {len(state["failures"])} 组需要修复，其余组继续。'
    r.update(status=state['status'],title='112档完整 Lean 证明批量推进',detail=detail,
        formally_certified_entries=len(done),completed_entry_indices=sorted(done),total_entries=262)
    save('reasoning.json',r)

def check(name,worker='setup',force=False):
    source=src(name);target=source.with_suffix('.olean')
    if source.parent==ROOT/'work/final_lean':target=HERE/(name+'.olean')
    code=source.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|native_decide)\b|^\s*axiom\s',code,re.M),name
    fingerprint=sha(source);deps=imports(source)
    with LOCK:
        state['active'][str(worker)]=name;publish()
        rec=records.get(name,{})
    if not force and rec.get('exit_code')==0 and rec.get('source_sha256')==fingerprint and rec.get('imports')==deps and target.exists() and rec.get('olean_sha256')==sha(target):
        return rec
    log=LOGS/(name+'.log');start=time.monotonic()
    print('Checking',name,flush=True)
    with log.open('w',encoding='utf-8') as f:
        result=subprocess.run([str(LEAN),'--root='+str(source.parent),'-o',str(target),str(source)],env=ENV,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
    rec=dict(exit_code=result.returncode,source=str(source.relative_to(ROOT)),source_sha256=fingerprint,
        imports=deps,seconds=round(time.monotonic()-start,3),finished_utc=now(),log=str(log.relative_to(ROOT)))
    if result.returncode==0:rec['olean_sha256']=sha(target)
    with LOCK:
        records[name]=rec
        save('bank-module-checks.json',dict(modules=records))
    if result.returncode:
        raise RuntimeError(name+': '+log.read_text(encoding='utf-8')[-2500:])
    print('Passed',name,rec['seconds'],'seconds',flush=True)
    return rec

def audit(name,theorem):
    output=(LOGS/(name+'.log')).read_text(encoding='utf-8')
    line=next(x for x in output.splitlines() if f"'{theorem}' depends on axioms:" in x)
    match=re.search(r'\[(.*)\]',line);axioms=set(match[1].split(', ')) if match[1] else set()
    assert axioms<=AXIOMS,(name,axioms)
    return sorted(axioms)

def generate_geometry(entry,data_only=False):
    args=[sys.executable,str(HERE/'generate_bank_bridge.py'),str(entry)]
    if data_only:args+=['--data-only']
    p=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,encoding='utf-8')
    if p.returncode:raise RuntimeError(p.stdout+p.stderr)

def build_group(rep):
    worker=str(rep)
    try:
        modules=[]
        if rep==0:
            # First112Reuse is checked during sequential setup; its complete
            # predecessor has a separate, fully verified 203-module receipt.
            modules=['First112Reuse']
        else:
            boolean=emit_boolean(rep)
            generate_geometry(rep)
            survey=read(OUT/'survey.json')['entries']
            owner=survey[str(rep)].get('reused_from',rep)
            c=read(OUT/f'cores/entry{owner:03d}.json');blocks=(len(c['clauses'])+31)//32
            prefix=f'E112{rep:03d}'
            modules=boolean+[prefix+'Data',prefix+'Semantics']+[prefix+f'Clauses{i:02d}' for i in range(blocks)]+[prefix+'Complete']
            for module in modules:check(module,worker)
            audit(prefix+'Complete',f'Snake9.Regrowth.{prefix}.region_exclusion')
        with LOCK:
            state['representatives'][str(rep)]=dict(status='PASSED',modules=modules,finished_utc=now())
            publish()
        entries=[int(i) for i,r in cover['entries'].items() if r['representative']==rep]
        for entry in entries:
            if entry!=rep:
                generate_geometry(entry,True)
                check(f'E112{entry:03d}Data',worker)
            module=emit_cover(entry,rep,cover['entries'][str(entry)]['translation'])
            check(module,worker)
            axes=audit(module,f'Snake9.Regrowth.Bank112.entry{entry}')
            with LOCK:
                state['entries'][str(entry)]=dict(status='PASSED',representative=rep,module=module,
                    axioms=axes,keep_vertices=112,excluded_edges=192,finished_utc=now())
                publish()
                event('bank112','完整112档入口已经过 Lean 核验。',entry=entry,completed=len(state['entries']))
            print('CERTIFIED ENTRY',entry,flush=True)
        with LOCK:
            state['failures'].pop(worker,None)
    except Exception as exc:
        with LOCK:
            state['failures'][worker]=dict(error=str(exc),time_utc=now())
            event('bank112','某一组证明需要修复，已保存断点。',representative=rep,error=str(exc)[-700:])
        print('FAILED GROUP',rep,str(exc),flush=True)
    finally:
        with LOCK:
            state['active'].pop(worker,None);publish()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--workers',type=int,default=2)
    parser.add_argument('--representatives',nargs='*',type=int)
    args=parser.parse_args()
    guard=(OUT/'bank-runner.lock').open('a+b')
    guard.seek(0);guard.write(b'0');guard.flush();guard.seek(0)
    try:msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
    except OSError:raise SystemExit('Another bank proof runner holds the lock.')
    save('bank-runner.json',dict(pid=os.getpid(),status='RUNNING',started_utc=now(),workers=args.workers))
    state.update(status='IN_PROGRESS',active={})
    for name in ['LocalRup','TreeRup','RegrowthParityCounts','CubeLocal','First112Reuse']:
        check(name)
    with LOCK:state['active'].pop('setup',None);publish()
    survey=read(OUT/'survey.json')['entries'];cores=read(OUT/'bank-cores.json')['entries']
    def cost(i):return cores[str(survey[str(i)].get('reused_from',i))]['derived_steps']
    reps=args.representatives if args.representatives is not None else cover['representatives']
    reps=sorted(reps,key=lambda i:(i not in (0,184),cost(i)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        for _ in pool.map(build_group,reps):pass
    if len(state['entries'])==262 and not state['failures']:
        name=aggregate();check(name,'aggregate',True)
        for theorem in ['bank_no192','bank_no_long_prefix','bank_no_long_suffix','bank_end_segment_length_le191']:
            audit(name,'Snake9.Regrowth.Bank112.'+theorem)
        state.update(status='PASSED',active={},completed_utc=now(),aggregate=name)
        event('bank112','全部262个112档入口及汇总定理通过 Lean。')
    else:
        state['status']='NEEDS_REPAIR' if state['failures'] else 'IN_PROGRESS'
    with LOCK:publish()
    save('bank-runner.json',dict(pid=os.getpid(),status=state['status'],finished_utc=now()))
    guard.close()

if __name__=='__main__':
    try:main()
    except Exception:
        save('bank-runner.json',dict(pid=os.getpid(),status='FAILED',error=traceback.format_exc(),finished_utc=now()))
        raise
