"""Frozen-source single-worker verification with content-validated checkpoints.

prepare writes local paths only to ignored runtime/. run resumes only matching
sources, dependencies, tools, and output hashes. serve exposes a read-only local
dashboard. No mathematical research or global theorem completion is automated.
"""
import argparse
import datetime as dt
import hashlib
import http.server
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import traceback
if not __debug__:
    raise RuntimeError('Verification must run without Python -O')

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
RUNTIME=HERE/'runtime'; BUILD=HERE/'build/frozen'
sys.path.insert(0,str(RUNTIME/'packages'))
import psutil
from replay import check, digest
PIN='c44e0c8ee63ca166450922a373c7409c5d26b00b'
ALLOWED={'propext','Classical.choice','Quot.sound'}
UP='milestones/28-unconditional-231-230/upstream/milestones/10-window-aggregate/'

def now(): return dt.datetime.now(dt.timezone.utc).isoformat()
def atomic(p,d):
    p=Path(p); p.parent.mkdir(parents=True,exist_ok=True)
    tmp=p.with_name(p.name+f'.{os.getpid()}.tmp')
    tmp.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    os.replace(tmp,p)
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def blob(commit,p):return git('show',commit+':'+p)
def hashbytes(b):return hashlib.sha256(b).hexdigest()
def process_context(config):
    env=os.environ.copy()
    env.pop('LEAN_PATH',None)
    env['PATH']=config['lean_bin']+os.pathsep+env.get('PATH','')
    mathlib=Path(config['mathlib'])
    libs=[str(BUILD/'src'),str(mathlib/'.lake/build/lib/lean')]
    libs += [str(p) for p in sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))]
    env['LEAN_PATH']=os.pathsep.join(libs)
    env['PYTHONPATH']=str(RUNTIME/'packages')
    return env

def prepare(a):
    RUNTIME.mkdir(parents=True,exist_ok=True)
    if (RUNTIME/'manifest.json').exists(): raise RuntimeError('Manifest exists: use run to resume')
    commit=git('rev-parse','HEAD').decode().strip()
    tracked=set(git('ls-tree','-r','--name-only',commit).decode().splitlines())
    roots=['work/final_lean/','work/spectral/stronger/','work/spectral/',
           'milestones/27-empty-square-packing/lean/']
    mods={}; order=[]
    def visit(m):
        if m in mods:return
        rel=next((r+m.replace('.','/')+'.lean' for r in roots if r+m.replace('.','/')+'.lean' in tracked),None)
        if rel is None:
            if not m.startswith(('Mathlib','Std','Lean','Init')):raise RuntimeError('Missing custom module: '+m)
            return
        data=blob(commit,rel); text=data.decode('utf-8')
        # Comments can mention these tokens; the compiler axiom audit is authoritative.
        imports=[]
        for l in text.splitlines():
            if l.startswith('import '): imports.extend(l.split('--')[0].split()[1:])
        mods[m]=dict(module=m,path=rel,sha256=hashbytes(data),imports=imports)
        for d in imports:visit(d)
        dest=BUILD/'src'/(m.replace('.','/')+'.lean')
        dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
        order.append(m)
    targets=['ParallelShareTerm','UpperTargetArithmetic','EmptyShareBound','SharePacking']
    for m in targets:visit(m)
    # Freeze exact encoder and shape records with the same source commit.
    for rel in sorted(p for p in tracked if p.startswith(UP)):
        out=BUILD/'upstream'/rel[len(UP):]
        out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(blob(commit,rel))
    lean_bin=Path(a.lean_bin).resolve(); mathlib=Path(a.mathlib).resolve()
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()
    assert actual==PIN, actual
    subprocess.run(['git','diff','--exit-code','HEAD','--','*.lean','lean-toolchain','lake-manifest.json'],cwd=mathlib,check=True,capture_output=True)
    ver=subprocess.check_output([str(lean_bin/'lean.exe'),'--version'],text=True).strip()
    assert '4.19.0' in ver
    toolhashes={str(p):digest(p) for p in [lean_bin/'lean.exe',lean_bin/'cadical.exe',*lean_bin.glob('*.dll')]}
    mdata=read(mathlib/'lake-manifest.json')
    for p in mdata['packages']:
        checkout=mathlib/'.lake/packages'/p['name']
        rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=checkout,text=True).strip()
        assert rev==p['rev'], (p['name'],rev,p['rev'])
        subprocess.run(['git','diff','--exit-code','HEAD','--','*.lean'],cwd=checkout,check=True,capture_output=True)
    config=dict(source_commit=commit,lean_bin=str(lean_bin),mathlib=str(mathlib),lean_version=ver,
        mathlib_commit=PIN,mathlib_manifest_sha256=digest(mathlib/'lake-manifest.json'),tools=toolhashes,
        memory_mb=a.memory_mb or max(256,min(2048,int(psutil.virtual_memory().available/2**20*.6))),
        timeout_seconds=a.timeout,python=sys.executable,python_version=sys.version,
        solver_version=subprocess.check_output([str(lean_bin/'cadical.exe'),'--version'],text=True).strip(),
        worker_sha256=digest(__file__),replay_sha256=digest(HERE/'scripts/replay.py'))
    fingerprint=hashbytes(json.dumps(config,sort_keys=True).encode())
    for m in order:
        mods[m]['dependency_hashes']={d:mods[d]['closure_hash'] for d in mods[m]['imports'] if d in mods}
        mods[m]['closure_hash']=hashbytes(json.dumps([mods[m]['sha256'],mods[m]['dependency_hashes'],fingerprint],sort_keys=True).encode())
    cases=[json.loads(l) for l in (BUILD/'upstream/data/share/final_a_X20.jsonl').read_text().splitlines() if l]
    frozen_files={str(p.relative_to(BUILD)):digest(p) for p in (BUILD/'upstream').rglob('*') if p.is_file()}
    manifest=dict(created=now(),config=config,modules=mods,order=order,targets=targets,cases=cases,
        frozen_files=frozen_files,config_fingerprint=fingerprint,
        scope='Partial source rebuild and 34 independent local CNF/RUP replays; not unconditional 231')
    atomic(RUNTIME/'manifest.json',manifest)
    atomic(RUNTIME/'state.json',dict(status='prepared',completed={},failures=[],last_progress=now()))
    print(json.dumps(dict(commit=commit,modules=len(order),cases=len(cases),memory_mb=config['memory_mb']),indent=2))

def current(phase):atomic(RUNTIME/'item-progress.json',dict(phase=phase,time=now()))

def item(a):
    manifest=read(RUNTIME/'manifest.json'); config=manifest['config']
    rec=manifest['cases'][a.index]; run=BUILD/'cases'/f'{a.index:02d}'
    run.mkdir(parents=True,exist_ok=True)
    sys.path.insert(0,str(BUILD/'upstream/scripts'))
    from share_enc import ShareEncoding, window_from_dirs
    cuts=read(BUILD/'upstream/data/share/final_a_X20.jsonl.cuts.json')
    current('CNF generation and hash check')
    enc=ShareEncoding(window_from_dirs(rec['dirs']),[(0,21)]*6,3,20,counter='stot',exact=True)
    for cut in cuts[','.join(map(str,rec['dirs']))]:enc.add_cycle_cut(cut)
    cnf=run/'model.cnf'; proof=run/'proof.lrat'
    with open(cnf,'w',encoding='ascii',newline='\n') as f:
        f.write(f'p cnf {enc.nv} {len(enc.clauses)}\n')
        for c in enc.clauses:f.write(' '.join(map(str,c))+' 0\n')
    assert digest(cnf)==rec['cnf_sha256'], ('model hash mismatch',a.index,digest(cnf),rec['cnf_sha256'])
    assert enc.nv==rec['variables'] and len(enc.clauses)==rec['clauses']
    clause_kinds=dict(__import__('collections').Counter(enc.kinds))
    del enc
    current('Proof-producing solver (not a theorem)')
    command=[str(Path(config['lean_bin'])/'cadical.exe'),'--elim=false','--lrat','--no-binary','--seed=1','-q',str(cnf),str(proof)]
    started=time.monotonic()
    receipt=read(run/'solved.json') if (run/'solved.json').exists() else None
    reusable=receipt and receipt.get('command')==command and receipt.get('cnf_sha256')==digest(cnf) and proof.exists() and receipt.get('proof_sha256')==digest(proof) and receipt.get('solver_sha256')==digest(command[0])
    if not reusable:
        with open(run/'solver.log','w',encoding='utf-8') as log:
            result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
        assert result.returncode==20, ('solver unresolved/non-UNSAT',result.returncode)
        receipt=dict(command=command,cnf_sha256=digest(cnf),proof_sha256=digest(proof),
                     solver_sha256=digest(command[0]),elapsed_seconds=time.monotonic()-started,
                     status='solver_UNSAT_not_replayed',time=now())
        atomic(run/'solved.json',receipt)
    solved=time.monotonic()
    current('Independent RUP replay (not Lean)')
    replay=check(cnf,proof)
    replay.update(index=a.index,dirs=rec['dirs'],cap=20,source_record=rec,seed=1,threads=1,
        solver_version=config['solver_version'],command=command,solver_seconds=receipt['elapsed_seconds'],
        replay_seconds=time.monotonic()-solved,clause_families=clause_kinds,
        model_code_sha256={n:digest(BUILD/'upstream/scripts'/n) for n in ['share_enc.py','wincert.py']},
        limit_seconds=config['timeout_seconds'],memory_budget_mb=config['memory_mb'])
    atomic(run/'result.json',replay)
    print(json.dumps(replay))

def lock():
    p=RUNTIME/'runner.lock'; f=open(p,'a+b');f.seek(0);f.write(b'0');f.flush();f.seek(0)
    if os.name=='nt':
        import msvcrt
        msvcrt.locking(f.fileno(),msvcrt.LK_NBLCK,1)
    else:
        import fcntl
        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
    return f

def kill_tree(p):
    try:
        proc=psutil.Process(p.pid)
        for c in proc.children(recursive=True):
            try:c.kill()
            except psutil.NoSuchProcess:pass
        proc.kill()
    except psutil.NoSuchProcess:pass

def supervise(command,log,config,state):
    start=time.monotonic();peak=0
    with open(log,'w',encoding='utf-8') as f:
        f.write('COMMAND '+json.dumps(command)+'\n');f.flush()
        p=subprocess.Popen(command,stdout=f,stderr=subprocess.STDOUT,env=process_context(config),cwd=ROOT)
        state['child_pid']=p.pid;state['current_started']=now()
        try:
            while p.poll() is None:
                try:
                    proc=psutil.Process(p.pid); tree=[proc]+proc.children(recursive=True)
                    rss=sum(x.memory_info().rss for x in tree if x.is_running());peak=max(peak,rss)
                except psutil.NoSuchProcess:rss=0
                mem=psutil.virtual_memory()
                state['resources']=dict(rss_mb=round(rss/2**20,1),peak_rss_mb=round(peak/2**20,1),
                    available_mb=round(mem.available/2**20,1),budget_mb=config['memory_mb'],cpu_percent=psutil.cpu_percent())
                state['heartbeat']=now()
                state['solver_receipts']=len(list((BUILD/'cases').glob('*/solved.json')))
                state['phase_detail']=read(RUNTIME/'item-progress.json') if (RUNTIME/'item-progress.json').exists() else None
                atomic(RUNTIME/'state.json',state)
                if rss>config['memory_mb']*2**20:raise RuntimeError('Resource budget exceeded; split or refactor before resuming')
                if mem.available<128*2**20:raise RuntimeError('System available memory below 128 MiB')
                if time.monotonic()-start>config['timeout_seconds']:raise RuntimeError('Item timeout: unresolved, not UNSAT')
                time.sleep(1)
            if p.returncode:raise RuntimeError(f'Command exit {p.returncode}; see {log}')
        except BaseException:
            kill_tree(p);p.wait();raise
    return dict(elapsed_seconds=time.monotonic()-start,peak_rss_mb=round(peak/2**20,1),command=command)

def audit_axioms(text):
    if re.search(r'sorryAx|Lean\.ofReduceBool|declaration uses .sorry',text):raise RuntimeError('Forbidden axiom/placeholder')
    found=[]
    for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
        axioms={x.strip() for x in raw.split(',') if x.strip()}
        assert axioms<=ALLOWED,(name,axioms)
        found.append(dict(theorem=name,axioms=sorted(axioms)))
    for name in re.findall(r"'([^']+)' does not depend on any axioms",text):found.append(dict(theorem=name,axioms=[]))
    return found

def validate(manifest):
    c=manifest['config']
    assert hashbytes(json.dumps(c,sort_keys=True).encode())==manifest['config_fingerprint']
    assert digest(__file__)==c['worker_sha256'] and digest(HERE/'scripts/replay.py')==c['replay_sha256']
    for p,h in c['tools'].items():assert digest(p)==h,('changed tool',p)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=c['mathlib'],text=True).strip()==PIN
    assert digest(Path(c['mathlib'])/'lake-manifest.json')==c['mathlib_manifest_sha256']
    subprocess.run(['git','diff','--exit-code','HEAD','--','*.lean','lean-toolchain','lake-manifest.json'],cwd=c['mathlib'],check=True,capture_output=True)
    for p,h in manifest['frozen_files'].items():assert digest(BUILD/p)==h,('changed input',p)
    for m,d in manifest['modules'].items():assert digest(BUILD/'src'/(m.replace('.','/')+'.lean'))==d['sha256']

def run(a):
    held=lock();manifest=read(RUNTIME/'manifest.json');validate(manifest);c=manifest['config']
    state=read(RUNTIME/'state.json');state.update(status='running',pid=os.getpid(),started=now(),
        target='231: six-centre local prerequisites',global_231='UNRESOLVED',global_230='UNRESOLVED',
        semantic_obligations=['Full parallel-share CNF assignment and counter semantics',
            '34 Lean-checked share refutations with arbitrary-snake normalization',
            '15,959 count-window Lean refutations and full bridge',
            'Final unconditional theorem and fresh custom closure rebuild'],
        totals=dict(lean_modules=len(manifest['order']),solver_cases=34,independent_replays=34),
        manifest=str(RUNTIME/'manifest.json'),checkpoint=str(RUNTIME/'state.json'))
    try:
        state['requested_phase']=a.phase
        for m in (manifest['order'] if a.phase != 'certificates' else []):
            key='lean:'+m;d=manifest['modules'][m];src=BUILD/'src'/(m.replace('.','/')+'.lean');out=src.with_suffix('.olean')
            cached=state['completed'].get(key)
            if cached and cached.get('closure_hash')==d['closure_hash'] and out.exists() and digest(out)==cached.get('artifact_sha256'):
                continue
            log=RUNTIME/'logs'/(m.replace('.','_')+'.log');log.parent.mkdir(parents=True,exist_ok=True)
            state.update(phase='Kernel source rebuild of partial components',current_item=m,latest_log=str(log))
            current('Lean source compilation; not an unconditional target')
            result=supervise([str(Path(c['lean_bin'])/'lean.exe'),'--root='+str(BUILD/'src'),'-o',str(out),str(src)],log,c,state)
            audits=audit_axioms(log.read_text(encoding='utf-8'))
            result.update(source_sha256=d['sha256'],dependency_hashes=d['dependency_hashes'],closure_hash=d['closure_hash'],
                artifact_sha256=digest(out),axiom_audits=audits,completed=now())
            state['completed'][key]=result;state['last_progress']=now();atomic(RUNTIME/'state.json',state)
        # Deliberately replays only the already-finished share batch, not the active seven-centre count batch.
        for i,rec in (enumerate(manifest['cases']) if a.phase != 'lean' else []):
            key=f'share:{i:02d}';path=BUILD/'cases'/f'{i:02d}';cached=state['completed'].get(key)
            if cached and (path/'result.json').exists() and digest(path/'result.json')==cached.get('result_sha256') and all(
                (path/f).exists() and digest(path/f)==cached.get(f+'_sha256') for f in ['model.cnf','proof.lrat']):continue
            log=RUNTIME/'logs'/f'share-{i:02d}.log'
            state.update(phase='Local solver and independent certificate replay',current_item=f'{i+1}/34 {rec["dirs"]}',latest_log=str(log))
            result=supervise([sys.executable,str(Path(__file__).resolve()),'item','--index',str(i)],log,c,state)
            result.update(result_sha256=digest(path/'result.json'),completed=now())
            for f in ['model.cnf','proof.lrat']:result[f+'_sha256']=digest(path/f)
            state['completed'][key]=result;state['last_progress']=now();atomic(RUNTIME/'state.json',state)
        validate(manifest)
        state.update(status='partial_batch_complete',phase='Mathematical integration still required',current_item=None,child_pid=None,
                     last_progress=now(),completion_scope=manifest['scope'],completed_phase=a.phase)
    except BaseException as ex:
        state.update(status='action_required',failure=str(ex),child_pid=None)
        state['failures'].append(dict(time=now(),item=state.get('current_item'),error=str(ex)))
        traceback.print_exc()
    finally:
        atomic(RUNTIME/'state.json',state);held.close()
    print(json.dumps(dict(status=state['status'],completed=len(state['completed']),failure=state.get('failure'))))

PAGE='''<!doctype html><meta charset="utf-8"><title>Q9 · 231 verification</title>
<style>body{font:16px system-ui;background:#f5f5f2;color:#212522;max-width:1050px;margin:40px auto;padding:0 24px}h1{font-size:26px}table{border-collapse:collapse;width:100%;background:white}td,th{text-align:left;padding:12px;border-bottom:1px solid #ddd}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#eaeae6;padding:18px}small{color:#555}</style>
<h1>Q9 · 231 验证工作台</h1><p>231 / 230 无条件定理仍未完成。各阶段单独统计。</p><div id="app"></div>
<script>const esc=x=>String(x??'—').replaceAll('&','&amp;').replaceAll('<','&lt;');async function refresh(){let s=await(await fetch('/state')).json();let c=s.completed||{};let n=Object.keys(c).filter(x=>x.startsWith('lean:')).length;let k=Object.keys(c).filter(x=>x.startsWith('share:')).length;let rows=[['状态',s.status],['阶段',s.phase],['当前项目',s.current_item],['最后完成进度',s.last_progress],['源码模块',n+' / '+(s.totals?.lean_modules??'?')],['求解器 UNSAT 收据',(s.solver_receipts??0)+' / 34'],['独立证书重放',k+' / 34'],['Lean 局部 share 反证','0 / 34'],['任意蛇的语义桥接','未完成'],['最终全局验证','未开始'],['资源',JSON.stringify(s.resources)],['检查点',s.checkpoint],['最新日志',s.latest_log]];document.getElementById('app').innerHTML='<table>'+rows.map(([a,b])=>'<tr><th>'+esc(a)+'</th><td>'+esc(b)+'</td></tr>').join('')+'</table><h2>未解决义务</h2><pre>'+esc((s.semantic_obligations||[]).join('\\n'))+'</pre><h2>失败记录</h2><pre>'+esc(JSON.stringify(s.failures||[],null,2))+'</pre><h2>日志末尾</h2><pre>'+esc(await(await fetch('/log')).text())+'</pre><small>不根据异质模块的完成数量预测剩余时间。</small>';}refresh();setInterval(refresh,5000);</script>'''

def serve(a):
    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path=='/':data=PAGE.encode();kind='text/html; charset=utf-8'
            elif self.path=='/state':data=(RUNTIME/'state.json').read_bytes();kind='application/json'
            elif self.path=='/log':
                p=Path(read(RUNTIME/'state.json').get('latest_log',''))
                data=p.read_bytes()[-12000:] if p.is_file() else b'';kind='text/plain; charset=utf-8'
            else:self.send_error(404);return
            self.send_response(200);self.send_header('Content-Type',kind);self.send_header('Cache-Control','no-store');self.end_headers();self.wfile.write(data)
        def log_message(self,*args):pass
    http.server.ThreadingHTTPServer(('127.0.0.1',a.port),Handler).serve_forever()

if __name__=='__main__':
    ap=argparse.ArgumentParser();sub=ap.add_subparsers(dest='action',required=True)
    p=sub.add_parser('prepare');p.add_argument('--lean-bin',required=True);p.add_argument('--mathlib',required=True)
    p.add_argument('--memory-mb',type=int,default=0);p.add_argument('--timeout',type=int,default=900)
    p=sub.add_parser('run');p.add_argument('--phase',choices=['all','lean','certificates'],default='all')
    p=sub.add_parser('item');p.add_argument('--index',type=int,required=True)
    p=sub.add_parser('serve');p.add_argument('--port',type=int,default=8796)
    a=ap.parse_args();globals()[a.action](a)
