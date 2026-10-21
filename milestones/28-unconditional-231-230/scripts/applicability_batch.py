"""Resumable, frozen-source applicability checks for the 34 parallel-share cores.

Waits for immutable cores from the independent Boolean worker. This job proves
geometric satisfying assignments; it does not replace the Boolean refutations.
"""
import argparse
import http.server
import json
import os
from pathlib import Path
import subprocess
import time
import traceback
import runner as common
import generate_parallel_cases as generator
from develop_lean import SEARCH

HERE=common.HERE
ROOT=common.ROOT
JOB=HERE/'runtime/applicability'
SRC=JOB/'src'
KERNEL=HERE/'runtime/kernel'
CONTROLLERS=['applicability_batch.py','generate_parallel_cases.py','generate_parallel_pilot.py',
    'generate_gate_pilot.py','runner.py','replay.py','develop_lean.py']

def prepare():
    if (JOB/'manifest.json').exists():raise RuntimeError('Existing batch: use run')
    original=common.read(HERE/'runtime/manifest.json');common.validate(original)
    commit=common.git('rev-parse','HEAD').decode().strip()
    files=set(common.git('ls-tree','-r','--name-only',commit).decode().splitlines())
    frozen={}
    def freeze(name):
        if name.startswith(('Std','Init','Lean','Mathlib')) or name in frozen:return
        rel=name.replace('.','/')+'.lean';path=next((p+'/'+rel for p in SEARCH if p+'/'+rel in files),None)
        assert path,('missing source',name)
        data=common.blob(commit,path)
        for line in data.decode().splitlines():
            if line.startswith('import '):
                for dep in line.split('--')[0].split()[1:]:freeze(dep)
        dest=SRC/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        frozen[name]=dict(source_path=path,source_sha256=common.digest(dest))
    freeze('ParallelShareCertificateBatch')
    controls={str(HERE/'scripts'/f):common.digest(HERE/'scripts'/f) for f in CONTROLLERS}
    gp=ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py';controls[str(gp)]=common.digest(gp)
    for path,h in controls.items():
        relative=Path(path).relative_to(ROOT).as_posix()
        assert common.hashbytes(common.blob(commit,relative))==common.hashbytes(Path(path).read_text(encoding='utf-8').replace('\r\n','\n').encode()),('uncommitted controller',path)
    config=original['config'].copy();config.update(source_commit=commit,timeout_seconds=1800)
    manifest=dict(created=common.now(),config=config,controllers=controls,frozen_modules=frozen,
        original_manifest_sha256=common.digest(HERE/'runtime/manifest.json'),
        kernel_manifest_sha256=common.digest(KERNEL/'manifest.json'),chunk_clauses=128,
        scope='Geometric applicability of 34 exact Boolean cores; global 231/230 remain unresolved')
    common.atomic(JOB/'manifest.json',manifest)
    common.atomic(JOB/'state.json',dict(status='prepared',completed={},cases={},failures=[],source_commit=commit,
        applicability_cases=0,total_cases=34,global_231='UNRESOLVED',global_230='UNRESOLVED'))
    print(json.dumps({'source_commit':commit,'modules':len(frozen),'manifest':str(JOB/'manifest.json')}))

def validate(m):
    for p,h in m['controllers'].items():assert common.digest(p)==h,('changed controller',p)
    assert common.digest(HERE/'runtime/manifest.json')==m['original_manifest_sha256']
    assert common.digest(KERNEL/'manifest.json')==m['kernel_manifest_sha256']
    for name,d in m['frozen_modules'].items():assert common.digest(SRC/(name.replace('.','/')+'.lean'))==d['source_sha256']
    common.validate(common.read(HERE/'runtime/manifest.json'))

def lock():
    import msvcrt
    f=open(JOB/'worker.lock','a+b');f.seek(0);f.write(b'0');f.flush();f.seek(0)
    msvcrt.locking(f.fileno(),msvcrt.LK_NBLCK,1);return f

def environment(config):
    env=common.process_context(config)
    base=str(HERE/'build/frozen/src')
    external=[p for p in env['LEAN_PATH'].split(os.pathsep) if p and os.path.normcase(p)!=os.path.normcase(base)]
    env['LEAN_PATH']=os.pathsep.join([str(SRC),*external]);return env

def execute(command,log,config,state):
    start=time.monotonic();peak=0;log.parent.mkdir(parents=True,exist_ok=True)
    with log.open('w',encoding='utf-8') as output:
        output.write(json.dumps(command)+'\n');output.flush()
        child=subprocess.Popen(command,stdout=output,stderr=subprocess.STDOUT,cwd=SRC,env=environment(config))
        try:
            while child.poll() is None:
                try:
                    p=common.psutil.Process(child.pid);rss=sum(p.memory_info().rss for p in [p,*p.children(recursive=True)] if p.is_running())
                except common.psutil.NoSuchProcess:rss=0
                peak=max(peak,rss)
                common.atomic(JOB/'live.json',dict(pid=os.getpid(),child_pid=child.pid,current_item=state['current_item'],
                    heartbeat=common.now(),resources=dict(rss_mb=round(rss/2**20,1),peak_rss_mb=round(peak/2**20,1),
                    available_mb=round(common.psutil.virtual_memory().available/2**20,1),memory_policy='observe_only')))
                if time.monotonic()-start>config['timeout_seconds']:raise RuntimeError('Module timeout: unresolved')
                time.sleep(1)
            if child.returncode:raise RuntimeError(f'Lean exit {child.returncode}: {log}')
        except BaseException:
            common.kill_tree(child);child.wait();raise
    return dict(elapsed_seconds=time.monotonic()-start,peak_rss_mb=round(peak/2**20,1),command=command)

def build(name,m,state,checked):
    if name.startswith(('Std','Init','Lean','Mathlib')):return None
    if name in checked:return checked[name]
    source=SRC/(name.replace('.','/')+'.lean');assert source.exists(),('missing source',name)
    data=source.read_bytes();sha=common.hashbytes(data);deps={}
    for line in data.decode().splitlines():
        if line.startswith('import '):
            for dep in line.split('--')[0].split()[1:]:
                h=build(dep,m,state,checked)
                if h:deps[dep]=h
    config=m['config'];fingerprint=common.hashbytes(json.dumps([sha,deps,config['lean_version'],config['tools'],config['mathlib_commit']],sort_keys=True).encode())
    old=state['completed'].get(name);out=source.with_suffix('.olean')
    if old and old['closure_hash']==fingerprint and out.exists() and common.digest(out)==old['artifact_sha256']:
        checked[name]=fingerprint
        return fingerprint
    log=JOB/'logs'/(name.replace('.','_')+'.log')
    state.update(status='running',phase='Lean geometric applicability',current_item=name,latest_log=str(log),last_progress=common.now())
    common.atomic(JOB/'state.json',state)
    result=execute([str(Path(config['lean_bin'])/'lean.exe'),'--root='+str(SRC),'-o',str(out),str(source)],log,config,state)
    result.update(source_sha256=sha,dependency_hashes=deps,closure_hash=fingerprint,artifact_sha256=common.digest(out),
        log_sha256=common.digest(log),axiom_audits=common.audit_axioms(log.read_text(encoding='utf-8')),completed=common.now())
    state['completed'][name]=result;state['last_progress']=common.now();common.atomic(JOB/'state.json',state)
    checked[name]=fingerprint
    print(name,'PASS',round(result['elapsed_seconds'],2),flush=True);return fingerprint

def run():
    held=lock();m=common.read(JOB/'manifest.json');validate(m);state=common.read(JOB/'state.json')
    state.update(status='running',pid=os.getpid(),started=common.now());state.pop('failure',None)
    try:
        for index in [1,0,*range(2,34)]:
            while not (KERNEL/'cases'/f'{index:02d}'/'ready.json').exists():
                state.update(status='waiting_for_core',current_item=f'Boolean core {index:02d}',heartbeat=common.now())
                common.atomic(JOB/'state.json',state)
                common.atomic(JOB/'live.json',dict(pid=os.getpid(),child_pid=None,current_item=state['current_item'],heartbeat=common.now()))
                time.sleep(30)
            ready=JOB/'cases'/f'{index:02d}.json'
            if ready.exists():
                d=common.read(ready)
                for p,h in d['generated_files'].items():assert common.digest(SRC/p)==h,('changed generated source',p)
            else:
                state.update(status='running',phase='Generate exact geometric trace',current_item=f'case {index:02d}')
                common.atomic(JOB/'state.json',state)
                d=generator.generate(index,SRC,m['chunk_clauses']);common.atomic(ready,d)
            # Revalidate the complete dependency closure once for each case.
            target=d['target'];fingerprint=build(target,m,state,{})
            audits=state['completed'][target]['axiom_audits'];assert audits,('missing target audit',target)
            state['cases'][str(index)]=dict(target=target,closure_hash=fingerprint,axiom_audits=audits,
                completed=common.now(),clauses=d['clauses'],chunks=d['chunks'],generation_receipt_sha256=common.digest(ready))
            state.update(applicability_cases=len(state['cases']),last_progress=common.now())
            common.atomic(JOB/'state.json',state)
        validate(m);state.update(status='applicability_complete',current_item=None,finished=common.now())
    except BaseException as ex:
        state.update(status='action_required',failure=str(ex))
        state['failures'].append(dict(time=common.now(),item=state.get('current_item'),error=str(ex)))
        traceback.print_exc()
    finally:
        common.atomic(JOB/'state.json',state);held.close()
    print(json.dumps({'status':state['status'],'applicability_cases':state.get('applicability_cases'),'failure':state.get('failure')}))

PAGE='''<!doctype html><meta charset="utf-8"><title>Q9 verification</title>
<style>body{font:16px system-ui;max-width:1000px;margin:40px auto;padding:0 24px;background:#f5f5f2;color:#212522}table{width:100%;background:white;border-collapse:collapse}th,td{padding:12px;text-align:left;border-bottom:1px solid #ddd}pre{white-space:pre-wrap;overflow-wrap:anywhere}</style>
<h1>Q9 · 231 验证</h1><p>全局 231 / 230 尚未完成。两个批次分别显示。</p><div id="app"></div>
<script>const esc=x=>String(x??'—').replaceAll('&','&amp;').replaceAll('<','&lt;');async function refresh(){let s=await(await fetch('/state')).json();let a=s.applicability,k=s.kernel,l=s.live;let rows=[['Boolean 内核反证',(k.kernel_cases??0)+' / 34'],['Boolean 当前项',k.current_item],['几何适用性',(a.applicability_cases??0)+' / 34'],['几何状态',a.status],['几何当前项',a.current_item],['检查点',s.checkpoint],['最新完成',a.last_progress],['资源',JSON.stringify(l.resources)],['全局上界','未解决']];document.getElementById('app').innerHTML='<table>'+rows.map(([x,y])=>'<tr><th>'+esc(x)+'</th><td>'+esc(y)+'</td></tr>').join('')+'</table><h2>失败记录</h2><pre>'+esc(JSON.stringify({boolean:k.failures,applicability:a.failures},null,2))+'</pre><h2>最新日志</h2><pre>'+esc(await(await fetch('/log')).text())+'</pre>';}refresh();setInterval(refresh,5000);</script>'''

def serve(port):
    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path=='/state':
                data=json.dumps(dict(applicability=common.read(JOB/'state.json'),kernel=common.read(KERNEL/'state.json'),
                    live=common.read(JOB/'live.json') if (JOB/'live.json').exists() else {},checkpoint=str(JOB/'state.json'))).encode();kind='application/json'
            elif self.path=='/log':
                p=common.read(JOB/'state.json').get('latest_log');data=('\n'.join(Path(p).read_text(errors='replace').splitlines()[-25:]) if p and Path(p).exists() else '').encode();kind='text/plain'
            else:data=PAGE.encode();kind='text/html'
            self.send_response(200);self.send_header('Content-Type',kind+'; charset=utf-8');self.end_headers();self.wfile.write(data)
        def log_message(self,*args):pass
    http.server.ThreadingHTTPServer(('127.0.0.1',port),Handler).serve_forever()

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['prepare','run','serve']);ap.add_argument('--port',type=int,default=8797);a=ap.parse_args()
    if a.mode=='prepare':prepare()
    elif a.mode=='run':run()
    else:serve(a.port)
