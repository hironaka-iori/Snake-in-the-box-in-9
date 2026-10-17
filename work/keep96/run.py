"""Bounded resumable pilot/survey. No KEEP=112 workers or files are touched."""
import argparse
import csv
import platform
import subprocess
import time
from datetime import datetime,timezone
from common import *
import pysat
import psutil
import pysolvers


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--phase',choices=['pilot','survey'],default='pilot')
    ap.add_argument('--seconds',type=float,default=300);ap.add_argument('--memory-mib',type=int,default=2048)
    ap.add_argument('--entries',type=int,nargs='+');ap.add_argument('--retry-unknown',action='store_true')
    a=ap.parse_args()
    if a.seconds<=0 or a.memory_mib<128:ap.error('positive time and memory >=128 MiB required')
    positives=json.loads((OUT/'positive-controls.json').read_text())
    if positives['status']!='PASSED' or len(positives['entries'])!=262:raise ValueError('positive controls required')
    for key,path in [('encoder_sha256',ROOT/'work/build_regrowth_cnf.py'),('bank_sha256',ROOT/'work/bank9.json')]:
        if positives['provenance'][key]!=sha(path):raise ValueError('positive controls stale')
    entries=a.entries or (json.loads((OUT/'pilot-selection.json').read_text())['entries'] if a.phase=='pilot' else list(range(262)))
    if len(set(entries))!=len(entries) or any(not 0<=j<262 for j in entries):raise ValueError('invalid entries')
    config=dict(keep=96,total_vertices=193,worker_wall_limit_seconds=a.seconds,memory_limit_mib=a.memory_mib,
                solver='Glucose 4.1 (PySAT g4)',python_sat=pysat.__version__,proof_logging=True,
                solver_parameters='defaults; no custom seed or incremental mode',python=sys.version,
                platform=platform.platform(),pysolvers_sha256=sha(pysolvers.__file__),
                encoder_sha256=sha(ROOT/'work/build_regrowth_cnf.py'),bank_sha256=sha(ROOT/'work/bank9.json'),
                sources={p.name:sha(p) for p in (HERE/'common.py',HERE/'worker.py',Path(__file__))})
    results=[]
    table=OUT/f'{a.phase}-results.json'
    def summary():
        save(table,dict(config=config,entries=results,planned_entries=entries,
                        complete=len(results)==len(entries),interpretation='Computational relaxation results, not Lean proofs'))
        with table.with_suffix('.csv').open('w',newline='',encoding='utf-8') as f:
            fields=['entry','status','termination','runtime_seconds','peak_rss_bytes','attempt','certificate','formula_sha256']
            writer=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore');writer.writeheader();writer.writerows(results)
    summary()
    for entry in entries:
        data,hashes=formula(entry)
        identity=dict(config=config,formula_hashes=hashes)
        key=hashlib.sha256(json.dumps(identity,sort_keys=True).encode()).hexdigest()
        entry_dir=OUT/'runs'/f'entry{entry:03d}'/key[:16]
        existing=sorted(entry_dir.glob('*/result.json')) if entry_dir.exists() else []
        reused=None
        for p in reversed(existing):
            r=json.loads(p.read_text())
            if r['identity']!=identity:continue
            if any(not (ROOT/f).exists() or sha(ROOT/f)!=h for f,h in r['artifact_hashes'].items()):continue
            if r['status'] in ('SAT','UNSAT') or (r['status']=='UNKNOWN' and not a.retry_unknown):
                reused=r;break
        if reused:
            results.append(reused);summary();print(entry,'reused',reused['status'],flush=True);continue
        attempt=entry_dir/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
        attempt.mkdir(parents=True,exist_ok=False)
        save(attempt/'started.json',dict(entry=entry,identity=identity,state='RUNNING_OR_INTERRUPTED',phase=a.phase))
        command=[sys.executable,str(HERE/'worker.py'),'--entry',str(entry),'--memory-mib',str(a.memory_mib),'--attempt',str(attempt)]
        start=time.perf_counter();peak=0;termination='PROCESS_EXIT'
        print('start',entry,'variables',data['variables'],'clauses',len(data['clauses']),flush=True)
        with (attempt/'solver.log').open('w',encoding='utf-8') as log:
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,cwd=ROOT)
            monitored=psutil.Process(process.pid)
            try:
                while process.poll() is None:
                    try:peak=max(peak,monitored.memory_info().rss)
                    except psutil.NoSuchProcess:pass
                    if time.perf_counter()-start>=a.seconds:
                        termination='TIMEOUT';process.kill();break
                    if peak>a.memory_mib*1024**2:
                        termination='MEMORY_LIMIT';process.kill();break
                    time.sleep(.1)
                rc=process.wait()
            except BaseException:
                process.kill();process.wait();raise
        duration=time.perf_counter()-start
        worker=attempt/'worker-result.json'
        r=json.loads(worker.read_text()) if rc==0 and worker.exists() and termination=='PROCESS_EXIT' else dict(status='UNKNOWN')
        if rc!=0 and termination=='PROCESS_EXIT':termination='WORKER_ERROR_OR_MEMORY_LIMIT'
        r.update(entry=entry,bank_index=entry//2,reversed=bool(entry%2),identity=identity,
                 termination=termination,exit_code=rc,runtime_seconds=duration,peak_rss_bytes=peak,
                 attempt=attempt.relative_to(ROOT).as_posix(),command=command,
                 formula_sha256=next(v for k,v in hashes.items() if k.endswith('.cnf.gz')),
                 variables=data['variables'],clauses=len(data['clauses']),region_vertices=len(data['vertices']))
        if r.get('certificate'):r['certificate']=(attempt/r['certificate']).relative_to(ROOT).as_posix()
        r['artifact_hashes']={**hashes,**{p.relative_to(ROOT).as_posix():sha(p) for p in attempt.iterdir() if p.is_file()}}
        save(attempt/'result.json',r);results.append(r);summary()
        print(entry,r['status'],round(duration,2),termination,flush=True)


if __name__=='__main__':main()
