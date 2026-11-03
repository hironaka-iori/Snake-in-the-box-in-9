"""Run the complete012032 replay alone and preserve the existing012301 job.

The watchdog waits for an orphaned owned replay driver, not merely for a
gap between compilers, before resuming the held coordinator.
"""
from pathlib import Path
import argparse,ctypes,datetime,hashlib,json,os,subprocess,sys,time
from ctypes import wintypes
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/151-countfree-replay-pilot';Q=R/'milestones/147-countfree-clause-semantics'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
ap=argparse.ArgumentParser();ap.add_argument('--watchdog',type=Path);a=ap.parse_args()
kernel=ctypes.WinDLL('kernel32',use_last_error=True);nt=ctypes.WinDLL('ntdll')
kernel.OpenProcess.argtypes=[wintypes.DWORD,wintypes.BOOL,wintypes.DWORD];kernel.OpenProcess.restype=wintypes.HANDLE
kernel.GetExitCodeProcess.argtypes=[wintypes.HANDLE,ctypes.POINTER(wintypes.DWORD)];kernel.GetExitCodeProcess.restype=wintypes.BOOL
kernel.CloseHandle.argtypes=[wintypes.HANDLE];kernel.CloseHandle.restype=wintypes.BOOL
for name in ['NtSuspendProcess','NtResumeProcess']:
    f=getattr(nt,name);f.argtypes=[wintypes.HANDLE];f.restype=ctypes.c_long
def open_process(pid):
    handle=kernel.OpenProcess(0x0800|0x1000|0x00100000,False,pid)
    if not handle:raise ctypes.WinError(ctypes.get_last_error())
    return handle
def alive(handle):
    code=wintypes.DWORD();assert kernel.GetExitCodeProcess(handle,ctypes.byref(code))
    return code.value==259
def snapshot():
    cmd='@(Get-CimInstance Win32_Process | Where-Object { $_.Name -eq "python.exe" -or $_.Name -eq "lean.exe" } | Select-Object ProcessId,ParentProcessId,Name,CommandLine,CreationDate) | ConvertTo-Json -Compress'
    result=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
    return result if isinstance(result,list) else [result]
def save(path,j):
    temp=path.with_suffix('.pending');temp.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');os.replace(temp,path)
def is_new_driver(row):
    return row['Name']=='python.exe' and '151-countfree-replay-pilot/scripts/run_full_replay.py' in (row['CommandLine'] or '').replace('\\','/')
if a.watchdog:
    j=read(a.watchdog);driver=open_process(j['replay_pid']);controller=open_process(j['controller_pid'])
    try:
        while alive(controller):
            if read(a.watchdog)['status'] in ['RESUMED','ABORTED_BEFORE_HOLD']:sys.exit(0)
            time.sleep(2)
        # The full replay may survive the controller. Keep the old job held
        # until the owned driver and any outstanding compiler have finished.
        while True:
            rows=snapshot()
            owned=[x for x in rows if is_new_driver(x) and x['ParentProcessId']==j['controller_pid']]
            if not owned and not any(x['Name']=='lean.exe' for x in rows):break
            time.sleep(2)
        if alive(driver) and read(a.watchdog)['status'] not in ['RESUMED','ABORTED_BEFORE_HOLD']:
            rc=nt.NtResumeProcess(driver)
            save(a.watchdog.with_name(a.watchdog.stem+'-recovery.json'),dict(status='WATCHDOG_RESUME',return_code=rc,at=datetime.datetime.now(datetime.timezone.utc).isoformat()))
    finally:kernel.CloseHandle(driver);kernel.CloseHandle(controller)
    sys.exit(0)
prep=read(H/'data/preparation.json')
for path,d in prep['source_files_sha256'].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==d,path
assert not (P/'data/full-replay-batch.lock').exists()
newprogress=read(P/'data/full-replay-progress.json')
assert newprogress['status']=='PASS_BOUNDED_FULL_REPLAY_PREFIX' and newprogress['active'] is None
assert len(newprogress['checked_modules'])==49
progress=read(Q/'replay/data/full-replay-progress.json');assert progress['status']=='RUNNING'
pid=progress['pid'];rows=snapshot();matches=[x for x in rows if x['ProcessId']==pid]
assert len(matches)==1 and '147-countfree-clause-semantics/scripts/run_full_replay.py' in matches[0]['CommandLine'].replace('\\','/')
assert not any(is_new_driver(x) for x in rows)
guard=H/'data'/('serialization-'+str(time.time_ns())+'.json')
j=dict(status='PREPARING_HOLD',controller_pid=os.getpid(),replay_pid=pid,replay_process=matches[0],
    replay_session=67526,replay_progress_before=progress,new_replay_progress_before=newprogress,
    started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    scope='Preserve same147 coordinator; run remaining151 full replay alone. A watchdog waits for an orphaned owned full driver before resuming147.')
save(guard,j);driver=open_process(pid);watcher=None;held=False;child=None
try:
    watcher=subprocess.Popen([sys.executable,'-B','-X','utf8',str(Path(__file__).resolve()),'--watchdog',str(guard)],cwd=R)
    rc=nt.NtSuspendProcess(driver);assert rc==0,rc;held=True
    j.update(status='COORDINATOR_HELD',suspend_return_code=rc,watchdog_pid=watcher.pid);save(guard,j)
    start=time.monotonic()
    while True:
        rows=snapshot();existing=[x for x in rows if x['Name']=='lean.exe' or x['ParentProcessId']==pid]
        if not existing:break
        assert time.monotonic()-start<300,existing
        time.sleep(2)
    j.update(status='RUNNING_FULL_REPLAY_ALONE',wait_seconds=time.monotonic()-start);save(guard,j)
    print('CURRENT147_CHECK_FINISHED; RUNNING_COMPLETE012032_REPLAY',flush=True)
    child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(P/'scripts/run_full_replay.py')],cwd=R)
    j['transfer_driver_pid']=child.pid;save(guard,j)
    code=child.wait();j['transfer_exit_code']=code
except BaseException as e:
    j['exception']=repr(e)
    if child is not None and child.poll() is None:
        subprocess.run(['taskkill','/PID',str(child.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    raise
finally:
    if held and alive(driver):
        # Never resume between an orphaned checker and its compiler.
        while any(x['Name']=='lean.exe' for x in snapshot()):time.sleep(2)
        rc=nt.NtResumeProcess(driver);j['resume_return_code']=rc;assert rc==0,rc;j['status']='RESUMED'
    else:j['status']='ABORTED_BEFORE_HOLD'
    j['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save(guard,j)
    kernel.CloseHandle(driver)
    if watcher is not None:watcher.wait(timeout=15)
    print(j['status'],flush=True)
raise SystemExit(j['transfer_exit_code'])
