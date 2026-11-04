"""Wait for the identified full driver; never restart or replace that job."""
from pathlib import Path
import ctypes, datetime, hashlib, json, os, subprocess, sys, time
from ctypes import wintypes

H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
kernel=ctypes.WinDLL('kernel32',use_last_error=True)
kernel.OpenProcess.argtypes=[wintypes.DWORD,wintypes.BOOL,wintypes.DWORD];kernel.OpenProcess.restype=wintypes.HANDLE
kernel.GetProcessTimes.argtypes=[wintypes.HANDLE]+[ctypes.POINTER(wintypes.FILETIME)]*4;kernel.GetProcessTimes.restype=wintypes.BOOL
kernel.GetExitCodeProcess.argtypes=[wintypes.HANDLE,ctypes.POINTER(wintypes.DWORD)];kernel.GetExitCodeProcess.restype=wintypes.BOOL
kernel.QueryFullProcessImageNameW.argtypes=[wintypes.HANDLE,wintypes.DWORD,wintypes.LPWSTR,ctypes.POINTER(wintypes.DWORD)];kernel.QueryFullProcessImageNameW.restype=wintypes.BOOL
kernel.WaitForSingleObject.argtypes=[wintypes.HANDLE,wintypes.DWORD];kernel.WaitForSingleObject.restype=wintypes.DWORD
kernel.CloseHandle.argtypes=[wintypes.HANDLE];kernel.CloseHandle.restype=wintypes.BOOL

def identity(handle):
    created=wintypes.FILETIME();exited=wintypes.FILETIME();kt=wintypes.FILETIME();ut=wintypes.FILETIME()
    assert kernel.GetProcessTimes(handle,ctypes.byref(created),ctypes.byref(exited),ctypes.byref(kt),ctypes.byref(ut))
    size=wintypes.DWORD(32768);buffer=ctypes.create_unicode_buffer(size.value)
    assert kernel.QueryFullProcessImageNameW(handle,0,buffer,ctypes.byref(size))
    code=wintypes.DWORD();assert kernel.GetExitCodeProcess(handle,ctypes.byref(code))
    return dict(creation_filetime=(int(created.dwHighDateTime)<<32)|int(created.dwLowDateTime),
                image=str(Path(buffer.value).resolve()),exit_code=int(code.value))

def main():
    planpath=H/'data/final-composition-plan.json';plan=read(planpath);planhash=sha(planpath)
    assert plan['status']=='PREPARED_COUNT_CONDITIONED_ACTUAL_SNAKE_COMPOSITION'
    progress=H/'data/final-continuation-progress.json';lock=H/'data/final-continuation.lock'
    assert not progress.exists(), 'Inspect the existing continuation before creating another'
    pins=plan['script_pins']
    for path,digest in pins.items():assert sha(R/path)==digest,path
    expected=plan['full_driver'];driver=None
    # Hold an actual process handle across the wait so PID reuse cannot be mistaken for completion.
    handle=kernel.OpenProcess(0x1000|0x00100000,False,expected['pid'])
    if handle:
        observed=identity(handle)
        if observed['creation_filetime']!=expected['creation_filetime'] or Path(observed['image'])!=Path(expected['image']):
            kernel.CloseHandle(handle);raise AssertionError('Original full-driver identity no longer matches')
        driver=handle
    else:
        # If it finished before this continuation was launched, only an already
        # completed exact progress record can permit the saved-evidence audit.
        completed=read(H/'data/full-replay-progress.json')
        assert completed['pid']==expected['pid'] and completed['started_at']==expected['started_at']
        assert completed['status']=='PASS_COMPLETE_FULL_REPLAY_MODULES' and completed['active'] is None
        assert len(completed['checked_modules'])==137
    with lock.open('x',encoding='utf-8') as out:json.dump(dict(pid=os.getpid()),out)
    state=dict(status='WAITING_FOR_SAME_FULL_DRIVER',pid=os.getpid(),
        started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),plan_sha256=planhash,
        expected_full_driver=expected,held_process_handle=driver is not None,stages=[],active_pid=None)
    def save():
        temporary=progress.with_suffix('.pending')
        temporary.write_bytes((json.dumps(state,indent=2)+'\n').encode('utf-8'));os.replace(temporary,progress)
    save()
    try:
        if driver is not None:
            while True:
                assert sha(planpath)==planhash
                result=kernel.WaitForSingleObject(driver,2000)
                assert result in [0,258],result
                if result==0:break
                # A partial progress-file write is observational only; the live
                # process handle is authoritative while the driver is running.
                try:
                    live=read(H/'data/full-replay-progress.json')
                    assert live['pid']==expected['pid'] and live['started_at']==expected['started_at']
                    assert live['driver_sha256']==expected['driver_sha256']
                    state['last_checked_modules']=len(live['checked_modules'])
                except (OSError,json.JSONDecodeError):
                    pass
                save()
            observed=identity(driver);assert observed['exit_code']==0,observed
            state['driver_exit']=observed
        completed=read(H/'data/full-replay-progress.json')
        assert completed['pid']==expected['pid'] and completed['started_at']==expected['started_at']
        assert completed['driver_sha256']==expected['driver_sha256']
        assert completed['status']=='PASS_COMPLETE_FULL_REPLAY_MODULES' and completed['active'] is None
        assert len(completed['checked_modules'])==137 and not (H/'data/full-replay-batch.lock').exists()
        stages=[('finish_full_replay.py', ['--verify-only'] if (H/'data/full-replay-completion.json').exists() else [],
                 'AUDITING_COMPLETE_SHARED_CORE'),
                ('check_final.py',['ShareComplete155'],'CHECKING_ACTUAL_SNAKE_COMPOSITION'),
                ('audit_actual.py',[],'AUDITING_ACTUAL_SNAKE_RESULT')]
        for name,args,label in stages:
            assert sha(planpath)==planhash
            for path,digest in pins.items():assert sha(R/path)==digest,path
            state['status']=label;save()
            if name=='check_final.py' and (H/'data/ShareComplete155-audit.json').exists():
                existing=read(H/'data/ShareComplete155-audit.json')
                assert existing['status']=='PASS' and existing['exit_code']==0 and existing['stop_reason'] is None
                state['stages'].append(dict(script=name,status='EXISTING_RECEIPT_AUDIT_REQUIRED'));save();continue
            log=H/'logs'/('final-continuation-'+str(time.time_ns())+'-'+name+'.log')
            with log.open('w',encoding='utf-8') as out:
                child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts'/name),*args],cwd=R,stdout=out,stderr=subprocess.STDOUT)
                state['active_pid']=child.pid;save();code=child.wait()
            state['active_pid']=None
            state['stages'].append(dict(script=name,arguments=args,exit_code=code,log=str(log),log_sha256=sha(log)))
            save();assert code==0,(name,code)
        accepted=read(H/'data/actual-snake-completion.json')
        assert accepted['status']=='PASS_ACTUAL_SNAKE_SHARE17_WITH_COUNT_CONDITIONS'
        state.update(status='PASS_COUNT_CONDITIONED_ACTUAL_SNAKE_SHARE17',
            completion_sha256=sha(H/'data/actual-snake-completion.json'))
    except BaseException as error:
        state.update(status='FAILED_REQUIRES_INSPECTION',exception=repr(error));raise
    finally:
        if driver is not None:kernel.CloseHandle(driver)
        state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();lock.unlink()
        print(json.dumps(state),flush=True)

if __name__=='__main__':main()
