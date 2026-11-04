"""Check the broader interpretation only after the recovered152 compiler finishes."""
from pathlib import Path
import ctypes,datetime,hashlib,json,os,subprocess,sys,time
from ctypes import wintypes
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/152-countfree-share16-completion'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
receipt=H/'data/continuation-progress.json';assert not receipt.exists()
recovery_path=P/'data/reboot-recovery-v2-progress.json';recovery=read(recovery_path)
kernel=ctypes.WinDLL('kernel32',use_last_error=True)
kernel.OpenProcess.argtypes=[wintypes.DWORD,wintypes.BOOL,wintypes.DWORD];kernel.OpenProcess.restype=wintypes.HANDLE
kernel.GetExitCodeProcess.argtypes=[wintypes.HANDLE,ctypes.POINTER(wintypes.DWORD)];kernel.GetExitCodeProcess.restype=wintypes.BOOL
kernel.CloseHandle.argtypes=[wintypes.HANDLE]
handle=kernel.OpenProcess(0x1000,False,recovery['pid'])
assert handle or recovery['status']=='PASS_RECOVERED_ACTUAL_SNAKE_COMPOSITION'
pins={str(p):sha(p) for p in [Path(__file__),H/'scripts/run_semantics.py',H/'scripts/check_module.py',
    H/'data/semantic-plan.json',P/'scripts/audit_actual_after_reboot.py']}
state=dict(status='WAITING_FOR_RECOVERED152',pid=os.getpid(),waited_for_pid=recovery['pid'],
    source_files_sha256=pins,started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),stages=[])
def save():
    tmp=receipt.with_suffix('.pending');tmp.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8');os.replace(tmp,receipt)
save()
try:
    while True:
        recovery=read(recovery_path)
        if recovery['status']=='PASS_RECOVERED_ACTUAL_SNAKE_COMPOSITION':break
        assert recovery['status'] in ['CHECKING_REMAINING_REPLAY','AUDITING_COMPLETE_REPLAY','CHECKING_ACTUAL_SNAKE_CONSEQUENCE']
        code=wintypes.DWORD();assert kernel.GetExitCodeProcess(handle,ctypes.byref(code)) and code.value==259
        time.sleep(2)
    if handle:kernel.CloseHandle(handle);handle=None
    for script,label in [(P/'scripts/audit_actual_after_reboot.py','AUDITING_RECOVERED152'),
                         (H/'scripts/run_semantics.py','CHECKING_BROADER_INTERPRETATION')]:
        for path,digest in pins.items():assert sha(path)==digest,path
        state['status']=label
        (H/'logs').mkdir(exist_ok=True)
        log=H/'logs'/('continuation-'+script.name+'.log');assert not log.exists()
        with log.open('w',encoding='utf-8') as output:
            child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(script)],cwd=R,stdout=output,stderr=subprocess.STDOUT)
            state['active_pid']=child.pid;save();code=child.wait()
        state['stages'].append(dict(script=str(script),exit_code=code,log=str(log),log_sha256=sha(log)))
        state['active_pid']=None;save();assert code==0,(script,code)
    state['status']='PASS_BROADER_SEMANTICS_AND_CONDITIONAL_TRANSFER'
except BaseException as error:
    state.update(status='FAILED_REQUIRES_INSPECTION',exception=repr(error));raise
finally:
    if handle:kernel.CloseHandle(handle)
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    print(json.dumps({k:state[k] for k in ['status','pid','stages']}),flush=True)
