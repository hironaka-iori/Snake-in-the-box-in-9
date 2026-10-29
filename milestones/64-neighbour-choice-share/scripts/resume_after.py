"""Wait for a confirmed Windows process to exit, then resume with two workers."""
from pathlib import Path
import ctypes,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
pid=int(sys.argv[1]);kernel=ctypes.WinDLL('kernel32',use_last_error=True)
kernel.OpenProcess.argtypes=[ctypes.c_ulong,ctypes.c_int,ctypes.c_ulong]
kernel.OpenProcess.restype=ctypes.c_void_p
kernel.WaitForSingleObject.argtypes=[ctypes.c_void_p,ctypes.c_ulong]
kernel.WaitForSingleObject.restype=ctypes.c_ulong
kernel.CloseHandle.argtypes=[ctypes.c_void_p]
handle=kernel.OpenProcess(0x00100000,False,pid)
if handle:
    print('Waiting for confirmed replay process',pid,'to exit',flush=True)
    result=kernel.WaitForSingleObject(handle,0xFFFFFFFF)
    kernel.CloseHandle(handle)
    if result!=0:raise OSError('Process wait failed: '+str(result))
else:
    error=ctypes.get_last_error()
    if error!=87:raise OSError(error,'Unable to observe prior process')
    print('Prior process no longer exists',flush=True)
print('Prior process exited; resuming source-checked progress with two workers',flush=True)
with (HERE/'logs/replay-two-workers.log').open('w',encoding='utf-8') as f:
    result=subprocess.run([sys.executable,'-X','utf8',str(HERE/'scripts/replay.py'),'--resume','--workers','2'],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
print('Replay exit code',result.returncode,flush=True)
sys.exit(result.returncode)
