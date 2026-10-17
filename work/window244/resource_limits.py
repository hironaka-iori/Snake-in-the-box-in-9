"""External approximate per-process memory budget for kernel compilation."""
import ctypes,os,pathlib,subprocess,time

if os.name=='nt':
    class MemoryCounters(ctypes.Structure):
        _fields_=[('cb',ctypes.c_ulong),('PageFaultCount',ctypes.c_ulong)]+[(n,ctypes.c_size_t) for n in ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage','PrivateUsage']]
    memory_info=ctypes.WinDLL('psapi').GetProcessMemoryInfo
    memory_info.argtypes=[ctypes.c_void_p,ctypes.POINTER(MemoryCounters),ctypes.c_ulong]
    memory_info.restype=ctypes.c_int

def run_bounded(command,log,*,cwd,env,limit_mib=1800):
    peak=0;exceeded=False
    with subprocess.Popen(command,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT) as proc:
        while proc.poll() is None:
            if os.name=='nt':
                info=MemoryCounters();info.cb=ctypes.sizeof(info)
                if memory_info(int(proc._handle),ctypes.byref(info),info.cb):
                    peak=max(peak,info.PrivateUsage,info.PeakPagefileUsage)
            elif pathlib.Path('/proc').exists():
                try:
                    fields=dict(line.split(':',1) for line in pathlib.Path(f'/proc/{proc.pid}/status').read_text().splitlines() if ':' in line)
                    peak=max(peak,int(fields.get('VmHWM','0 kB').split()[0])*1024)
                except (FileNotFoundError,ProcessLookupError):pass
            else:
                proc.kill();proc.wait();raise RuntimeError('No memory monitor is implemented for this platform')
            if peak>limit_mib*1024**2:
                exceeded=True;proc.kill();break
            time.sleep(.2)
        code=proc.wait()
    if exceeded:log.write(f'\nExternal memory budget exceeded ({limit_mib} MiB).\n')
    return dict(exit_code=code,peak_bytes=peak,memory_exceeded=exceeded,
                memory_metric='private_commit' if os.name=='nt' else 'peak_resident',limit_mib=limit_mib)
