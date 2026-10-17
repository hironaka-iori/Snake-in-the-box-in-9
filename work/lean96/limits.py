import ctypes,os
_job=None

def memory_limit(mebibytes):
    global _job
    size = mebibytes * 1024**2
    if os.name != 'nt':
        import resource
        resource.setrlimit(resource.RLIMIT_AS,(size,size))
        return 'RLIMIT_AS'
    from ctypes import wintypes as w
    class Basic(ctypes.Structure):
        _fields_=[('process_time',ctypes.c_int64),('job_time',ctypes.c_int64),('flags',w.DWORD),
                  ('min_ws',ctypes.c_size_t),('max_ws',ctypes.c_size_t),('active',w.DWORD),
                  ('affinity',ctypes.c_size_t),('priority',w.DWORD),('scheduling',w.DWORD)]
    class IO(ctypes.Structure):
        _fields_=[(s,ctypes.c_uint64) for s in ['read_ops','write_ops','other_ops','read_bytes','write_bytes','other_bytes']]
    class Extended(ctypes.Structure):
        _fields_=[('basic',Basic),('io',IO),('process_memory',ctypes.c_size_t),
                  ('job_memory',ctypes.c_size_t),('peak_process',ctypes.c_size_t),('peak_job',ctypes.c_size_t)]
    k=ctypes.WinDLL('kernel32',use_last_error=True)
    k.CreateJobObjectW.argtypes=[ctypes.c_void_p,w.LPCWSTR];k.CreateJobObjectW.restype=w.HANDLE
    k.GetCurrentProcess.restype=w.HANDLE
    k.AssignProcessToJobObject.argtypes=[w.HANDLE,w.HANDLE]
    k.SetInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD]
    _job=k.CreateJobObjectW(None,None)
    limits=Extended();limits.basic.flags=0x100;limits.process_memory=size
    if not _job or not k.SetInformationJobObject(_job,9,ctypes.byref(limits),ctypes.sizeof(limits)) or not k.AssignProcessToJobObject(_job,k.GetCurrentProcess()):
        raise ctypes.WinError(ctypes.get_last_error())
    return 'Windows Job Object PROCESS_MEMORY hard commit limit'
