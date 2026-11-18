"""Bounded-cost Windows memory/process snapshots without CIM or subprocesses."""
import ctypes
from ctypes import wintypes
import json
import time


class MEMORYSTATUSEX(ctypes.Structure):
    _fields_ = [('dwLength', wintypes.DWORD), ('dwMemoryLoad', wintypes.DWORD)] + [
        (name, ctypes.c_ulonglong) for name in ['ullTotalPhys', 'ullAvailPhys',
        'ullTotalPageFile', 'ullAvailPageFile', 'ullTotalVirtual', 'ullAvailVirtual',
        'ullAvailExtendedVirtual']]


class PROCESSENTRY32W(ctypes.Structure):
    _fields_ = [('dwSize', wintypes.DWORD), ('cntUsage', wintypes.DWORD),
        ('th32ProcessID', wintypes.DWORD), ('th32DefaultHeapID', ctypes.c_size_t),
        ('th32ModuleID', wintypes.DWORD), ('cntThreads', wintypes.DWORD),
        ('th32ParentProcessID', wintypes.DWORD), ('pcPriClassBase', wintypes.LONG),
        ('dwFlags', wintypes.DWORD), ('szExeFile', wintypes.WCHAR * 260)]


class PROCESS_MEMORY_COUNTERS_EX(ctypes.Structure):
    _fields_ = [('cb', wintypes.DWORD), ('PageFaultCount', wintypes.DWORD)] + [
        (name, ctypes.c_size_t) for name in ['PeakWorkingSetSize', 'WorkingSetSize',
        'QuotaPeakPagedPoolUsage', 'QuotaPagedPoolUsage', 'QuotaPeakNonPagedPoolUsage',
        'QuotaNonPagedPoolUsage', 'PagefileUsage', 'PeakPagefileUsage', 'PrivateUsage']]


kernel = ctypes.WinDLL('kernel32', use_last_error=True)
psapi = ctypes.WinDLL('psapi', use_last_error=True)
kernel.GlobalMemoryStatusEx.argtypes = [ctypes.POINTER(MEMORYSTATUSEX)]
kernel.GlobalMemoryStatusEx.restype = wintypes.BOOL
kernel.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
kernel.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
for name in ['Process32FirstW', 'Process32NextW']:
    function = getattr(kernel, name)
    function.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
    function.restype = wintypes.BOOL
kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
kernel.OpenProcess.restype = wintypes.HANDLE
kernel.GetExitCodeProcess.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD)]
kernel.GetExitCodeProcess.restype = wintypes.BOOL
kernel.CloseHandle.argtypes = [wintypes.HANDLE]
kernel.CloseHandle.restype = wintypes.BOOL
psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE,
    ctypes.POINTER(PROCESS_MEMORY_COUNTERS_EX), wintypes.DWORD]
psapi.GetProcessMemoryInfo.restype = wintypes.BOOL
INVALID_HANDLE_VALUE = ctypes.c_void_p(-1).value


def snapshot():
    """Return physical memory and private bytes of live lean.exe processes.

    Unknown live-process memory is an error, never a fabricated zero. Processes
    that exit between enumeration and measurement are omitted. All owned API
    handles are closed before return. Callers must reject a nonempty errors list.
    """
    started = time.monotonic()
    out = dict(free_bytes=0, total_bytes=0, processes=[], errors=[],
               provider='GlobalMemoryStatusEx+Toolhelp32+GetProcessMemoryInfo')
    memory = MEMORYSTATUSEX();memory.dwLength = ctypes.sizeof(memory)
    if kernel.GlobalMemoryStatusEx(ctypes.byref(memory)):
        out.update(free_bytes=int(memory.ullAvailPhys), total_bytes=int(memory.ullTotalPhys),
                   memory_load_percent=int(memory.dwMemoryLoad))
    else:
        out['errors'].append(dict(api='GlobalMemoryStatusEx', error=ctypes.get_last_error()))
    handle = kernel.CreateToolhelp32Snapshot(0x00000002, 0)
    if handle == INVALID_HANDLE_VALUE or not handle:
        out['errors'].append(dict(api='CreateToolhelp32Snapshot', error=ctypes.get_last_error()))
    else:
        try:
            entry = PROCESSENTRY32W();entry.dwSize = ctypes.sizeof(entry)
            present = kernel.Process32FirstW(handle, ctypes.byref(entry))
            if not present and ctypes.get_last_error() != 18:
                out['errors'].append(dict(api='Process32FirstW', error=ctypes.get_last_error()))
            while present:
                if entry.szExeFile.lower() == 'lean.exe':
                    pid = int(entry.th32ProcessID)
                    # Windows permits this query with limited information access.
                    process = kernel.OpenProcess(0x1000, False, pid)
                    if not process:
                        error = ctypes.get_last_error()
                        if error != 87:  # Invalid parameter means the PID exited.
                            out['errors'].append(dict(api='OpenProcess', pid=pid, error=error))
                    else:
                        try:
                            counters = PROCESS_MEMORY_COUNTERS_EX();counters.cb = ctypes.sizeof(counters)
                            if psapi.GetProcessMemoryInfo(process, ctypes.byref(counters), counters.cb):
                                out['processes'].append(dict(ProcessId=pid,
                                    ParentProcessId=int(entry.th32ParentProcessID),
                                    PrivatePageCount=int(counters.PrivateUsage),
                                    WorkingSetSize=int(counters.WorkingSetSize)))
                            else:
                                error = ctypes.get_last_error();exit_code = wintypes.DWORD()
                                if not kernel.GetExitCodeProcess(process, ctypes.byref(exit_code)) or exit_code.value == 259:
                                    out['errors'].append(dict(api='GetProcessMemoryInfo', pid=pid, error=error))
                        finally:
                            kernel.CloseHandle(process)
                present = kernel.Process32NextW(handle, ctypes.byref(entry))
            if ctypes.get_last_error() != 18:
                out['errors'].append(dict(api='Process32NextW', error=ctypes.get_last_error()))
        finally:
            kernel.CloseHandle(handle)
    out['snapshot_seconds'] = time.monotonic() - started
    return out


if __name__ == '__main__':
    print(json.dumps(snapshot()))
