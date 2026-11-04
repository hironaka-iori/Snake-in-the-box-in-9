"""Native process inventory for a single bounded graph worker; no CIM calls."""
import ctypes
from ctypes import wintypes
import re
import native_resources as native


class UNICODE_STRING(ctypes.Structure):
    _fields_ = [('Length', wintypes.USHORT), ('MaximumLength', wintypes.USHORT),
                ('Buffer', ctypes.c_void_p)]


ntdll = ctypes.WinDLL('ntdll', use_last_error=True)
ntdll.NtQueryInformationProcess.argtypes = [wintypes.HANDLE, wintypes.ULONG,
    ctypes.c_void_p, wintypes.ULONG, ctypes.POINTER(wintypes.ULONG)]
ntdll.NtQueryInformationProcess.restype = ctypes.c_long
GRAPH = re.compile(r'(evaluate_(graph|pair|six_shapes)\.py|find_potential\.py|'
                   r'after155_potential_test\.py|run_potential(?:_v[234])?\.py|potential_range(?:_v[234])?\.py)', re.I)


def command_line(handle):
    size = wintypes.ULONG()
    ntdll.NtQueryInformationProcess(handle, 60, None, 0, ctypes.byref(size))
    if not 0 < size.value < 1024*1024:
        raise RuntimeError('Invalid native command-line buffer size')
    buffer = ctypes.create_string_buffer(size.value)
    status = ntdll.NtQueryInformationProcess(handle, 60, buffer, size.value, ctypes.byref(size))
    if status < 0:
        raise RuntimeError('Native command-line query failed: '+hex(status & 0xffffffff))
    value = UNICODE_STRING.from_buffer(buffer)
    pointer = value.Buffer or 0
    if value.Length == 0:
        return ''
    if not (ctypes.addressof(buffer) <= pointer and pointer+value.Length <= ctypes.addressof(buffer)+len(buffer)):
        raise RuntimeError('Invalid native command-line pointer')
    return ctypes.wstring_at(pointer, value.Length//2)


def snapshot(owned=()):
    result = native.snapshot()
    result['lean_processes'] = result.pop('processes')
    result['graph_processes'] = []
    result['owned_memory'] = []
    handle = native.kernel.CreateToolhelp32Snapshot(2, 0)
    if not handle or handle == native.INVALID_HANDLE_VALUE:
        result['errors'].append(dict(api='GraphProcessSnapshot', error=ctypes.get_last_error()))
        return result
    try:
        entry = native.PROCESSENTRY32W(); entry.dwSize = ctypes.sizeof(entry)
        present = native.kernel.Process32FirstW(handle, ctypes.byref(entry))
        if not present and ctypes.get_last_error() != 18:
            result['errors'].append(dict(api='GraphProcess32FirstW', error=ctypes.get_last_error()))
        while present:
            pid = int(entry.th32ProcessID)
            if entry.szExeFile.lower().startswith('python'):
                process = native.kernel.OpenProcess(0x1000, False, pid)
                if not process:
                    error = ctypes.get_last_error()
                    if error != 87:
                        result['errors'].append(dict(api='OpenPythonProcess', pid=pid, error=error))
                else:
                    try:
                        cmd = command_line(process)
                        if GRAPH.search(cmd):
                            result['graph_processes'].append(dict(pid=pid, command=cmd))
                        if pid in owned:
                            memory = native.PROCESS_MEMORY_COUNTERS_EX(); memory.cb = ctypes.sizeof(memory)
                            if not native.psapi.GetProcessMemoryInfo(process, ctypes.byref(memory), memory.cb):
                                raise RuntimeError('Owned process memory query failed')
                            result['owned_memory'].append(dict(pid=pid, private_bytes=int(memory.PrivateUsage)))
                    except Exception as error:
                        code = wintypes.DWORD()
                        if not native.kernel.GetExitCodeProcess(process, ctypes.byref(code)) or code.value == 259:
                            result['errors'].append(dict(api='PythonProcessQuery', pid=pid, error=str(error)))
                    finally:
                        native.kernel.CloseHandle(process)
            present = native.kernel.Process32NextW(handle, ctypes.byref(entry))
        if ctypes.get_last_error() != 18:
            result['errors'].append(dict(api='GraphProcess32NextW', error=ctypes.get_last_error()))
    finally:
        native.kernel.CloseHandle(handle)
    return result
