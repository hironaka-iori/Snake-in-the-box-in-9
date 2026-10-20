"""Read-only local monitor. No solver launching or file mutations through HTTP."""
import argparse
import ctypes
import json
import os
from pathlib import Path
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlsplit

HERE=Path(__file__).resolve().parents[1]

def alive(pid):
    if os.name=='nt':
        kernel=ctypes.WinDLL('kernel32',use_last_error=True)
        kernel.OpenProcess.restype=ctypes.c_void_p
        kernel.OpenProcess.argtypes=[ctypes.c_ulong,ctypes.c_int,ctypes.c_ulong]
        kernel.CloseHandle.argtypes=[ctypes.c_void_p]
        kernel.GetExitCodeProcess.argtypes=[ctypes.c_void_p,ctypes.POINTER(ctypes.c_ulong)]
        h=kernel.OpenProcess(0x1000,False,pid)
        if not h: return False
        code=ctypes.c_ulong()
        ok=kernel.GetExitCodeProcess(h,ctypes.byref(code)); kernel.CloseHandle(h)
        return bool(ok and code.value==259)
    try: os.kill(pid,0); return True
    except OSError: return False

def snapshot():
    data=json.loads((HERE/'analysis.json').read_text(encoding='utf-8'))
    jobs=[]
    for p in (HERE/'runs').rglob('RUNNING.lock'):
        row=json.loads(p.read_text(encoding='utf-8'))
        jobs.append(dict(run=p.parent.name,**row,process_alive=alive(row['pid'])))
    logs=sorted((HERE/'runs').rglob('*.log'),key=lambda p:p.stat().st_mtime)
    latest=logs[-1] if logs else None
    return dict(**data,monitor_pid=os.getpid(),jobs=jobs,
        recent_log=str(latest.relative_to(HERE)) if latest else None,
        recent_log_tail=latest.read_text(encoding='utf-8')[-2500:] if latest else '',
        last_saved=max(a['saved'] for a in data['solver_attempts']))

class Handler(SimpleHTTPRequestHandler):
    def __init__(self,*args,**kwargs): super().__init__(*args,directory=str(HERE),**kwargs)
    def do_GET(self):
        path=urlsplit(self.path).path
        if path=='/api/status':
            body=json.dumps(snapshot(),ensure_ascii=False).encode()
            self.send_response(200); self.send_header('Content-Type','application/json; charset=utf-8')
            self.send_header('Cache-Control','no-store'); self.end_headers(); self.wfile.write(body)
        else:
            if path=='/': self.path='/dashboard.html'
            super().do_GET()
    def log_message(self,*args): pass

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--port',type=int,default=8794); args=ap.parse_args()
    print(f'Read-only saturated-pair monitor PID {os.getpid()} at http://127.0.0.1:{args.port}',flush=True)
    ThreadingHTTPServer(('127.0.0.1',args.port),Handler).serve_forever()
