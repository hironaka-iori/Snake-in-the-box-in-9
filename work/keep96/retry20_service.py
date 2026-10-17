"""One bounded retry of the twenty unresolved cases, with a separate dashboard."""
import json, os, subprocess, sys, threading, msvcrt
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from common import OUT, ROOT, HERE, save

STATE = OUT / 'retry20-runner.json'
def read(path):
    return json.loads(path.read_text(encoding='utf-8')) if path.exists() else {}

def snapshot():
    return dict(runner=read(STATE), results=read(OUT/'retry20-results.json'),
                log=(OUT/'retry20.stdout.log').read_text(encoding='utf-8')[-3000:] if (OUT/'retry20.stdout.log').exists() else '')

PAGE = '''<!doctype html><html lang="zh"><meta charset="utf-8"><title>96档 · 20入口续算</title>
<style>body{max-width:900px;margin:60px auto;padding:20px;background:#f4f3ef;color:#222;font:18px system-ui}h1{font-size:30px}pre{background:white;padding:24px;white-space:pre-wrap;font-size:14px}#count{font-size:36px}p{line-height:1.7}</style>
<h1>96档 · 剩余20个入口</h1><p>每个入口最多5分钟、2GB内存。这里只显示求解器结果，不表示Lean证明完成。</p><div id="count"></div><p id="status"></p><pre id="log"></pre>
<script>async function refresh(){try{let s=await(await fetch('/api/status')).json();let r=s.results.entries||[];let n=k=>r.filter(x=>x.status===k).length;document.querySelector('#count').textContent=r.length+' / 20 已保存';document.querySelector('#status').textContent=s.runner.status+' · UNSAT '+n('UNSAT')+' · SAT '+n('SAT')+' · 未决 '+n('UNKNOWN');document.querySelector('#log').textContent=s.log}catch(e){document.querySelector('#status').textContent='暂时无法连接后台'}}refresh();setInterval(refresh,5000)</script></html>'''

class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        data = json.dumps(snapshot(),ensure_ascii=False) if self.path=='/api/status' else PAGE
        self.send_response(200);self.send_header('Content-Type','application/json; charset=utf-8' if self.path=='/api/status' else 'text/html; charset=utf-8');self.end_headers();self.wfile.write(data.encode())
    def log_message(self,*args): pass

def main():
    guard=(OUT/'retry20.lock').open('a+b');guard.seek(0);guard.write(b'0');guard.flush();guard.seek(0)
    msvcrt.locking(guard.fileno(),msvcrt.LK_NBLCK,1)
    entries=read(OUT/'summary.json')['unknown_entries']
    assert len(entries)==20
    server=ThreadingHTTPServer(('127.0.0.1',51994),Handler)
    state=dict(pid=os.getpid(),status='RUNNING',entries=entries,seconds_per_entry=300,memory_mib=2048,started_utc=datetime.now(timezone.utc).isoformat())
    save(STATE,state)
    def run():
        try:
            with (OUT/'retry20.stdout.log').open('a',encoding='utf-8') as out, (OUT/'retry20.stderr.log').open('a',encoding='utf-8') as err:
                proc=subprocess.Popen([sys.executable,'-u',str(HERE/'run.py'),'--phase','retry20','--seconds','300','--memory-mib','2048','--entries',*map(str,entries)],cwd=ROOT,stdout=out,stderr=err)
                state['driver_pid']=proc.pid;save(STATE,state);rc=proc.wait()
            state.update(status='COMPLETED' if rc==0 else 'FAILED',exit_code=rc,finished_utc=datetime.now(timezone.utc).isoformat());save(STATE,state)
        except Exception as exc:
            state.update(status='FAILED',error=str(exc));save(STATE,state)
    threading.Thread(target=run,daemon=True).start()
    server.serve_forever()

if __name__=='__main__':main()
