"""Read-only local dashboard; no proof runner is launched by HTTP requests."""
from common import *
from http.server import ThreadingHTTPServer,BaseHTTPRequestHandler
import psutil
def snapshot():
    s=read(OUT/'progress.json',{})
    active=False
    try:
        p=psutil.Process(s.get('pid',-1))
        active=p.is_running() and abs(p.create_time()-s.get('process_created',0))<1
    except (psutil.Error,ValueError):pass
    s['runner_active']=active
    if s.get('status')=='RUNNING' and not active:s['status']='STOPPED_UNEXPECTEDLY'
    s['total_entries']=262;s['total_representatives']=len(read(OUT/'cover.json',{}).get('representatives',[]))
    modules=read(OUT/'modules.json',{})
    s['completed_modules']=sum(r['status']=='PASSED' for r in modules.values())
    recent=sorted(modules.items(),key=lambda x:x[1]['finished'],reverse=True)[:8]
    s['recent_logs']=[dict(module=n,status=r['status'],seconds=r['seconds'],log=r['log']) for n,r in recent]
    s['eta']='Not estimated: representative certificate costs vary substantially.'
    s['historical_solver']={'UNSAT':242,'UNKNOWN':20,'note':'Historical survey, not Lean results. Missing artifacts are not counted as verified.'}
    return s
class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path=='/status.json':
            content=json.dumps(snapshot()).encode();kind='application/json'
        elif self.path in ('/','/index.html'):
            content=(HERE/'dashboard.html').read_bytes();kind='text/html; charset=utf-8'
        else:self.send_error(404);return
        self.send_response(200);self.send_header('Content-Type',kind);self.send_header('Cache-Control','no-store');self.end_headers();self.wfile.write(content)
    def log_message(self,*args):pass
if __name__=='__main__':ThreadingHTTPServer(('127.0.0.1',52096),Handler).serve_forever()
