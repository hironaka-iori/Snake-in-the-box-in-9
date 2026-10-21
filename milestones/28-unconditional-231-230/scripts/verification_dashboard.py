"""Read-only combined dashboard, independent of frozen worker controllers."""
import argparse
import http.server
import json
from pathlib import Path
import runner as r
from fast_share_batch import PAGE

RUNTIME=r.HERE/'runtime'
TARGETS=['FastCountD012A11.LocalWindow','FastCountD012A12.LocalWindow',
    'FastCountD012A13.LocalWindow','FastCountQ012A14.LocalWindow']

PAGE=PAGE.replace('条件式聚合独立重建','条件式聚合闭包核验')
PAGE=PAGE.replace("Object.keys(f.completed??{}).length+' / 220'", "f.completed_count+' / 220'")
PAGE=PAGE.replace("['检查点',s.checkpoint]", "['两中心计数局部反证',s.counts.completed+' / 4'],['计数检查状态 / 当前项',s.counts.status+' / '+s.counts.current],['检查点',s.checkpoint]")

def state():
    kernel=r.read(RUNTIME/'fast-kernel/state.json')
    app=r.read(RUNTIME/'applicability/state.json')
    old=r.read(RUNTIME/'fresh/97db4f7433a54258ca26ec7329a81011781290c3/ParallelShareAggregate231/state.json')
    repair=r.HERE/'data/aggregate-231-repaired-build.json'
    if repair.exists():
        leaf=r.read(repair)
        aggregate=dict(status='已通过：219 个独立重建依赖 + 修复末项复检',current=leaf['source_commit'][:8],
            completed_count=leaf['modules'],failure=None)
    else:
        aggregate=dict(status=old['status'],current=old.get('current'),failure=old.get('failure'),
            completed_count=len(old['completed']))
    dev=r.read(RUNTIME/'bridge-development/state.json')
    done=[t for t in TARGETS if t in dev['completed']]
    counts=dict(completed=len(done),status='已通过' if len(done)==4 else '需核对进程与日志',current=None)
    for p in r.psutil.process_iter(['pid','cmdline']):
        args=p.info['cmdline'] or []
        if len(args)>2 and Path(args[0]).name=='python.exe' and any(x.endswith('develop_lean.py') for x in args) and TARGETS[0] in args:
            counts.update(status='运行中',pid=p.pid)
            try:
                children=p.children(recursive=True)
                counts['current']=Path(children[-1].cmdline()[-1]).stem if children else '准备下一模块'
            except r.psutil.NoSuchProcess:pass
    return dict(kernel={k:kernel.get(k) for k in ['kernel_cases','status','current_item','phase','last_progress','resources','failures']},
        applicability={k:app.get(k) for k in ['applicability_cases','status','current_item','last_progress','failures']},
        live=r.read(RUNTIME/'applicability/live.json'),aggregate=aggregate,counts=counts,
        checkpoint=str(RUNTIME/'fast-kernel/state.json'))

def serve(port):
    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path=='/state':data=json.dumps(state(),ensure_ascii=False).encode();kind='application/json'
            elif self.path=='/log':
                p=r.read(RUNTIME/'fast-kernel/state.json').get('latest_log')
                data=('\n'.join(Path(p).read_text(encoding='utf-8',errors='replace').splitlines()[-20:]) if p else '').encode();kind='text/plain'
            else:data=PAGE.encode();kind='text/html'
            self.send_response(200);self.send_header('Content-Type',kind+'; charset=utf-8')
            self.send_header('Cache-Control','no-store');self.end_headers();self.wfile.write(data)
        def log_message(self,*args):pass
    http.server.ThreadingHTTPServer(('127.0.0.1',port),Handler).serve_forever()

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--port',type=int,default=8798)
    serve(parser.parse_args().port)
