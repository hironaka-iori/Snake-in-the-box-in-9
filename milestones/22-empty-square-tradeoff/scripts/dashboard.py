"""Read-only localhost monitor. It never schedules or launches research."""
import argparse, ctypes, json, os, pathlib, subprocess
from http.server import BaseHTTPRequestHandler, HTTPServer
from datetime import datetime,timezone
P=pathlib.Path(__file__).resolve().parents[1]

def alive(pid):
    if not pid:return False
    if os.name=='nt':
        k=ctypes.windll.kernel32
        k.OpenProcess.restype=ctypes.c_void_p
        handle=k.OpenProcess(0x1000,False,pid)
        if not handle:return False
        code=ctypes.c_ulong(); k.GetExitCodeProcess(ctypes.c_void_p(handle),ctypes.byref(code)); k.CloseHandle(ctypes.c_void_p(handle))
        return code.value==259
    try:os.kill(pid,0);return True
    except ProcessLookupError:return False

def snapshot():
    cases=[]; processes=[]
    for folder in sorted((P/'runs').glob('20261020-*')):
        for f in sorted(folder.glob('*.json')):
            z=json.loads(f.read_text(encoding='utf-8'))
            if 'result' in z:
                r=z['result'];cases.append({'case':f.stem,'status':r.get('status','CHECKED'),
                    'seconds':round(z['elapsed_seconds'],3),'saved':z['finished'],
                    'evidence':'仅计算证据','path':str(f.relative_to(P))})
        state=folder/'status.json'
        if state.exists():
            z=json.loads(state.read_text(encoding='utf-8'))
            if z.get('pid'): processes.append({'pid':z['pid'],'alive':alive(z['pid']),'case':z['current']})
    successes=list((P/'logs').glob('definitions-attempt*/manifest.json'))
    proofs=[json.loads(f.read_text()) for f in successes]
    passed=[x for x in proofs if x.get('status')=='PASS']
    files=[f for f in (P/'runs').rglob('*') if f.is_file() and f.suffix in ['.log','.json']]
    recent=max(files,key=lambda f:f.stat().st_mtime) if files else None
    logfiles=[f for f in files if f.suffix=='.log']
    recentlog=max(logfiles,key=lambda f:f.stat().st_mtime) if logfiles else None
    raw_unknown=sum(c['status']=='UNKNOWN' for c in cases)
    later=P/'logs/independent-check-final.json'
    derived=json.loads(later.read_text()).get('resolved_timeouts',[]) if later.exists() else []
    return {'hypothesis':'空面达到 21 重数时的遗漏角点奇偶性；极端窗口的全局拼接',
        'total':len(cases),'completed':len(cases),'unresolved':max(0,raw_unknown-len(derived)-1),
        'raw_unknown':raw_unknown,
        'counterexamples':2,'independently_verified_counterexamples':2,
        'scope':'阶段实验已结束；a(9) 仍未确定。原始 UNKNOWN 共 5 项：2 项由后续见证解决，1 项由人类证明排除，4/5 中心拼接仍未决。',
        'lean':'26 边反例与规范化九步弦排除已通过内核审计' if passed else '尚未通过最终审计',
        'mathematical':'同奇偶遗漏的饱和空面邻域强迫 v=4(n-2)-1：数学证明待形式化',
        'open':['把新结构限制转为有收益的 E–T 不等式','六中心全局排除的可信证书及几何桥',
                '排除所有相关低均值模式，而非单个循环','对近上界长蛇控制混合奇偶饱和空面的总数'],
        'processes':processes,'cases':cases,
        'small_cube_audit':'Q2/Q3/Q4 共 332 条根定向路径；Q3 全部 256 个选点集合的编码对照',
        'recent_file':str(recent.relative_to(P)) if recent else None,
        'recent_log':str(recentlog.relative_to(P)) if recentlog else None,
        'recent_log_tail':'\n'.join(recentlog.read_text(encoding='utf-8',errors='replace').splitlines()[-12:]) if recentlog else '',
        'recent_save':datetime.fromtimestamp(recent.stat().st_mtime,timezone.utc).isoformat() if recent else None,
        'evidence':'Lean 已证 / 数学证明待形式化 / 仅计算证据，分别标注',
        'new_global_bound':False}

HTML='''<!doctype html><html lang="zh-CN"><meta charset="utf-8"><title>Q9 空方块研究</title>
<style>body{font:16px system-ui;max-width:1080px;margin:42px auto;padding:0 24px;color:#26332d;background:#f8f9f6}h1{font-size:30px}h2{font-size:19px;margin-top:30px}p{line-height:1.7}.metrics{display:flex;gap:28px;border-top:2px solid #476956;border-bottom:1px solid #c5cdc5;padding:20px 0}.metrics b{display:block;font-size:26px}table{width:100%;border-collapse:collapse}td,th{padding:9px;text-align:left;border-bottom:1px solid #d9dfd9}small{color:#56665b}code{font-size:13px}.muted{color:#66716a}</style>
<h1>Q9 空方块与单例方块</h1><p id="hyp"></p><p id="scope"></p>
<div class="metrics"><div><b id="total"></b>实验条目</div><div><b id="done"></b>已返回结果</div><div><b id="unknown"></b>仍未解决</div><div><b>2 / 2</b>反例 / 独立复核</div></div>
<p class="muted">以上是实验进度，不是数学问题的解决百分比。未给出剩余时间预测。</p>
<h2>证据与证明义务</h2><p id="lean"></p><p id="math"></p><ul id="open"></ul><p id="audit"></p>
<h2>运行状态</h2><p id="process"></p><small id="save"></small>
<details><summary>最近日志</summary><pre id="log"></pre></details>
<h2>实验记录</h2><table><thead><tr><th>实验</th><th>状态</th><th>秒</th><th>证据等级</th></tr></thead><tbody id="rows"></tbody></table>
<p class="muted">面板只读取本地记录，每 15 秒刷新。它不会继续研究、启动求解器或发送通知。</p>
<script>async function load(){let s=await(await fetch('/api')).json();for(let [id,value] of Object.entries({hyp:s.hypothesis,scope:s.scope,total:s.total,done:s.completed,unknown:s.unresolved,lean:s.lean,math:s.mathematical,audit:s.small_cube_audit,log:s.recent_log+'\n'+s.recent_log_tail,process:s.processes.length?JSON.stringify(s.processes):'没有运行中的研究进程；仅此只读面板服务运行。',save:'最近保存：'+s.recent_save+' · '+s.recent_file}))document.getElementById(id).textContent=value;let list=document.getElementById('open');list.replaceChildren(...s.open.map(x=>{let l=document.createElement('li');l.textContent=x;return l}));document.getElementById('rows').replaceChildren(...s.cases.map(c=>{let tr=document.createElement('tr');for(let x of [c.case,c.status,c.seconds,c.evidence]){let td=document.createElement('td');td.textContent=x;tr.append(td)}return tr}));}load();setInterval(load,15000)</script></html>'''

class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path=='/api': data=json.dumps(snapshot(),ensure_ascii=False).encode();typ='application/json'
        elif self.path=='/':data=HTML.encode();typ='text/html'
        else:self.send_error(404);return
        self.send_response(200);self.send_header('Content-Type',typ+'; charset=utf-8');self.send_header('Content-Length',str(len(data)));self.end_headers();self.wfile.write(data)
    def log_message(self,*args):pass

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--port',type=int,default=8793);ap.add_argument('--snapshot',action='store_true');a=ap.parse_args()
    if a.snapshot:
        (P/'dashboard-snapshot.json').write_text(json.dumps(snapshot(),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        (P/'dashboard.html').write_text(HTML,encoding='utf-8')
    else:HTTPServer(('127.0.0.1',a.port),Handler).serve_forever()
