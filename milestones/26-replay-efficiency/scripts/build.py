# build.py SRCROOT MOD  -> compile LocalWindowUnsat/MOD/{Data*,Check*} and main with lean -o; prints per-module size/time/rss
import json, os, re, subprocess, sys, time
LEAN=os.environ.get('LEAN', os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.19.0/bin/lean'))
LIB=os.path.join(os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')), 'work', 'final_lean', '.lake', 'build', 'lib', 'lean')
src, mod = sys.argv[1], sys.argv[2]
only = sys.argv[3] if len(sys.argv) > 3 else None   # 'data' to skip checks
outl = os.path.join(src, '_olean')
env = dict(os.environ, LEAN_PATH=outl + ':' + os.environ.get('STUDY', '/tmp/replay-study') + '/oleanstudy/lib:' + LIB)
d = os.path.join(src, 'LocalWindowUnsat', mod)
def key(f):
    m = re.match(r'(Data|Check|Main)(\d*)', f); return ({'Data':0,'Check':1,'Main':2}[m.group(1)], int(m.group(2) or 0))
files = sorted([f[:-5] for f in os.listdir(d) if f.endswith('.lean')], key=key) if os.path.isdir(d) else []
mods = [('LocalWindowUnsat/%s/%s' % (mod, f)) for f in files]
if os.path.exists(os.path.join(src, 'LocalWindowUnsat', mod + '.lean')): mods.append('LocalWindowUnsat/' + mod)
res = []
for m in mods:
    if only == 'data' and '/Check' in m: continue
    if only == 'nomain' and m.endswith(mod): continue
    o = os.path.join(outl, m + '.olean'); os.makedirs(os.path.dirname(o), exist_ok=True)
    if only == 'checks' and '/Check' not in m: continue
    if os.path.exists(o) and os.path.getmtime(o) > os.path.getmtime(os.path.join(src, m + '.lean')) and only != 'checks': continue
    t = time.time()
    p = subprocess.Popen(['nice','-n','15',LEAN,'-o',o,os.path.join(src,m+'.lean')],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    import threading
    def guard(pid=p.pid):
        while True:
            try:
                rss = int([l for l in open('/proc/%d/status' % pid) if l.startswith('VmRSS')][0].split()[1])
            except Exception:
                return
            if rss > 2.9e6:
                os.kill(pid, 9); print('KILLED: RSS cap', flush=True); return
            time.sleep(0.3)
    threading.Thread(target=guard, daemon=True).start()
    outp = p.stdout.read(); _, st, ru = os.wait4(p.pid, 0); p.returncode = 0
    dt = time.time()-t
    if st: print(outp[-3000:].decode()); sys.exit(1)
    rss = ru.ru_maxrss/1e6
    rec = dict(module=m.split('/')[-1], src=os.path.getsize(os.path.join(src,m+'.lean')), olean=os.path.getsize(o), sec=round(dt,2), cpu=round(ru.ru_utime+ru.ru_stime,2), rss_gb=round(rss,3))
    print(json.dumps(rec), flush=True)
    open(os.path.join(src, 'results.jsonl'), 'a').write(json.dumps(dict(rec, window=mod)) + '\n')
