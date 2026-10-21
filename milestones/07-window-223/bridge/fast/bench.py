"""bench.py LABEL file.lean ... : build in order with lc.py, print per-group totals (inputs / steps / main)."""
import subprocess, sys, re, os
label, files = sys.argv[1], sys.argv[2:]
out = subprocess.run(['./lc.py'] + files, capture_output=True, text=True, env=dict(os.environ)).stdout
tot = {'inputs': 0.0, 'steps': 0.0, 'main': 0.0}; peak = 0; ok = True
for l in out.splitlines():
    m = re.match(r'(\S+) rc=(-?\d+) wall ([\d.]+) s cpu ([\d.]+) s peakRSS (\d+) MB', l)
    if not m: continue
    f, rc, cpu, rss = m.group(1), int(m.group(2)), float(m.group(4)), int(m.group(5))
    ok &= rc == 0; peak = max(peak, rss)
    g = 'inputs' if 'Inputs' in f else 'main' if 'Main' in f else 'steps'
    tot[g] += cpu
olean = sum(os.path.getsize(f[:-5] + '.olean') for f in files if os.path.exists(f[:-5] + '.olean'))
line = f"{label}: ok={ok} inputs {tot['inputs']:.1f} s, steps {tot['steps']:.1f} s, main {tot['main']:.1f} s, total {sum(tot.values()):.1f} s CPU; peak RSS {peak} MB; olean {olean/2**20:.0f} MB"
print(line); open('bench.log', 'a').write(line + '\n')
