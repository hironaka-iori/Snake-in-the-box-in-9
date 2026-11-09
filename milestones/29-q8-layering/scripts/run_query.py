"""One SAT query with the level encoding, as used for data/q7_runs.txt and data/q8_runs.txt.
usage: python3 run_query.py n c L [plain|s6|s65]
  plain : base encoding + levels (D = 2^(n-2)) + symmetry breaking
  s6    : plus |F cap Q6| <= g6(#pieces) on every 6-subcube (exact g6 table)
  s65   : plus the same with the exact g5 table on every 5-subcube"""
import sys, os, time, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gforest
D = os.path.join(HERE, '..', 'data')
def tab(n): return {json.loads(l)['c']: json.loads(l)['g_le'] for l in open(os.path.join(D, 'g%d.jsonl' % n))}
g5, g6 = tab(5), tab(6)
n, c, L = map(int, sys.argv[1:4]); mode = sys.argv[4] if len(sys.argv) > 4 else 'plain'
sub = {'plain': None, 's6': [(6, g6)], 's65': [(6, g6), (5, g5)]}[mode]
t = time.time(); st, sel, r = gforest.search(n, c, L, 99999, levels=1 << (n - 2), sub=sub)
print(n, c, L, mode, st, r, round(time.time() - t, 1), flush=True)
if sel: print(gforest.check_forest(sel, n), json.dumps(sel))
