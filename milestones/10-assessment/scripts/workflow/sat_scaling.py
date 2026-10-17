"""SAT-time scaling of the repo's regrowth necessary-condition CNF vs freed vertices.
Usage: python sat_scaling.py ENTRY REV KEEP TIMEOUT
Prints one JSON line. Uses a scratch copy of work/build_regrowth_cnf.py (unchanged)."""
import sys, json, time, threading
sys.path.insert(0, '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf')
from regrowth_cnf_copy import encode
from pysat.solvers import Solver

entry, rev, keep, timeout = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
solver_name = sys.argv[5] if len(sys.argv) > 5 else 'cadical195'
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
path = bank[entry]['vertex_sequence']
if rev:
    path = path[::-1]
t0 = time.time()
data = encode(path, keep=keep, total_vertices=193)
tenc = time.time() - t0
s = Solver(name=solver_name, bootstrap_with=data['clauses'], use_timer=True)
timer = threading.Timer(timeout, lambda: s.interrupt())
timer.start()
t0 = time.time()
res = s.solve_limited(expect_interrupt=True)
el = time.time() - t0
timer.cancel()
status = {True: 'SAT', False: 'UNSAT', None: 'UNKNOWN'}[res]
extra = {}
if res:
    model = set(l for l in s.get_model() if l > 0)
    sel = [v for v, i in data['selected'].items() if i in model]
    extra['selected'] = len(sel)
st = s.accum_stats()
print(json.dumps(dict(entry=entry, rev=rev, keep=keep, freed=193 - keep, solver=solver_name,
                      status=status, seconds=round(el, 3), encode_s=round(tenc, 2),
                      vars=data['variables'], clauses=len(data['clauses']),
                      region=len(data['vertices']), conflicts=st.get('conflicts'),
                      decisions=st.get('decisions'), **extra)), flush=True)
