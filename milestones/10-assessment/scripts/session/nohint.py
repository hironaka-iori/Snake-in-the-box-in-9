import json, sys
from fiber_cp import solve, verify
from bank_words import decompose
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
i = int(sys.argv[1]); target = int(sys.argv[2]) if len(sys.argv) > 2 else None
word, segs, n = decompose(bank[i])
r = solve(word, seconds=float(sys.argv[3]) if len(sys.argv) > 3 else 300, workers=1, target=target)
print(i, 'outer len', len(word), 'target', target, {k: v for k, v in r.items() if k != 'path'}, 'path_len', len(r.get('path', [])), 'verified', verify(r['path']) if 'path' in r else None, flush=True)
