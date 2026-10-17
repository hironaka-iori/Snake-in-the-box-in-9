import json, sys
from fiber_cp import solve, verify
from bank_words import decompose
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
for i in [0, 30, 60]:
    word, segs, n = decompose(bank[i])
    r = solve(word, seconds=float(sys.argv[1]), workers=4, hint=segs)
    ok = verify(r['path']) if 'path' in r else None
    print(i, 'outer len', len(word), 'bank vertices', n, '->', {k: v for k, v in r.items() if k != 'path'}, 'path_len', len(r.get('path', [])), 'verified', ok, flush=True)
