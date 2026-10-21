"""Own plain solve of every key of a set whose UNSAT status was only derived (member of a
range certificate of k6_w3_loop, or contained in a non-lumped UNSAT key): such a key needs
its own certificate.  Calls are logged in oracle_full.jsonl (k6loop record format).

usage: nice -n 19 python verify.py KEYS.json
"""
import sys, json
sys.dont_write_bytecode = True
import fp, prune as PR

S = fp.Status()
ks = [PR.lumped_of(d, a) for d, a in json.load(open(sys.argv[1]))['keys']]
todo = [k for k in ks if S.src.get(k) in ('range', 'derived')]
res = {}
for k in todo:
    ds, syms = k
    key = fp.rkey(ds, tuple(fp.LUMP[s] for s in syms))
    enc = fp.K6.ws.from_key(key)
    st, sel, cuts, sec = fp.K6.ws.solve(enc, 120)
    rec = dict(dirs=list(key[0]), alpha=[list(a) for a in key[1]], kind='plain',
               k=len(syms), result=st, witness=None, cuts=cuts, seconds=round(sec, 2), nv=enc.nv,
               ncl=len(enc.clauses), src='verify')
    with open(fp.ORACLE, 'a') as f:
        f.write(json.dumps(rec) + '\n')
    res[st] = res.get(st, 0) + 1
    assert st == 'UNSAT', (k, st)
print(json.dumps(dict(checked=len(todo), results=res)))
