"""LRAT samples of the most expensive (by current estimate) non-reused keys of a set.
usage: nice -n 19 python sample_top.py KEYS.json N"""
import sys, json, numpy as np
sys.dont_write_bytecode = True
import samples, prune as PR, fp, proofs
ks = [PR.lumped_of(d, a) for d, a in json.load(open(sys.argv[1]))['keys']]
c, h, cert = PR.load_costs(ks, True)
for i in np.argsort(-c)[:int(sys.argv[2])]:
    if h[i] in ('reuse', 'measured'):
        continue
    ds, syms = ks[i]
    proofs.measure(fp.rkey(ds, tuple(fp.LUMP[s] for s in syms)))
