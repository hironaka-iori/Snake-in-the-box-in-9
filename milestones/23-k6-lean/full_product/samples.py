"""LRAT samples (trimmed CaDiCaL 2.1.3 hints) of keys of a pruned set, to calibrate costs.json.

Uses ../../11-local-ceiling/k6_loop/proofs.py `measure` (lazy-cut solve, cold `cadical --lrat`,
count the hints the empty clause depends on, delete CNF and proof at once), with the proof
file capped at 100 MB and the scratch files in the k6full scratch directory.  One line per
sample in samples.jsonl.  Keys are stratified by centre count and by their own solve time.

usage: nice -n 19 python samples.py KEYS.json N [seed]
"""
import sys, os, json, random
sys.dont_write_bytecode = True
import fp
import proofs
import prune as PR

proofs.OUT = os.path.join(fp.HERE, 'samples.jsonl')
proofs.CAP_KB = 100 * 1024
fp.K6.SCR = fp.SCR


def main():
    ks = [PR.lumped_of(d, a) for d, a in json.load(open(sys.argv[1]))['keys']]
    n = int(sys.argv[2]); random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 11)
    cert = PR.certified(); sec = PR.seconds_map()
    done = set()
    if os.path.exists(proofs.OUT):
        done = {PR.lumped_of(r['dirs'], r['alpha']) for r in map(json.loads, open(proofs.OUT))}
    pool = [k for k in ks if k not in cert and k not in done]
    # strata: centre count x solve-time tercile (unknown time = own stratum)
    strata = {}
    for k in pool:
        s = sec.get(k)
        b = 'u' if s is None else (0 if s < 0.1 else 1 if s < 0.5 else 2)
        strata.setdefault((len(k[1]), b), []).append(k)
    tot = sum(len(v) for v in strata.values())
    pick = []
    for st, v in sorted(strata.items(), key=lambda x: str(x[0])):
        m = max(1, round(n * len(v) / tot))
        pick += random.sample(v, min(m, len(v)))
    print({str(k): len(v) for k, v in strata.items()}, len(pick), flush=True)
    for k in pick:
        ds, syms = k
        proofs.measure(fp.rkey(ds, tuple(fp.LUMP[s] for s in syms)))


if __name__ == '__main__':
    main()
