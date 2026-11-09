"""LRAT size of share-threshold certificates at the low levels this run uses (cost model of stage D).

Picks UNSAT threshold records of this run spread over solve times, rebuilds the static CNF with
its lazy cycle cuts (wincert_share.from_key + solve), and measures it with
wincert_share.measure_proof (CaDiCaL --lrat, trimmed to the empty clause's cone; every proof file
is deleted right after measuring; per-file cap FSIZE_KB).  Appends to data/share_samples.jsonl.
usage: share_samples.py N
"""
import sys, os, json, glob, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
import wincert_share as ws

OUT = os.path.join(HERE, 'data', 'share_samples.jsonl')
WORK = os.path.join(C.SCR, 'proof')


def main():
    n = int(sys.argv[1])
    recs = []
    for f in sorted(glob.glob(os.path.join(HERE, 'data', 'oracle_share*.jsonl'))):
        for l in open(f):
            r = json.loads(l)
            if r['kind'] == 'thr' and r['result'] == 'UNSAT' and r['seconds'] <= 60:
                recs.append(r)
    recs.sort(key=lambda r: r['seconds'])
    pick = [recs[int(i * (len(recs) - 1) / max(1, n - 1))] for i in range(n)]
    ws.FSIZE_KB = 90 * 1024
    for r in pick:
        if C.disk_mb() < 450:
            print('disk low, stop'); break
        k = (tuple(r['dirs']), tuple(tuple(a) for a in r['alpha']))
        enc = ws.from_key(k, M=12, cap=r['T'] - 1)
        st, sel, cuts, sec = ws.solve(enc, 120)
        if st != 'UNSAT':
            continue
        t = time.time()
        m = ws.measure_proof(enc, WORK, timeout=900)
        m.update(dirs=r['dirs'], alpha=r['alpha'], T=r['T'], solve_seconds=r['seconds'], resolve=round(sec, 2),
                 wall=round(time.time() - t, 1))
        print(json.dumps({x: m.get(x) for x in ('T', 'solve_seconds', 'lrat_hints', 'core_clauses', 'failed', 'timeout')}), flush=True)
        with open(OUT, 'a') as f:
            f.write(json.dumps(m) + '\n')


if __name__ == '__main__':
    main()
