"""Six-window threshold tests and LRAT samples on the lowest plain-SAT live 6-keys (the keys a
threshold phase of the loop would test next).  For each of N keys: ladder at ceil10(W6 + GAP), +10, ...
(k6w3loop.ladder, symmetry breaking on); every UNSAT is re-solved cold with
CaDiCaL --lrat, trimmed, measured and deleted (data/proof_samples.jsonl).
usage: thrsample.py N [GAP] [TL]"""
import sys, os, math
ME = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, ME)
import k6w3loop as L
from k6w3loop import *

N = int(sys.argv[1]); GAP = int(sys.argv[2]) if len(sys.argv) > 2 else 12
TL = float(sys.argv[3]) if len(sys.argv) > 3 else 120
G, P, O, sub = setup(); Tb = Tables(G, sub)
r = evaluate(G, P, O, Tb)
W6 = r['W6']
ks = np.unique(G['K6'][r['idx']])
cand = [j for j in ks[np.argsort(W6[ks], kind='stable')] if P.st.get(G['keys6'][j]) == 'SAT'][:N]
for j in cand:
    k = G['keys6'][j]
    T0 = 10 * math.ceil((int(W6[j]) + GAP) / 10)
    res = ladder(k, [T0, T0 + 20], TL, O, sample=1)     # every UNSAT is measured (with its cycle cuts)
    print(keystr(k), 'W6', int(W6[j]), res, flush=True)
