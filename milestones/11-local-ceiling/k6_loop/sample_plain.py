"""LRAT samples of the kept plain exclusions of minimal_A_t235.json (10 six-centre, 14 five-centre)."""
import sys, os, json, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proofs
d = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'minimal_A_t235.json')))
random.seed(7)
ks = [(tuple(k[0]), tuple(tuple(a) for a in k[1])) for k in d['keys']]
for c, n in ((6, 10), (5, 14)):
    for k in random.sample([k for k in ks if len(k[1]) == c], n):
        proofs.measure(k)
