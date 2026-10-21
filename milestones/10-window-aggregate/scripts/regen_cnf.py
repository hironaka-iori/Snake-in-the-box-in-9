"""Regenerate the CNF of a count-free shape certificate and print its sha256.
  python regen_cnf.py --dirs 0 1 2 0 3 1 0 --X 20 --cuts shapes6_X20.jsonl.cuts.json [--out f.cnf]
The CNF is ShareEncoding(window_from_dirs(dirs), alpha=[(0,21)]*k, radius=3, bound=X,
counter='stot', exact=True) followed by the recorded cycle cuts in their recorded order."""
import argparse, hashlib, json, os, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from share_enc import ShareEncoding, window_from_dirs
from wincert import write_cnf

ap = argparse.ArgumentParser()
ap.add_argument('--dirs', type=int, nargs='+', required=True)
ap.add_argument('--X', type=int, required=True)
ap.add_argument('--cuts', required=True)
ap.add_argument('--out')
a = ap.parse_args()
k = len(a.dirs) - 1
enc = ShareEncoding(window_from_dirs(a.dirs), [(0, 21)] * k, 3, a.X, counter='stot', exact=True)
for c in json.load(open(a.cuts))[','.join(map(str, a.dirs))]:
    enc.add_cycle_cut(c)
out = a.out or tempfile.mktemp(suffix='.cnf')
write_cnf(enc, out)
print(hashlib.sha256(open(out, 'rb').read()).hexdigest(), out)
