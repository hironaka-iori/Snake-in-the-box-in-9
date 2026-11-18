#!/usr/bin/env python3
"""The 4.19 sources of the K7R34C7W16 chain (relaxed-keller line, milestone 10) for the 230 port.

    k7src.py --out DIR

Fetches branch claude/relaxed-keller-60ks7i BY NAME (depth 1, into refs/remotes/origin/relaxed-keller),
extracts the 185 files of lean435/c230/k7-src.sha256 from work/spectral/stronger and checks each sha256.
The other modules of the chain's import closure are byte-identical to this branch's work/spectral/stronger
files (checked when the list was made) and come from there through port.py's normal roots.
"""
import argparse, hashlib, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
BRANCH = 'claude/relaxed-keller-60ks7i'
REF = 'refs/remotes/origin/relaxed-keller'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--no-fetch', action='store_true')
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    want = [l.split() for l in open(os.path.join(ROOT, 'lean435', 'c230', 'k7-src.sha256')) if l.strip()]
    if not a.no_fetch:
        subprocess.run(['git', 'fetch', '--depth=1', 'origin', f'refs/heads/{BRANCH}:{REF}'], cwd=ROOT, check=True)
    bad = 0
    for h, f in want:
        p = os.path.join(a.out, f)
        if not (os.path.exists(p) and hashlib.sha256(open(p, 'rb').read()).hexdigest() == h):
            data = subprocess.run(['git', 'show', f'{REF}:work/spectral/stronger/{f}'], cwd=ROOT, check=True,
                                  capture_output=True).stdout
            open(p, 'wb').write(data)
        if hashlib.sha256(open(p, 'rb').read()).hexdigest() != h:
            print('sha256 mismatch', f)
            bad += 1
    if bad:
        raise SystemExit(f'{bad} files differ from lean435/c230/k7-src.sha256')
    print(f'{len(want)} K7 chain sources in {a.out}, sha256 checked')


if __name__ == '__main__':
    main()
