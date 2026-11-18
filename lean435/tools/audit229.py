#!/usr/bin/env python3
"""Conditional audit of the parametrised K7 count (milestone 38, lean435/c229/C229Final.lean).

    audit229.py --spec-src S [--spec-src ...] --spec-build B [--spec-build ...] --work W

The spec layer is the one of c230chain.sh (core stack, ported K7 chain, C230*) plus C229Final, built with
build.py.  As `assemble230.py --conditional`: no glue and no certificate interface; `audit.py final`
compiles a file that imports C229Final from a clean directory (public .olean only, --setup, strace) and
checks that the axioms of the conditional theorems are within [propext, Classical.choice, Quot.sound].
The theorems keep their two certificate premises (`AllTab tab230`, `AllShareK K shares230`): nothing here
proves a bound.
"""
import argparse, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
THEOREMS = ['Snake9.upper_229_of_refutedK7', 'Snake9.upper_of_refutedK7_share', 'Snake9.upper_228_of_refutedK7',
            'Snake9.upper_227_of_refutedK7', "Snake9.upper_230_of_refutedK7'", 'Snake9.C230.upper_of_tables_shareK',
            'Snake9.C230.window_shareK']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec-src', action='append', required=True)
    ap.add_argument('--spec-build', action='append', required=True)
    ap.add_argument('--work', required=True)
    a = ap.parse_args()
    w = os.path.abspath(a.work)
    os.makedirs(os.path.join(w, 'iface'), exist_ok=True)
    man = os.path.join(w, 'empty-manifest.jsonl')
    open(man, 'w').close()
    fin = os.path.join(w, 'Conditional229_435.lean')
    open(fin, 'w').write('\n'.join(
        ['module', '', 'public import C229Final', '',
         '/-! The conditional theorems of milestone 38 with their two certificate premises (audit229.py). -/', ''] +
        [f'#check @{t}' for t in THEOREMS] + [f'#print axioms {t}' for t in THEOREMS] + ['']))
    cmd = [sys.executable, os.path.join(HERE, 'audit.py'), 'final']
    for s, b in zip(a.spec_src, a.spec_build):
        cmd += ['--src', os.path.abspath(s), '--spec-build', os.path.abspath(b)]
    cmd += ['--iface', os.path.join(w, 'iface'), '--manifest', man, '--final', fin,
            '--module-name', 'Conditional229_435', '--work', os.path.join(w, 'w')]
    for t in THEOREMS:
        cmd += ['--theorem', t]
    r = subprocess.run(cmd, capture_output=True, text=True)
    txt = r.stdout + r.stderr
    print(txt)
    open(os.path.join(w, 'conditional-audit.txt'), 'w').write(txt)
    sys.exit(r.returncode)


if __name__ == '__main__':
    main()
