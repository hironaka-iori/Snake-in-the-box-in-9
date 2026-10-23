"""Regenerate the generated Lean sources of the 234 share bridge from committed data.

usage: python3 -I regen234.py WORK OUTDIR [--cond UpperBound235Cond.lean] [--uncond NAME] [--check]

For each of the 34 shapes of data/share/final_a_X20.jsonl: gen234.py (share CNF, sha256 checked
against the certificate, CaDiCaL --lrat, backward trim, CRup and G1 modules; the trimmed proof is
deleted afterwards); then gen_final234.py (ShareRefs234, UpperBound234Cond and, with --uncond,
UpperBound234).  With --check every written file must match sources.sha256, else sources.sha256 is
written.  Writes build_order.txt (hand-written modules first).  Resumable: a shape whose modules
already match sources.sha256 is skipped.
"""
import hashlib, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
HAND = ['CRup', 'CRupCmd', 'ShareG1', 'ShareWin', 'ShareNorm', 'AggregateDirectionK6R3WShare234']


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def main():
    args = sys.argv[1:]
    check = '--check' in args
    fin = []
    for opt in ('--cond', '--uncond'):
        if opt in args:
            i = args.index(opt); fin += [opt, args[i + 1]]; del args[i:i + 2]
    work, out = args[0], args[1]
    os.makedirs(work, exist_ok=True)
    ref = {}
    if os.path.exists(os.path.join(HERE, 'sources.sha256')):
        for line in open(os.path.join(HERE, 'sources.sha256')):
            h, n = line.split(); ref[n] = h
    shapes = [json.loads(l)['dirs'] for l in open(os.path.join(REPO, 'milestones', '10-window-aggregate',
                                                                  'data', 'share', 'final_a_X20.jsonl'))]
    order = []
    for d in shapes:
        s = ','.join(map(str, d))
        P = 'V' + ''.join(map(str, d))
        gj = os.path.join(work, f'd{"".join(map(str, d))}_share20.gen.json')
        mine = sorted(n for n in ref if re.fullmatch(P + r'(Inputs|S\d+|Main|G1|G1C\d+|Ref)\.lean', n))
        if (mine and os.path.exists(gj) and all(os.path.exists(os.path.join(out, n))
                and sha(os.path.join(out, n)) == ref[n] for n in mine)):
            print('up to date', s, flush=True)
        else:
            r = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'gen234.py'), work, out, s],
                               capture_output=True, text=True, check=True)
            print(r.stdout.split('\n')[0][:200], flush=True)
            for ext in ('.trim', '.cnf'):
                p = gj.replace('.gen.json', ext)
                if os.path.exists(p):
                    os.remove(p)
        order += json.load(open(gj))['modules']
    subprocess.run([sys.executable, '-I', os.path.join(HERE, 'gen_final234.py'), out] + fin, check=True)
    tail = ['ShareRefs234', 'UpperBound234Cond'] + (['UpperBound234'] if '--uncond' in fin else [])
    full = HAND + order + tail
    open(os.path.join(HERE, 'build_order.txt'), 'w').write('\n'.join(full) + '\n')
    gen = order + tail
    if check:
        bad = [m for m in gen if ref.get(m + '.lean') != sha(os.path.join(out, m + '.lean'))]
        if bad:
            raise SystemExit(f'{len(bad)} generated sources differ from sources.sha256, e.g. {bad[:3]}')
        print('all', len(gen), 'generated sources match sources.sha256')
    else:
        with open(os.path.join(HERE, 'sources.sha256'), 'w') as f:
            for m in gen:
                f.write(f'{sha(os.path.join(out, m + ".lean"))}  {m}.lean\n')
        print('wrote sources.sha256 for', len(gen), 'generated sources')


if __name__ == '__main__':
    main()
