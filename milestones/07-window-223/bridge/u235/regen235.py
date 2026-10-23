"""Regenerate the generated Lean sources of the 235 bridge from committed data.

usage: python3 -I regen235.py WORK OUTDIR [--check]

For each bridged shape (shapes_done.txt): writes WORK/cuts_<dirs>_r3.json from cuts235.json,
runs gen235.py (shape CNF, CaDiCaL --lidrup session, backward trim, CRup Lean modules), then
gen_table235.py --done (D235Data, D235Tab_*, D235Table, D235Refs, UpperBound235,
UpperBound235Cond).  With --check every written file must match sources.sha256 and every
session its recorded statistics; writes build_order.txt.  Resumable: a shape whose modules
already match their hashes is skipped.
"""
import hashlib, json, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def main():
    work, out = sys.argv[1], sys.argv[2]
    check = '--check' in sys.argv
    os.makedirs(work, exist_ok=True)
    cuts = json.load(open(os.path.join(HERE, 'cuts235.json')))
    done = open(os.path.join(HERE, 'shapes_done.txt')).read().split()
    ref = {}
    if os.path.exists(os.path.join(HERE, 'sources.sha256')):
        for line in open(os.path.join(HERE, 'sources.sha256')):
            h, n = line.split(); ref[n] = h
    order = []
    for s in done:
        key = s.replace(',', '')
        json.dump(cuts[key], open(os.path.join(work, f'cuts_d{key}_r3.json'), 'w'))
        P = 'Q' + key
        gj = os.path.join(work, f'd{key}_r3_sym.gen.json')
        mine = sorted(n for n in ref if re.fullmatch(P + r'(Inputs|S\d+|Tgt\d+|G1|G1C\d+|Chk|W\d+|Ref)\.lean', n))
        if (mine and os.path.exists(gj) and all(os.path.exists(os.path.join(out, n))
                and sha(os.path.join(out, n)) == ref[n] for n in mine)):
            print('up to date', s, flush=True)
        else:
            r = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'gen235.py'), work, out, s],
                               capture_output=True, text=True, check=True)
            print(r.stdout.split('\n')[0][:200], flush=True)
        order += json.load(open(gj))['modules']      # Inputs, S.., Tgt.., G1, G1C.., Ref
    r = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'gen_table235.py'), out, '--done'] + done,
                       capture_output=True, text=True, check=True)
    tabs = [m for m in r.stdout.split('modules:')[1].split('\n')[0].split()]
    hand = ['FastRup', 'FastRupCmd', 'D239Lex', 'D239LexG1', 'FastRupT', 'CRup', 'CRupCmd', 'Sh235G1',
            'Sh235Win', 'Win235Norm', 'Win235Glue']
    tail = ['D235Refs', 'UpperBound235'] if len(done) == 34 else ['UpperBound235Cond']
    full = hand + tabs + order + tail
    open(os.path.join(HERE, 'build_order.txt'), 'w').write('\n'.join(full) + '\n')
    gen = [m for m in full if m not in hand]
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
