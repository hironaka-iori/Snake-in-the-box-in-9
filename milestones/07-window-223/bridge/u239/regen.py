"""Regenerate the Lean sources of the unconditional 239 bound from committed certificate data.

For each of the 145 certified direction windows listed in `cases.json`:
  * `reuse` (10): the CNF is identical (sha256) to one refuted for the 241 bound; nothing to do;
  * `trim` (80): decompress the committed CNF and DRUP proof from
    `milestones/10-window-aggregate/certificates/direction/`, check both sha256 against
    `cases.json`, trim with `drat-trim -L` and check the sha256 of the LRAT;
  * `sym` (55): decompress and check the committed CNF, add lex-leader clauses and re-solve with
    CaDiCaL 1.9.5 (PySAT), trim, and check the sha256 of the symmetry-broken CNF and of the LRAT.
Then `gen.py` writes the step/input/G1 modules, `gen_table.py` D239Table.lean and `gen_refs.py`
D239Refs.lean and UpperBound239.lean, and every written file is compared with `sources.sha256`.

usage: python3 -I regen.py WORK OUTDIR [--jobs N] [--only TAG...] [--keep]
  WORK: scratch directory (needs about 1.5 GB while running; LRAT files are deleted after use
        unless --keep); OUTDIR: where the .lean files go (normally work/spectral/stronger; the
        generated `DV*.lean` files there are git-ignored, about 0.9 GB).
Hash mismatches are fatal: the sources would still be checked by the kernel, but they would not
be the ones the published build and manifest refer to.
"""
import argparse, gzip, hashlib, json, os, shutil, subprocess, sys
from concurrent.futures import ProcessPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..'))
CERTS = os.path.join(REPO, 'milestones', '10-window-aggregate', 'certificates', 'direction')
DT = os.environ.get('DRAT_TRIM', os.path.join(REPO, 'milestones', '10-window-aggregate', '.build', 'drat-trim'))


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def unzip(src, dst):
    with gzip.open(src) as i, open(dst, 'wb') as o:
        shutil.copyfileobj(i, o, 1 << 20)


def prepare(args):
    """Produce WORK/data/TAG.lrat (trim) or WORK/sym/TAG.lrat (sym); returns a log line."""
    work, c = args
    t = c['tag']
    d = f'{work}/data'
    unzip(f'{CERTS}/{t}.cnf.gz', f'{d}/{t}.cnf')
    assert sha(f'{d}/{t}.cnf') == c['cnf_sha256'], f'{t}: committed CNF differs from cases.json'
    if c['kind'] == 'trim':
        unzip(f'{CERTS}/{t}.drup.gz', f'{d}/{t}.drup')
        assert sha(f'{d}/{t}.drup') == c['drup_sha256'], f'{t}: committed DRUP differs from cases.json'
        r = subprocess.run(['nice', '-n', '10', DT, f'{d}/{t}.cnf', f'{d}/{t}.drup', '-L', f'{d}/{t}.lrat',
                            '-t', '20000'], stdin=subprocess.DEVNULL, capture_output=True, text=True)
        os.remove(f'{d}/{t}.drup')
        assert 's VERIFIED' in r.stdout, f'{t}: drat-trim failed'
        got = sha(f'{d}/{t}.lrat')
    else:
        sys.path.insert(0, HERE)
        import symsolve
        symsolve.run(t, work, c)
        assert sha(f'{work}/sym/{t}.cnf') == c['sym_cnf_sha256'], f'{t}: symmetry-broken CNF differs'
        got = sha(f'{work}/sym/{t}.lrat')
    assert got == c['lrat_sha256'], f'{t}: LRAT sha256 {got} differs from cases.json'
    return f'{t} {c["kind"]} ok'


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('work'); ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=1)
    ap.add_argument('--only', nargs='*', default=None)
    ap.add_argument('--keep', action='store_true')
    a = ap.parse_args()
    work, out = os.path.abspath(a.work), os.path.abspath(a.out)
    for s in ('data', 'sym'):
        os.makedirs(f'{work}/{s}', exist_ok=True)
    os.makedirs(out, exist_ok=True)
    cases = json.load(open(os.path.join(HERE, 'cases.json')))
    todo = [c for c in cases if c['kind'] != 'reuse' and (a.only is None or c['tag'] in a.only)]
    sys.path.insert(0, HERE)
    import gen
    gen.DATA, gen.SYM = f'{work}/data', f'{work}/sym'
    expected = dict(reversed(l.split()) for l in open(os.path.join(HERE, 'sources.sha256')))
    written = []
    with ProcessPoolExecutor(max_workers=max(1, a.jobs)) as pool:
        for c, msg in zip(todo, pool.map(prepare, [(work, c) for c in todo])):
            print(msg, flush=True)
            files = gen.run(c['tag'], out)
            written += files
            if not a.keep:
                for p in (f'{work}/data/{c["tag"]}.lrat', f'{work}/sym/{c["tag"]}.lrat',
                          f'{work}/sym/{c["tag"]}.cnf'):
                    if os.path.exists(p): os.remove(p)
    if a.only is None:
        import gen_table, gen_refs
        gen_table.write(out)
        gen_refs.write(out)
        written += ['D239Table', 'D239Refs', 'UpperBound239']
    bad = [m for m in written if expected.get(m + '.lean') != sha(f'{out}/{m}.lean')]
    print(f'{len(written)} modules written, {len(written) - len(bad)} match sources.sha256', flush=True)
    if bad:
        raise SystemExit('sha256 mismatch: ' + ' '.join(bad[:20]))


if __name__ == '__main__':
    main()
