#!/usr/bin/env python3
"""The replay step of cert231.py for ONE share or ctx certificate, with the proof search and generator options
exposed (milestone 36, very large certificates; used for `T012301A36264K45`).

    bigreplay435.py --plan P --core COREDIR --work DIR --out GENOUT NAME
                    [--configs LIST] [--seeds 1] [--jobs 3] [--keep-lrat] [--pack-chunk 16384] [--seg 60000]
                    [--lrat-only | --gen-only]

Same steps as `cert231.replay` for a share key (cert233.share_regen, gen_lean_core.core_lrat,
gen_lean_lrat_v3 with --off cert233.offset and --warm cert233.WARM), but
  - the CaDiCaL portfolio is --configs (default: `--unsat`, `--unsat --subsume=0`, `` with seed 1), ONE
    round, --jobs runs in parallel (the big replay of cert231 runs 21 configurations x 5 rounds, one at a
    time on a 15 GB machine);
  - the LRAT is kept (--keep-lrat) so the Lean source can be regenerated with other generator options
    (--pack-chunk: bytes per ProofPack chunk, --seg: hints per segment).
Any UNSAT proof of the core is acceptable: the kernel checks it, and the statement (`refuted`) depends
only on the Cnf part. Writes GENOUT/LocalWindowUnsat/NAME.lean and WORK/NAME.replay.json.
"""
import argparse, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '35-231-lean', 'certify'))
sys.dont_write_bytecode = True
if os.environ.get('PROD435_ADAPTER'):          # interval keys of the 230 route (c230.py): patch the generators first
    import importlib.util
    _sp = importlib.util.spec_from_file_location('prod435_adapter', os.environ['PROD435_ADAPTER'])
    _ad = importlib.util.module_from_spec(_sp)
    _sp.loader.exec_module(_ad)
    _ad.apply()
import cert231  # noqa: E402
C, GC = cert231.C, cert231.GC


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--plan', required=True)
    ap.add_argument('--core', required=True)
    ap.add_argument('--work', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--configs', default='--unsat;--unsat --subsume=0;')
    ap.add_argument('--seeds', type=int, default=1)
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--pack-chunk', type=int, default=16384)
    ap.add_argument('--seg', type=int, default=60000)
    ap.add_argument('--max-lemmas', type=int, default=4000)
    ap.add_argument('--gen-only', action='store_true')
    ap.add_argument('--lrat-only', action='store_true')
    ap.add_argument('--cadical', default='/usr/local/bin/cadical')
    ap.add_argument('--stream', action='store_true', help='low-memory generator genv3stream.py (same output bytes)')
    ap.add_argument('name')
    a = ap.parse_args()
    name, work = a.name, os.path.abspath(a.work)
    certs, jd = os.path.join(work, 'certs'), os.path.join(work, 'json')
    os.makedirs(certs, exist_ok=True)
    m = C.load_meta(a.core, name)
    assert m is not None, 'core JSON needed'
    plain = m.get('kind') in ('k6', 'H')        # a plain seed (cert233.core_plain), e.g. the 230 interval keys
    assert plain or m.get('kind') in ('share', 'ctxshare'), 'plain, share or ctx core JSON needed'
    ctx = m['kind'] == 'ctxshare'
    meta = dict(m)
    rec = {'name': name, 'variables': meta['variables'], 'core': len(meta['core_ids'])}
    if not a.gen_only:
        t0 = time.time()
        if plain:                               # as cert231.replay for a seed: the full CNF, core ids of it
            C.regen_plain(meta, certs)
        else:
            enc, ren, core, tags, used_c = cert231.X.regen(m) if ctx else C.share_regen(m)
            rl = lambda x: (1 if x > 0 else -1) * ren[abs(x)]   # noqa: E731
            gz = os.path.join(certs, name + '.cnf.gz')
            C.write_cnf_gz(len(ren), [[rl(x) for x in c] for c in core], gz)
        C.plain_json(meta, jd)
        GC.PORTFOLIO[:] = [c.split() for c in a.configs.split(';')]
        C.K.TOOLCHAIN_CADICAL = a.cadical
        cad = C.K.cadical_wrapper(work, 20000)     # ulimit -f in MB: full raw LRATs of 100 M+ hints
        rec['regen_s'] = round(time.time() - t0, 1)
        t0 = time.time()
        _, info = GC.core_lrat(name, meta['core_ids'], work, cad, list(range(1, a.seeds + 1)), certs,
                               rounds=1, jobs=a.jobs)
        rec.update(lrat_s=round(time.time() - t0, 1), core_lrat_hints=info['hints'], lemmas=info['lemmas'],
                   producer=info['producer'], portfolio=GC.PORTFOLIO)
        GC.extract_cnf(name, work, certs)
        print(json.dumps(rec), flush=True)
    if a.lrat_only:
        return
    C.plain_json(meta, jd)
    t0 = time.time()
    gen = os.path.join(HERE, 'genv3stream.py') if a.stream else C.V3
    cmd = [sys.executable, gen, '--work', work, '--data', jd, '--out', a.out, '--seg', str(a.seg),
           '--max-lemmas', str(a.max_lemmas), '--pack-chunk', str(a.pack_chunk),
           '--off', str(C.offset(meta['variables'])), '--warm', str(C.WARM), name]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stderr[-3000:], file=sys.stderr)
        raise SystemExit('generation failed')
    g = json.loads(r.stdout.strip().splitlines()[-1])
    if ctx:                                     # as cert231.replay: the ctx replay imports LocalWindowCtxCnf.NAME
        p = os.path.join(a.out, 'LocalWindowUnsat', name + '.lean')
        src = open(p).read()
        assert src.count('import LocalWindowCnf.' + name) == 1
        q = os.path.join(a.out, 'LocalWindowCtxUnsat', name + '.lean')
        os.makedirs(os.path.dirname(q), exist_ok=True)
        open(q, 'w').write(src.replace('import LocalWindowCnf.' + name, 'import LocalWindowCtxCnf.' + name))
        os.remove(p)
    g['gen_s'] = round(time.time() - t0, 1)
    rec.update(g)
    json.dump(rec, open(os.path.join(work, name + '.replay.json'), 'w'))
    print(json.dumps(rec), flush=True)


if __name__ == '__main__':
    main()
