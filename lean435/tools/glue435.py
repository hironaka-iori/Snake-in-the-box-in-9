#!/usr/bin/env python3
"""Glue modules of the 4.35 assembly (milestone 36): from the per-certificate public theorems
`Snake9.LocalWindow.<N>.refuted` to the certificate premises of the chain `upper_<B>_of_refuted6SC<T>`.

    glue435.py --tag T --gen GENDIR --plan P --freederive F --out OUTDIR [--names-only]

GENDIR holds the generated (4.19 form) chain sources of gen_lean_automaton6sc.py; the key lists are read
from `LocalWindowDirKeys6SC<T>[P<g>]` there. For every chunk of the chain's key lists one module is written:

  Glue6SC<T>D<c>    AllRefutedList dirChunk6S<T>_<c>       (plain k6 keys)
  Glue6SC<T>H8      AllRefutedList h8Keys6S<T>
  Glue6SC<T>S<i>    AllRefutedShareList shareChunk6S<T>_<i>
  Glue6SC<T>C7_<i>  AllP RefutedCtx7 ctx7Chunk6SC<T>_<i>   (and C8_<i>)
  Glue6SC<T>        allRefuted6S<T>, allRefutedShare6S<T>, allRefutedCtx6SC<T> (Glue435 lemmas)

Each chunk module imports the certificate modules of its keys PRIVATELY (only their public interface
is needed) and states its chunk publicly. A key's term:
  paid plain key / free key certified itself    `<N>.refuted`                       (LocalWindowCert.<N>)
  free key = a 233 seed with widened bounds      `Families.refuted_key_of_wide <seed>.refuted (by decide +kernel)`
  free key derived by L1 / L2 from a 233 seed    `Families.refuted_key_of_wide …` / `Families.refuted_key_sub (mkPerm v) s …`
                                                 (cert233.proof_term's two forms; table freederive_<plan>.json.gz)
  share key                                      `<T…>.refuted`                       (5-window, cap K)
  ctx key                                        `<C…>.refuted`                       (LocalWindowCtxCert.<N>)
It writes OUTDIR/glue-needs.json: per glue module, the certificate modules it imports.
"""
import argparse, gzip, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.dont_write_bytecode = True
for d in ('milestones/33-233-lean/certify', 'milestones/35-231-lean/scripts', 'milestones/35-231-lean/certify'):
    sys.path.insert(0, os.path.join(ROOT, d))

LIT = re.compile(r'\(\[([\d, ]*)\], \[([\d, ]*)\](?:, (\d+))?\)')


def lists(path):
    """{def name: [tuples]} of the literal key lists of a generated keys module."""
    s = open(path, encoding='utf-8').read()
    out = {}
    for m in re.finditer(r'^noncomputable def (\w+) : List \(List Nat × List Nat(?: × Nat)?\) := \[(.*?)\]\n\n',
                         s, re.M | re.S):
        body = m.group(2)
        items = []
        for t in LIT.finditer(body):
            ds = tuple(int(x) for x in t.group(1).split(',') if x.strip())
            sy = tuple(int(x) for x in t.group(2).split(',') if x.strip())
            items.append((ds, sy) if t.group(3) is None else (ds, sy, int(t.group(3))))
        out[m.group(1)] = items
    return out


def lst(x):
    return '[' + ', '.join(str(int(v)) for v in x) + ']'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tag', required=True)
    ap.add_argument('--gen', required=True)
    ap.add_argument('--plan', required=True)
    ap.add_argument('--freederive', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--chunks', default=None, help='only these chunk modules (e.g. D0,S3) - tests')
    a = ap.parse_args()
    import cert233 as C
    import ctxcert as X
    import gen_lean_automaton6sc as GEN
    import families_k7 as FK
    T = a.tag
    P = GEN.load_plan(a.plan)
    rows = {(tuple(r['key'][0]), tuple(r['key'][1])): r for r in P['plain_rows']}
    der = {}
    for k, v in json.load(gzip.open(a.freederive, 'rt')).items():
        d, s = k.split('|')
        der[(tuple(int(x) for x in d.split()), tuple(int(x) for x in s.split()))] = v
    pl233 = C.load_plan(C.PLAN)

    def plain_term(k):
        r = rows.get(k)
        if r is None or not r['free'] or k in P['h8']:
            if r is not None and r['free'] and k not in P['h8']:
                raise SystemExit(f'free key without derivation {k}')
            n = C.pname(k)                         # certified itself (paid, or an H8 cut)
            return f'{n}.refuted', n
        e = der[k]
        if e[0] == 'self':
            n = C.pname(k)
            return f'{n}.refuted', n
        if e[0] == 'seed':
            n = C.pname(k)
            wide = pl233[k][1]
            if [tuple(x) for x in wide] == [tuple(x) for x in C.GC.dir_bounds(k[1])]:
                return f'{n}.refuted', n
            return f'Families.refuted_key_of_wide {n}.refuted (by decide +kernel)', n
        _, seed, meth, v, s = e
        sk = (tuple(seed[0]), tuple(seed[1]))
        n = C.pname(sk)
        if meth == 'L1':
            return f'Families.refuted_key_of_wide {n}.refuted (by decide +kernel)', n
        return f'Families.refuted_key_sub (mkPerm {lst(v)}) {s} {n}.refuted (by decide +kernel)', n

    gen = a.gen
    parts = sorted(f for f in os.listdir(gen) if re.fullmatch(rf'LocalWindowDirKeys6SC{T}P\d+\.lean', f))
    where, lit = {}, {}
    for f in parts + [f'LocalWindowDirKeys6SC{T}.lean']:
        for nm, items in lists(os.path.join(gen, f)).items():
            where[nm] = f[:-5]
            lit[nm] = items
    os.makedirs(a.out, exist_ok=True)
    needs = {}
    mods = []

    def emit(mod, defname, pred, terms, certs, extra=()):
        # the keys module imports every part and the chain's predicates
        imps = [f'public import LocalWindowDirKeys6SC{T}'] + [f'import {x}' for x in extra] + \
               [f'import {c}' for c in sorted(set(certs))]
        body = ',\n    '.join(terms + ['trivial'])
        txt = '\n'.join(['module', ''] + imps + [
            '', f'/-! Glue chunk `{defname}` of the chain `{T}` (lean435/tools/glue435.py). -/', '',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
            'namespace Snake9.LocalWindow', 'open Snake9.DirectionWindow6S Snake9.DirectionWindow6SC', '',
            f'public theorem glue_{defname} : {pred} {defname} :=', f'  ⟨{body}⟩', '',
            'end Snake9.LocalWindow', ''])
        open(os.path.join(a.out, mod + '.lean'), 'w').write(txt)
        needs[mod] = sorted(set(certs))
        mods.append((mod, defname))

    want = set(a.chunks.split(',')) if a.chunks else None
    dchunks = sorted((nm for nm in lit if re.fullmatch(rf'dirChunk6S{T}_\d+', nm)), key=lambda x: int(x.rsplit('_', 1)[1]))
    for nm in dchunks:
        c = nm.rsplit('_', 1)[1]
        if want and f'D{c}' not in want:
            continue
        tc = [plain_term(k) for k in lit[nm]]
        fam = any('Families' in t for t, _ in tc)
        emit(f'Glue6SC{T}D{c}', nm, 'AllRefutedList', [t for t, _ in tc],
             ['LocalWindowCert.' + n for _, n in tc], ('LocalWindowFamilies',) if fam else ())
    if not want or 'H8' in want:
        nm = f'h8Keys6S{T}'
        names = [C.pname(k) for k in lit[nm]]
        emit(f'Glue6SC{T}H8', nm, 'AllRefutedList', [f'{n}.refuted' for n in names],
             ['LocalWindowCert.' + n for n in names])
    for nm in sorted((x for x in lit if re.fullmatch(rf'shareChunk6S{T}_\d+', x)), key=lambda x: int(x.rsplit('_', 1)[1])):
        i = nm.rsplit('_', 1)[1]
        if want and f'S{i}' not in want:
            continue
        names = [C.sname(k) for k in lit[nm]]
        emit(f'Glue6SC{T}S{i}', nm, 'AllRefutedShareList', [f'{n}.refuted' for n in names],
             ['LocalWindowCert.' + n for n in names])
    for n in (7, 8):
        for nm in sorted((x for x in lit if re.fullmatch(rf'ctx{n}Chunk6SC{T}_\d+', x)),
                         key=lambda x: int(x.rsplit('_', 1)[1])):
            i = nm.rsplit('_', 1)[1]
            if want and f'C{n}_{i}' not in want:
                continue
            names = [X.name_of(n, k[0], k[1], k[2]) for k in lit[nm]]
            emit(f'Glue6SC{T}C{n}_{i}', nm, f'AllP RefutedCtx{n}', [f'{x}.refuted' for x in names],
                 ['LocalWindowCtxCert.' + x for x in names])
    if not want:
        # the top module: chunk lists -> the three premises of the chain
        def allp(pred, chunks, pfx):
            return '⟨' + ', '.join([f'glue_{c}' for c in chunks] + ['trivial']) + '⟩'
        sch = sorted((x for x in lit if re.fullmatch(rf'shareChunk6S{T}_\d+', x)), key=lambda x: int(x.rsplit('_', 1)[1]))
        c7 = sorted((x for x in lit if re.fullmatch(rf'ctx7Chunk6SC{T}_\d+', x)), key=lambda x: int(x.rsplit('_', 1)[1]))
        c8 = sorted((x for x in lit if re.fullmatch(rf'ctx8Chunk6SC{T}_\d+', x)), key=lambda x: int(x.rsplit('_', 1)[1]))
        top = ['module', '', f'public import LocalWindowDirKeys6SC{T}', 'import Glue435'] + \
              [f'import {m}' for m, _ in mods] + [
            '', f'/-! The certificate premises of the chain `{T}` from the glue chunks (lean435/tools/glue435.py). -/', '',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
            'namespace Snake9.LocalWindow', 'open Snake9.DirectionWindow6S Snake9.DirectionWindow6SC Snake9.Glue435', '',
            f'public theorem allRefuted6S{T} : AllRefuted6S{T} :=',
            f'  ⟨allRefutedList_flatten {allp(0, dchunks, "")}, glue_h8Keys6S{T}⟩', '',
            f'public theorem allRefutedShare6S{T} : AllRefutedShare6S{T} :=',
            f'  allRefutedShareList_flatten {allp(0, sch, "")}', '',
            f'public theorem allRefutedCtx6SC{T} : AllRefutedCtx6SC{T} :=',
            f'  ⟨allP_flatten {allp(0, c7, "")}, allP_flatten {allp(0, c8, "")}⟩', '',
            'end Snake9.LocalWindow', '']
        open(os.path.join(a.out, f'Glue6SC{T}.lean'), 'w').write('\n'.join(top))
    import shutil
    shutil.copyfile(os.path.join(ROOT, 'lean435', 'glue', 'Glue435.lean'), os.path.join(a.out, 'Glue435.lean'))
    json.dump(needs, open(os.path.join(a.out, 'glue-needs.json'), 'w'), indent=0)
    allc = sorted({c for v in needs.values() for c in v})
    print(f'{len(mods)} glue chunk modules' + ('' if want else ' + the top module') +
          f'; {len(allc)} certificate modules needed')


if __name__ == '__main__':
    main()
