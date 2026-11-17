#!/usr/bin/env python3
"""Split one very large certificate into several Lean 4.35 modules (milestone 36, `T012301A36264K45`).

    split435.py --in GENOUT --out SRC [--parts K] [--data-mb 40] NAME

Reads the same 4.19 generator output as to435.py (Cnf source and checker-v3 replay source of NAME) and
writes, instead of ONE merged module `LocalWindowCert.NAME`:

  (ctx certificates: LocalWindowCtxCertSplit.NAME.* and LocalWindowCtxCert.NAME)
  LocalWindowCertSplit.NAME.Cnf     the Cnf body (raw, cnf, tags, check_*, sat), everything public+exposed
  LocalWindowCertSplit.NAME.D<j>    proof data: the segment definitions p<c>, t<c> of a range of segments
  LocalWindowCertSplit.NAME.Ps      `Ps := [p0, p1, ...]` (imports Cnf and every D<j>)
  LocalWindowCertSplit.NAME.K<k>    kernel checks: `ok<c>` (and `warm<c>`) of a contiguous range of
                                    segments, `by decide +kernel`, as the generator wrote them; imports Ps
  LocalWindowCert.NAME              the final module: PRIVATE imports of Cnf, Ps and every K<k>; the
                                    generator's `steps*` lemmas and `unsat` (seg_step / final_false over
                                    the ok<c>), and the same `public theorem refuted : <literal statement>`
                                    as to435.py writes (one `public import LocalWindowShareCtx`)

Soundness: every declaration is the generator's own text, only distributed over modules; the checker
reads `Ps` only through `segP`, so the statement of `ok<c>` is the same term whichever module holds it.
The K<k> are independent of each other (each needs Cnf + D* + Ps only), so they can be built on different
machines; the final module only type-checks the chain (no evaluation). The parts must be built from the
SAME sources (sha256 in SPLIT-MANIFEST.json) and their imported Cnf/D/Ps .olean must be byte-identical to
the final machine's (4.35 output is deterministic; `split435.py verify` checks the recorded hashes).

The final module exports only `refuted` and has the exported imports {LocalWindowShareCtx}, like a
merged certificate, so glue (glue435.py), assemble435.py and audit.py load only its public .olean.

Weights: a segment's weight is the byte size of its p<c> definition (packed lemma words, ~ hints).
"""
import argparse, hashlib, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import port  # noqa: E402

DECL = re.compile(r'^(?:noncomputable def|theorem) (\w+)', re.M)


def decls(body):
    """[(name, text)] of the top-level declarations of a body (from one decl start to the next)."""
    ms = list(DECL.finditer(body))
    out = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(body)
        out.append((m.group(1), body[m.start():end].rstrip() + '\n'))
    return out, (ms[0].start() if ms else len(body))


def sha_t(t):
    return hashlib.sha256(t.encode()).hexdigest()


def chunks(ws, k):
    """Cut the weights ws into k contiguous ranges of about equal sum: list of (a, b)."""
    tot, out, a, acc = sum(ws), [], 0, 0
    for i, w in enumerate(ws):
        acc += w
        if len(out) < k - 1 and acc >= tot * (len(out) + 1) / k and i + 1 < len(ws):
            out.append((a, i + 1))
            a = i + 1
    out.append((a, len(ws)))
    return out


def split(name, cnf_text, unsat_text, nparts, data_mb, ctx=False):
    ns = f'Snake9.LocalWindow.{name}'
    cnf_mod = 'LocalWindowCtxCnf.' if ctx else 'LocalWindowCnf.'
    fdir = 'LocalWindowCtxCert' if ctx else 'LocalWindowCert'
    pre = f'{fdir}Split.{name}'
    cl, ce, ci = port.split_header(cnf_text)
    ul, ue, ui = port.split_header(unsat_text)
    cmod = cnf_mod + name
    assert cmod in ui, 'replay does not import its Cnf module'
    cbody = '\n'.join(cl[ce:]).strip() + '\n'
    ubody = '\n'.join(ul[ue:])
    assert cbody.rstrip().endswith(f'end {ns}')
    assert ubody.rstrip().endswith(f'end {ns}')
    opts = re.findall(r'^set_option .*$', ubody, re.M)
    assert opts == ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false'], opts
    k0 = ubody.index(f'namespace {ns}\n') + len(f'namespace {ns}\n')
    k1 = ubody.rindex(f'end {ns}')
    ds, _ = decls(ubody[k0:k1])
    names = [n for n, _ in ds]
    D = dict(ds)
    assert len(D) == len(ds), 'duplicate declaration names'
    nseg = sum(1 for n in names if re.fullmatch(r'p\d+', n))
    expect = {f'p{c}' for c in range(nseg)} | {f't{c}' for c in range(nseg)} | {f'ok{c}' for c in range(nseg)} | {'Ps', 'unsat'}
    rest = set(names) - expect
    assert all(re.fullmatch(r'warm\d+|steps\d+', n) for n in rest), sorted(rest)[:10]
    assert expect <= set(names)
    for n in rest:
        if n.startswith('warm'):
            assert int(n[4:]) < nseg
    cdecl = set(DECL.findall(cbody))
    assert not (cdecl & set(names)) and 'refuted' not in cdecl | set(names)
    stmt, proof = port.refuted_decl(cnf_text)
    other_imps = [i for i in ci + ui if i != cmod]
    imps = []
    for i in other_imps:
        if i not in imps:
            imps.append(i)
    hdr = lambda what: [f'-- {pre}: {what} (lean435/tools/split435.py; generator text, distributed over modules)']
    O = '\n'.join(opts)
    files = {}
    # Cnf
    files[f'{pre}.Cnf'] = '\n'.join(['module', ''] + hdr('the Cnf part') + ['public import ' + i for i in ci] +
                                    ['', '@[expose] public section', '', cbody])
    # data chunks
    wseg = [len(D[f'p{c}']) + len(D[f't{c}']) for c in range(nseg)]
    nd = max(1, -(-sum(wseg) // int(data_mb * 1e6)))
    dr = chunks(wseg, nd)
    dmods = []
    for j, (a, b) in enumerate(dr):
        m = f'{pre}.D{j}'
        dmods.append(m)
        body = ''.join(D[f'p{c}'] + '\n' for c in range(a, b)) + ''.join(D[f't{c}'] + '\n' for c in range(a, b))
        files[m] = '\n'.join(['module', ''] + hdr(f'proof data of segments {a}..{b - 1}') +
                             ['public import ProofPack', 'public import LratV3', '', '@[expose] public section', '',
                              O, '', f'namespace {ns}', '', body + f'end {ns}', ''])
    files[f'{pre}.Ps'] = '\n'.join(['module', ''] + hdr('the segment list') + ['public import ' + f'{pre}.Cnf'] +
                                   ['public import ' + m for m in dmods] +
                                   ['', '@[expose] public section', '', O, '', f'namespace {ns}', '', D['Ps'],
                                    f'end {ns}', ''])
    # kernel-check parts: weights = p<c> size (the work of ok<c> is ~ its hints)
    wk = [len(D[f'p{c}']) for c in range(nseg)]
    kr = chunks(wk, nparts)
    kmods = []
    for k, (a, b) in enumerate(kr):
        m = f'{pre}.K{k}'
        kmods.append(m)
        body = ''
        for c in range(a, b):
            if f'warm{c}' in D:
                body += D[f'warm{c}'] + '\n'
            body += D[f'ok{c}'] + '\n'
        files[m] = '\n'.join(['module', ''] + hdr(f'kernel checks of segments {a}..{b - 1}') +
                             [f'public import {pre}.Ps', 'public import LratV3', '', 'public section', '', O, '',
                              f'namespace {ns}', '', body + f'end {ns}', ''])
    # final
    steps = ''.join(D[n] + '\n' for n in names if n.startswith('steps'))
    tail = (f'/-- The certificate, stated with literal parameters (lean435/tools/to435.py). -/\n'
            f'public theorem refuted : {stmt} :=\n  {proof}\n\n')
    fin = (['module', '', f'-- {fdir}.{name}: the final module of a split certificate '
            '(lean435/tools/split435.py); its parts are private imports', 'public import LocalWindowShareCtx'] +
           ['import ' + i for i in imps] + [f'import {pre}.Cnf', f'import {pre}.Ps'] + ['import ' + m for m in kmods] +
           ['', O, '', f'namespace {ns}', '', steps + D['unsat'], tail + f'end {ns}', ''])
    files[f'{fdir}.{name}'] = '\n'.join(fin)
    info = dict(name=name, segments=nseg, data=[[m, a, b] for m, (a, b) in zip(dmods, dr)],
                parts=[[m, a, b, sum(wk[a:b])] for m, (a, b) in zip(kmods, kr)],
                final=f'{fdir}.{name}', prefix=pre, statement=stmt,
                inputs={'cnf_sha256': sha_t(cnf_text), 'unsat_sha256': sha_t(unsat_text)},
                sources={m: sha_t(t) for m, t in files.items()})
    return files, info


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--in', dest='inp', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--parts', type=int, default=4)
    ap.add_argument('--data-mb', type=float, default=40.0)
    ap.add_argument('name')
    a = ap.parse_args()
    ctx = os.path.exists(os.path.join(a.inp, 'LocalWindowCtxCnf', a.name + '.lean'))
    cp = os.path.join(a.inp, 'LocalWindowCtxCnf' if ctx else 'LocalWindowCnf', a.name + '.lean')
    up = os.path.join(a.inp, 'LocalWindowCtxUnsat' if ctx else 'LocalWindowUnsat', a.name + '.lean')
    files, info = split(a.name, open(cp, encoding='utf-8').read(), open(up, encoding='utf-8').read(),
                        a.parts, a.data_mb, ctx)
    for m, t in files.items():
        q = os.path.join(a.out, m.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(q), exist_ok=True)
        open(q, 'w', encoding='utf-8').write(t)
        print(f'{m}: {len(t.encode())} bytes')
    mp = os.path.join(a.out, f'SPLIT-MANIFEST.{a.name}.json')
    json.dump(info, open(mp, 'w'), indent=1)
    print(json.dumps({k: v for k, v in info.items() if k != 'sources'}))


if __name__ == '__main__':
    main()
