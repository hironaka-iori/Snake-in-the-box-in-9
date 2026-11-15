#!/usr/bin/env python3
"""Generator switch: turn certificate sources written by the 4.19 generators (cert233.py,
milestones/35-231-lean/certify/cert231.py, scripts/gen_lean_*.py) into Lean 4.35 module files.
The generators are not modified: this post-processor reads their output.

    to435.py --in GENOUT --out SRC435 [--pair] NAME...

GENOUT holds, per certificate NAME, the Cnf source <CnfDir>/NAME.lean and the replay source
<UnsatDir>/NAME.lean, with (CnfDir, UnsatDir) = (LocalWindowCtxCnf, LocalWindowCtxUnsat) for ctx
certificates and (LocalWindowCnf, LocalWindowUnsat) for share and plain ones (as cert231.py writes).

Default: ONE module per certificate, `LocalWindowCtxCert.NAME` / `LocalWindowCert.NAME`
(AUDIT-SCALING.md: every imported .olean is one memory mapping, limit 65,530), containing
  - `module`, all imports private, plus `public import LocalWindowShareCtx` (the statement's names);
  - the Cnf body and the replay body, both private (not exported, not exposed);
  - `public theorem refuted : <predicate with literal parameters> := <_of_sat> sat unsat`.
Its public .olean holds only `refuted` (about 9 KB). With --pair, the two-module form of port.py
(Cnf private; replay `import all` Cnf) is written instead.
"""
import argparse, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import port  # noqa: E402

KINDS = [('LocalWindowCtxCnf', 'LocalWindowCtxUnsat', 'LocalWindowCtxCert'),
         ('LocalWindowCnf', 'LocalWindowUnsat', 'LocalWindowCert')]


def merged(name, cnf_text, unsat_text, cnf_mod, cert_dir):
    cl, ce, ci = port.split_header(cnf_text)
    ul, ue, ui = port.split_header(unsat_text)
    if cnf_mod not in ui:
        raise SystemExit(f'to435: {name}: replay does not import {cnf_mod}')
    imps = []
    for i in ci + ui:
        if i != cnf_mod and i not in imps:
            imps.append(i)
    cbody = '\n'.join(cl[ce:]).rstrip()
    ubody = '\n'.join(ul[ue:]).strip()
    ns = f'Snake9.LocalWindow.{name}'
    for body in (cbody, ubody):
        if not body.rstrip().endswith(f'end {ns}'):
            raise SystemExit(f'to435: {name}: a body does not end with `end {ns}`')
    # disjoint declaration names (the two bodies share the namespace)
    rx = re.compile(r'^(?:noncomputable )?(?:def|theorem|abbrev) (\S+)', re.M)
    a, b = set(rx.findall(cbody)), set(rx.findall(ubody))
    if a & b or 'refuted' in a | b:
        raise SystemExit(f'to435: {name}: duplicate declaration names {sorted(a & b)}')
    # the replay repeats the options; options inside a namespace are scoped, so keep both
    stmt, proof = port.refuted_decl(cnf_text)
    k = ubody.rfind(f'end {ns}')
    tail = (f'/-- The certificate, stated with literal parameters (lean435/tools/to435.py). -/\n'
            f'public theorem refuted : {stmt} :=\n  {proof}\n\n')
    out = ['module', '', f'-- {cert_dir}.{name}: Cnf and replay of one certificate in one module '
           '(lean435/tools/to435.py)', 'public import LocalWindowShareCtx']
    out += ['import ' + i for i in imps]
    return '\n'.join(out) + '\n' + cbody + '\n\n' + ubody[:k] + tail + ubody[k:] + '\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--in', dest='inp', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--pair', action='store_true')
    ap.add_argument('names', nargs='+')
    a = ap.parse_args()
    for n in a.names:
        for cdir, udir, mdir in KINDS:
            cp, up = os.path.join(a.inp, cdir, n + '.lean'), os.path.join(a.inp, udir, n + '.lean')
            if os.path.exists(cp) and os.path.exists(up):
                break
        else:
            raise SystemExit(f'to435: no Cnf + replay sources for {n} under {a.inp}')
        ct, ut = open(cp, encoding='utf-8').read(), open(up, encoding='utf-8').read()
        if a.pair:
            files = {f'{cdir}/{n}.lean': port.port_cnf(f'{cdir}.{n}', ct),
                     f'{udir}/{n}.lean': port.port_replay(f'{udir}.{n}', ut, ct)}
        else:
            files = {f'{mdir}/{n}.lean': merged(n, ct, ut, f'{cdir}.{n}', mdir)}
        for rel, txt in files.items():
            q = os.path.join(a.out, rel)
            os.makedirs(os.path.dirname(q), exist_ok=True)
            open(q, 'w', encoding='utf-8').write(txt)
            print(f'{rel}: {len(txt.encode())} bytes')


if __name__ == '__main__':
    main()
