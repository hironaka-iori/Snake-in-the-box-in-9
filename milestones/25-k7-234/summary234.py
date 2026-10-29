"""Cost summary of a k7 key set for 234: hints (measured where available, the solve-time model
elsewhere), kernel-hours at 0.42 and 0.22 ms per hint, .olean disk at about 10 bytes per hint.

  python summary234.py TAG [OUT.json]
"""
import sys, os, json, gzip
sys.dont_write_bytecode = True
import prune234 as P4


def main():
    tag = sys.argv[1]
    d = json.load(gzip.open(os.path.join(P4.D, f'keys_{tag}.json.gz'), 'rt'))
    C = P4.Costs(); O = P4.Oracle()
    by, H, Hm, CL, paid = {}, 0.0, 0.0, 0.0, 0
    for k in d['keys']:
        if k[0] == 'k6':
            h, c, b = C.k6((tuple(k[1]), tuple(k[2]))); kind = 'k6'
        else:
            key = (k[0], tuple(k[1]), tuple(k[2]))
            h, c, b = C.new(key, O.sec.get(key, 0.05)); kind = {'H': 'H9', 'F': 'F8'}[k[0]]
        b = 'reuse' if b == 'reuse' else ('measured' if b == 'measured' else 'model')
        a = by.setdefault(f'{kind}:{b}', [0, 0.0]); a[0] += 1; a[1] += h
        if b != 'reuse':
            paid += 1; H += h; CL += c
            Hm += h if b == 'measured' else 0
    s = d['summary']
    out = dict(tag=tag, P=s['P'], Q=s['Q'], B=s['B'], lam=s['P'] / s['Q'], range=s['range'], bound=s['bound'],
               keys=len(d['keys']), paid_keys=paid,
               counts={t: sum(1 for k in d['keys'] if (k[0] if k[0] != 'H' else 'H9') == t) for t in ('k6', 'H9', 'F')},
               hints=round(H), hints_measured=round(Hm), core_clauses=round(CL),
               kernel_hours_042ms=round(H * 0.42e-3 / 3600), kernel_hours_022ms=round(H * 0.22e-3 / 3600),
               olean_GB_10B_per_hint=round(H * 10 / 1e9, 1),
               by_basis={b: dict(keys=a[0], hints=round(a[1])) for b, a in sorted(by.items())})
    print(json.dumps(out, indent=1))
    if len(sys.argv) > 2:
        json.dump(out, open(sys.argv[2], 'w'), indent=1)


if __name__ == '__main__':
    main()
