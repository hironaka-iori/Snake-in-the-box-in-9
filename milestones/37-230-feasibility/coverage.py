"""Which window exclusions of a relaxed-keller minimal set are implied by a Lean-certified key of the
main line (the 31,902 plain keys of the 231 plan, all Lean-certified or derivable): a contiguous
sub-window (either orientation) with containing count bounds.  Prints counts and DRUP proof lines.
usage: coverage.py MINIMAL_SET.json INDEX.json [OUT_UNCOVERED.json]"""
import gzip, json, collections, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
PLAN = os.path.join(HERE, '..', '28-combined-identities', 'data', 'certplan231_563_1_cap.json.gz')
LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)


def canon(ds):
    m = {}; return tuple(m.setdefault(x, len(m)) for x in ds)


def main_keys():
    d = json.load(gzip.open(PLAN))
    M = collections.defaultdict(list)
    for r in d['plain']:
        ds, sy = r['key']
        if len(sy) != len(ds) - 1:
            continue
        b = tuple(LUMP[s] for s in sy)
        M[canon(ds)].append(b); M[canon(ds[::-1])].append(b[::-1])
    return M


def covered(e, M):
    n = len(e['dirs']); al = e['alpha']
    for i in range(n):
        for j in range(i + 3, n + 1):
            for b in M.get(canon(e['dirs'][i:j]), ()):
                if all(lo >= bl and hi <= bh for (lo, hi), (bl, bh) in zip(al[i:j - 1], b)):
                    return True
    return False


if __name__ == '__main__':
    M = main_keys()
    idx = {(tuple(c['dirs']), tuple(map(tuple, c['alpha']))): c for c in json.load(open(sys.argv[2]))['cases']}
    ex = json.load(open(sys.argv[1]))['exclusions']
    tot = cl = 0; unc = []; ncov = 0
    for e in ex:
        c = idx[(tuple(e['dirs']), tuple(map(tuple, e['alpha'])))]
        tot += c['proof_lines']
        if covered(e, M):
            ncov += 1; cl += c['proof_lines']
        else:
            unc.append(dict(case=c['case'], dirs=e['dirs'], alpha=e['alpha'], radius=c['radius'],
                            proof_lines=c['proof_lines'], seconds=c['seconds']))
    print(json.dumps(dict(set=os.path.basename(sys.argv[1]), windows=len(ex), covered=ncov, uncovered=len(unc),
                          proof_lines_M=round(tot / 1e6, 1), uncovered_lines_M=round((tot - cl) / 1e6, 1))))
    if len(sys.argv) > 3:
        json.dump(unc, (gzip.open if sys.argv[3].endswith('.gz') else open)(sys.argv[3], 'wt'))
