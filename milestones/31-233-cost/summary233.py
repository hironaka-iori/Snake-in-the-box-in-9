"""Cost summary of a 233 certificate set: data/cost233_best.json (+ the chain of steps).

usage: summary233.py TAG [TAG_STEP1 TAG_STEP2 ...]   (the chain: tags of the sets after each step)
Hints are LRAT hints of the Lean replays (plain keys and share thresholds); kernel hours at checker
v3's 0.1 ms/hint and a conservative 0.2 ms/hint; .olean at 2.5 B/hint, plus ~50 KB of packed
Cnf/Sat module per certificate.  The families step (fam233.py) is applied when data/fam_TAG.json exists.
"""
import sys, os, json, gzip, shutil
import lib233 as L


def main():
    tag = sys.argv[1]; chain = sys.argv[2:]
    s = json.load(open(os.path.join(L.D, f'sum_{tag}.json')))
    ncert = s['plain_paid'] + s['share_paid']
    out = dict(set=f'keys233_best.json.gz (= set_{tag})', P=s['P'], Q=s['Q'], B=s['B'], lam_weight=s['lam'],
               lam_alpha=s['lam_alpha'], potential_range=s['range'], range_allowed=s['Rmax'], bound=s['bound'],
               plain_keys=s['plain_keys'], plain_free=s['plain_free'], plain_paid=s['plain_paid'],
               share_thresholds_used=s['share_used'], share_lean_floor=s['share_lean_floor'],
               share_paid=s['share_paid'],
               plain_hints=s['plain_hints'], share_hints=s['share_hints'],
               plain_by_basis=s['plain_by_basis'], share_by_basis=s['share_by_basis'],
               cost=L.summary_cost(s['hints'], ncert))
    fam = os.path.join(L.D, f'fam_{tag}.json')
    if os.path.exists(fam):
        f = json.load(open(fam))
        out['families'] = f
        out['cost_with_families'] = L.summary_cost(s['hints'] - f['removed_hints'], ncert - f['removed_keys'])
    out['chain'] = []
    for t in chain:
        p = os.path.join(L.D, f'sum_{t}.json')
        if os.path.exists(p):
            c = json.load(open(p))
            out['chain'].append(dict(tag=t, step=c.get('step'), lam_alpha=round(c['lam_alpha'], 4), B=c['B'],
                                     range=c['range'], plain_paid=c['plain_paid'], share_paid=c['share_paid'],
                                     plain_hints=c['plain_hints'], share_hints=c['share_hints'], hints=c['hints']))
    json.dump(out, open(os.path.join(L.D, 'cost233_best.json'), 'w'), indent=1)
    shutil.copy(os.path.join(L.D, f'set_{tag}.json.gz'), os.path.join(L.D, 'keys233_best.json.gz'))
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
