"""Replace kept H9 keys by their F8 generalisation where that is cheaper (README 'Cost reduction').

An H9 key excludes one step window X with counts a2..a8 (a1 uncounted); the F8 key
f8_key(X, c) excludes the 8-direction window X[1:] with the same 7 counts, in both orientations,
for every X with that suffix.  So it excludes a superset of the transitions of every H9 key of
its group, and the substitution can only remove transitions: the potential stays valid.

  nice -n 10 python f8sub234.py TAG NEWTAG
Writes data/keys_NEWTAG.json.gz (re-prune it with prune234.py --start NEWTAG --start-strict).
"""
import sys, os, json, gzip, collections
sys.dont_write_bytecode = True
import k7
import prune234 as P4
from k7 import canon


def main():
    tag, new = sys.argv[1], sys.argv[2]
    d = json.load(gzip.open(os.path.join(P4.D, f'keys_{tag}.json.gz'), 'rt'))
    C = P4.Costs(); O = P4.Oracle()

    def cost(key):
        return C.eff(*C.new(key, O.sec.get(key, 0.05)))

    groups = collections.defaultdict(list)
    for k in d['keys']:
        if k[0] == 'H':
            key = ('H', tuple(k[1]), tuple(k[2]))
            f = k7.f8_key(canon(tuple(reversed(key[1]))), tuple(reversed(key[2])))
            groups[f].append(key)
    drop, add, saved = set(), [], 0.0
    for f, mem in groups.items():
        if O.st.get(f) != 'UNSAT':
            continue
        cf, cm = cost(f), sum(cost(m) for m in mem)
        if cf < cm:
            drop |= set(mem); add.append(f); saved += cm - cf
    keys = [k for k in d['keys'] if not (k[0] == 'H' and ('H', tuple(k[1]), tuple(k[2])) in drop)]
    have = {json.dumps(k) for k in keys}
    for f in add:
        k = [f[0], list(f[1]), list(f[2])]
        if json.dumps(k) not in have:
            keys.append(k)
    d['keys'] = keys; d['summary'] = dict(d['summary'], tag=new)
    for x in ('hints', 'core', 'basis'):
        d.pop(x, None)
    json.dump(d, gzip.open(os.path.join(P4.D, f'keys_{new}.json.gz'), 'wt'))
    print(json.dumps(dict(groups=len(groups), decided=sum(1 for f in groups if f in O.st),
                          replaced_groups=len(add), h9_dropped=len(drop), saved_objective=round(saved))))


if __name__ == '__main__':
    main()
