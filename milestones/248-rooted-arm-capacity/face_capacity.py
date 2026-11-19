"""Bound the parity counts in each rooted domain using Q4 restrictions alone."""
from collections import Counter
from functools import lru_cache
from pathlib import Path

import conditioned as search


def bound(domain, fixed):
    # A parent face may be split along any of its free coordinates.  The actual
    # count pair must lie in the Minkowski sum for *every* one of those splits.
    # Children can therefore use different orientations for their own Q4 covers.
    seen = Counter()
    encoded = {}
    root_splits = []
    @lru_cache(maxsize=None)
    def counts(mask,base):
        free = [i for i in range(8) if not mask & (1 << i)]
        seen[len(free)] += 1
        if len(free) == 4:
            offsets = [0]
            for i in free:
                offsets += [v | (1<<i) for v in offsets]
            pairset = search.face_table([base|v for v in offsets],domain,fixed)
            packed = sum(1<<(e+search.STRIDE*o) for e,o in pairset)
        else:
            packed = None
            for i in free:
                bit = 1<<i
                a = counts(mask|bit,base)
                b = counts(mask|bit,base|bit)
                if a.bit_count()>b.bit_count():
                    a,b=b,a
                total = 0
                for offset in search.bits(a):
                    total |= b << offset
                if not mask:
                    root_splits.append(dict(axis=i,admits_quota=bool(search.attainable(total,48,48))))
                packed = total if packed is None else packed & total
        encoded[(mask,base)] = packed
        return packed
    root = counts(0,0)
    equal = [k for k in range(81) if search.attainable(root,k,k)]
    # These relaxed maxima include the frozen proper prefix and the requirement
    # that selected vertices can attain their necessary degrees in the domain.
    result = dict(admits_48_each=bool(search.attainable(root,48,48)),
                  largest_equal_parity_quota=max(equal,default=None),
                  maximum_total=max(((n//search.STRIDE)+(n%search.STRIDE) for n in search.bits(root)),default=None),
                  root_splits=root_splits, face_counts=seen)
    if not result["admits_48_each"]:
        # Full finite certificate for successful exclusions only. Each byte
        # string is a little-endian bit field indexed by even+128*odd.
        result["tables"]=[dict(fixed_mask=m,base=b,
                               counts_hex=n.to_bytes((n.bit_length()+7)//8,"little").hex())
                          for (m,b),n in sorted(encoded.items())]
    counts.cache_clear()
    return result


def main():
    parents=search.partner.parent_arms()
    rows=[]
    for i,e,prefix in search.open_cases():
        arm=search.partner.rooted_parent(parents[i],e)
        domain=search.domain_after_prefix(arm,prefix)
        if not set(prefix)<=domain:
            answer=dict(admits_48_each=False,removed_prefix=True)
        else:
            answer=bound(domain,set(prefix))
        rows.append(dict(class_id=i,endpoint=e,prefix=prefix,**answer))
        print(i,e,prefix,"admits 48+48:",answer["admits_48_each"],flush=True)
    source=search.HERE/"conditioned.py"
    search.save(search.HERE/"face-capacities.json",dict(
        sources={p.name:search.partner.digest(p) for p in (Path(__file__),source,search.LAST/"partner-children-summary.json")},
        scope="Local Q4 induced-forest restrictions and parity count propagation over every axis split; a surviving count pair is inconclusive.",
        standalone_exclusions=sum(not r["admits_48_each"] for r in rows),records=rows))


if __name__=="__main__":
    main()
