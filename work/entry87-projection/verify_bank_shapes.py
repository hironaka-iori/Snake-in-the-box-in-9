"""Verify every positive shape obstruction using direct projected paths."""
from collections import Counter
import csv,json
from pathlib import Path
from itertools import combinations
from insertion_shapes import patterns,projected_intervals,scores
from solve import BANK,save

if __name__=="__main__":
    bank=[r["vertex_sequence"] for r in json.loads(BANK.read_bytes())]
    rows=list(csv.DictReader(Path("bank-shape-exclusions.csv").open(encoding="utf-8-sig")))
    all_masks={sum(1<<i for i in b) for b in combinations(range(9),3)}
    assert len(rows)==131*84 and {(int(r["entry"]),int(r["retained_mask"])) for r in rows}=={
        (k,m) for k in range(131) for m in all_masks}
    fam,lookup=patterns(); totals=Counter(); peaks=[];checks=0
    for row in rows:
        k=int(row["entry"]);mask=int(row["retained_mask"]);peak=int(row["peak"])
        keep=tuple(b for b in range(9) if mask>>b&1)
        ps=list(map(int,row["excluded_positions"].split()))
        assert len(set(ps))==len(ps)==int(row["exclusions"])
        totals[k]+=len(ps)
        src=bank[k]
        for j in ps:
            q=src[:j+1]+src[j:]
            tr=projected_intervals(q,keep)
            vals=scores(tr,fam,lookup)
            assert max(v for v,_ in vals)>32
            checks+=1
        j=int(row["sample_position"])
        tr=projected_intervals(src[:j+1]+src[j:],keep)
        parity=int(row["sample_parity"]);family=fam[int(row["sample_family"])]
        obs=sum(any(t&s==s for s in family) for t in tr[parity::2])
        assert obs==peak
        peaks.append(peak)
    report=dict(bank_entries=len(bank),retained_triples=len(all_masks),
                tested_insertions=len(rows)*192,checked_exclusions=checks,
                min_per_entry=min(totals.values()),max_per_entry=max(totals.values()),
                affected_entries=sum(n>0 for n in totals.values()),max_obstruction=max(peaks))
    print(report)
    save(Path("bank-shapes-summary.json"),report)
