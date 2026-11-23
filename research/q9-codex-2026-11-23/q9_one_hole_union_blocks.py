"""Cover small exterior budgets with overlapping allowed blocks in the full 191 seed-union search."""
from itertools import combinations_with_replacement
from pathlib import Path
import json,random,sys
from q9_intact_bank_search import word_path,search,verify

def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    seeds=[json.loads(s) for s in Path("q9_rigid_puncture_archive_20261121/hits.jsonl").read_text().splitlines()]
    for cap in [1,2]:
        for i,h in [(472,0),(576,96)]:
            family=[r["vertices"] for r in seeds if (r["donor"],r["hole"])==(i,h)]
            union=set().union(*map(set,family));arm=word_path(bank[i]);fixed=set(arm)-{arm[h]}
            sat={v for v in fixed if sum((v^1<<d) in fixed for d in range(9))==2}
            blocked={arm[h]}|({v^1<<d for v in sat for d in range(9)}-fixed)
            assert not union&blocked and all(verify(p) for p in family)
            outside=sorted(set(range(512))-union-blocked)
            random.Random(59821).shuffle(outside)
            blocks=[outside[k:k+5] for k in range(0,len(outside),5)]
            jobs=[(k,) for k in range(len(blocks))] if cap==1 else list(combinations_with_replacement(range(len(blocks)),2))
            for indices in jobs:
                allowed=union.union(*(blocks[k] for k in indices))
                r=search(arm,192,80000,set(family[0]),(),False,omit=(arm[h],),forbid=set(range(512))-allowed,exterior=(union,cap))
                print(json.dumps(dict(donor=i,hole=h,cap=cap,group=indices,groups=len(jobs),sites=len(outside),branches=r)),flush=True)
                if any(z["status"]=="FOUND" for z in r):return
if __name__=="__main__":main()
