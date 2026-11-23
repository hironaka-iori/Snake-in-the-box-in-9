"""Search recombinations of all fitted punched-donor 191 witnesses, with an outside-site budget."""
from collections import defaultdict
from pathlib import Path
import json
import sys
from q9_intact_bank_search import word_path, verify, search

def main():
    bank = Path("q8_catalogue_96_98.words").read_text().split()
    families = defaultdict(list)
    for line in Path("q9_rigid_puncture_archive_20261121/hits.jsonl").read_text().splitlines():
        r=json.loads(line)
        families[r["donor"],r["hole"]].append(r["vertices"])
    for cap in map(int,sys.argv[1:]):
        for (i,h), paths in sorted(families.items(),key=lambda kv:-len(kv[1])):
            a=word_path(bank[i])
            assert all(verify(p) and len(p)==192 and set(a)-set(p)=={a[h]} for p in paths)
            union=set().union(*map(set,paths))
            fixed=set(a)-{a[h]}
            hard={a[h]} if cap else set(range(512))-union
            for n in ([191,192] if cap==0 else [192]):
                result=search(a,n,120000,set(paths[0]),(),n==191,omit=(a[h],),forbid=hard,exterior=(union,cap))
                if n==191: assert result[0]["status"]=="FOUND"
                print(json.dumps(dict(donor=i,hole=h,parents=len(paths),pool=len(union),cap=cap,goal=n,branches=result)),flush=True)
                if n==192 and any(r["status"]=="FOUND" for r in result):return
if __name__=="__main__": main()
