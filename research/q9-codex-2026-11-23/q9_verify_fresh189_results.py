from pathlib import Path
from collections import Counter
import math,json
from q9_classify_record_donor_windows import canonical
from q9_rigid_facet_ports import word_path
D=Path("q9_degree_trade_pairs")
def main():
    bank=list(map(word_path,Path("q9_uncovered_abab_20261121/outside_wordbanks189.words").read_text().split()))
    archive={canonical(w):i for i,w in enumerate(Path("q9_far189_spring_20261121/comparison191.words").read_text().split())}
    r=list(map(json.loads,(D/"new189.jsonl").read_text().splitlines()))
    assert r.pop(0)["Q3_controls"]==[1008,576]
    expected={(i,k,g) for i in range(16) for k in range(6) for g in (2,3)}
    hits=[];total=0;tested=0
    for row in r:
        i,k,g=row["row"],row["deleted"],row["gain"];expected.remove((i,k,g))
        if row["found"]:
            p=row["vertices"];assert len(p)==len(set(p))==190+g and all(0<=v<512 for v in p)
            assert len(set(bank[i])-set(p))==k and all(((v^x).bit_count()==1)==(a+1==b) for b,v in enumerate(p) for a,x in enumerate(p[:b]))
            key=canonical("".join(str((v^x).bit_length()-1) for v,x in zip(p,p[1:])))
            hits.append((i,len(p)-1,archive.get(key)))
        else:assert row["deletion_sets"]==math.comb(190,k)
        if g==3:total+=row["deletion_sets"];tested+=row["candidates"]
    assert not expected
    assert total==16*sum(math.comb(190,k) for k in range(6))
    x=[json.loads(l) for l in (D/"mixed8.jsonl").read_text().splitlines()]
    result=dict(seeds=len(bank),removed=[0,1,2,3,4,5],controls=1008,validated_control_positives=576,
                covered_deletion_sets_192=total,final_candidates_192=tested,paths_192=sum(n>=192 for _,n,_ in hits),
                seeds_with_191=len({i for i,n,c in hits if n==191}),archive_191=sorted({c for _,n,c in hits if n==191}),
                sparse_region_8_width=[min(t["released"] for t in x),max(t["released"] for t in x)])
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
