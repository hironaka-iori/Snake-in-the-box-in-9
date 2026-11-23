"""Audit case coverage and verify positive paths without the SAT solver."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

def rows(stem):
    return list(map(json.loads,Path(stem+".jsonl").read_text().splitlines()))

def identity(row):
    return row["source"],row["row"],row["omitted"]

def index(stem):
    records=rows(stem)
    out={identity(r):r for r in records}
    assert len(out)==len(records)
    return out

def by_signature(stem,identity_fn):
    result={}
    for r in rows(stem):
        sigs=result.setdefault(identity_fn(r),{})
        assert r["sig"] not in sigs
        sigs[r["sig"]]=r
    assert all(set(s)=={0,1,2} for s in result.values())
    return result

def check_positives(stem):
    result=Counter()
    for r in rows(stem):
        w=r["witness"]
        if not w:continue
        assert len(w)==len(set(w)) and all(0<=v<512 for v in w)
        for (i,v),(j,u) in combinations(enumerate(w),2):
            assert ((v^u).bit_count()==1)==(j==i+1)
        if "omitted" in r:assert r["omitted"] not in w
        result[len(w)-1]+=1
    return result

def main():
    r9=index("q9_capacity_groups_radius9")
    assert set(r9)=={k for k,r in index("q9_break_matched_radius9_retry").items() if r["status"]=="UNKNOWN"}
    assert len(r9)==81 and all(r["status"]=="UNSAT" for r in r9.values())
    base=index("q9_break_matched_width12")
    revised=index("q9_capacity_groups_radius12")
    assert len(base)==2232 and set(revised)=={k for k,r in base.items() if r["status"]=="UNKNOWN"}
    base.update(revised)
    signatures=by_signature("q9_endpoint_domains_r12",identity)
    assert set(signatures)=={k for k,r in base.items() if r["status"]=="UNKNOWN"}
    broad_key=lambda r:(r["source"],r["row"],r["radius"])
    broad=rows("q9_full_obstruction_release")
    broad_sig=by_signature("q9_full_obstruction_endpoint",broad_key)
    assert set(broad_sig)=={broad_key(r) for r in broad if r["status"]=="UNKNOWN"}
    def outcome(r,key,parts):
        if r["status"]!="UNKNOWN":return r["status"]
        verdicts={v["status"] for v in parts[key].values()}
        if "FOUND" in verdicts:return "FOUND"
        return "UNKNOWN" if "UNKNOWN" in verdicts else "UNSAT"
    mixed=index("q9_minimal_mixed")
    pending={k for k,r in base.items() if outcome(r,k,signatures)=="UNKNOWN"}
    assert set(mixed)==pending
    for k,r in mixed.items():
        assert signatures[k][0]["status"]==signatures[k][1]["status"]=="UNSAT"
        assert signatures[k][2]["status"]=="UNKNOWN" and r["status"]=="UNSAT"
        # All opposite-color candidates have odd length >=193. A free endpoint
        # could be trimmed to a same-color candidate of even length >=192.
        # Otherwise both endpoints are anchored, which the final solver excludes.
    return dict(radius12_all_lengths_excluded=len(base),mixed_cases_requiring_fixed_tips=len(mixed),radius9_completed=len(r9),radius12_before_fixed_tip_check=Counter(outcome(r,k,signatures) for k,r in base.items()),
                all_anchors_released=Counter(outcome(r,broad_key(r),broad_sig) for r in broad),
                controls={name:check_positives(name) for name in ("q9_capacity_groups_control","q9_endpoint_domains_control","q9_full_obstruction_191","q9_mosaic_lists_control")})
if __name__=="__main__":print(json.dumps(main(),indent=2))
