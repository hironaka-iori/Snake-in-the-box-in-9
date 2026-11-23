"""Reconcile the near-optimal Q8 seed searches and the Q9 deletion logs."""
from collections import Counter
from itertools import product
from math import comb
from pathlib import Path
import hashlib,json
from verify_q9_center_avoidance import verify
from verify_q9_explicit_layer_join import main as explicit
def read(f):return [json.loads(l) for l in Path(f).read_text().splitlines()]
def main():
    fn="q9_near98_atleast192.jsonl";ctrl,*rows=read(fn)
    assert ctrl[4]=="FOUND" and len(ctrl[-1])==99 and ctrl[3]==96;verify(ctrl[-1])
    arm=read("q8_free_layer_full98_duals.jsonl")[0]["certificate"]["arm"]
    verify(arm);assert set(ctrl[-1])==set(arm)
    cases={(j,g,e) for j in range(99) for g,e in ((192,0),(192,1),(193,0))}
    assert len(rows)==297 and {(j[0],g,e) for j,e,g,*_ in rows}==cases
    statuses=Counter()
    for (idx,),e,g,s,upper,w in rows:
        assert s in {"DUAL_EXCLUSION","EXHAUSTED"} and w is None
        if s=="DUAL_EXCLUSION":assert upper<(g+1)*10000
        statuses[s]+=1
    other=read("q9_near98_sat_atleast192.jsonl")
    assert len(other)==100 and len({r[0] for r in other[1:]})==99
    c,*exchanges=read("q9_five_delete_192.jsonl")
    assert c["q9_crosschecks"]==131 and {r[0] for r in exchanges}==set(range(131)) and len(exchanges)==131
    assert all(r[1]=="NO" and r[2]==comb(192,5) and not r[-1] for r in exchanges)
    small=json.loads(Path("q9_minimum_controls.json").read_text())
    joined=explicit()
    return dict(q8_reference_vertices=arm,near98_minimum_cases=len(cases),minimum_outcomes=statuses,
                minimum_log_sha256=hashlib.sha256(Path(fn).read_bytes()).hexdigest(),
                independent_cardinality_sat=Counter(r[2] for r in other[1:]),small_cube_control=small,
                five_delete_combinations=sum(r[2] for r in exchanges),known_q9_parents=len(exchanges),
                q8_join_edges=joined["edges"],q8_join_checked_pairs=joined["checked_pairs"])
if __name__=="__main__":print(json.dumps(main(),indent=2))
