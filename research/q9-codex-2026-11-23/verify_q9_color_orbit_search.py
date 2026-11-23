"""Audit coverage of the paired-color search, including the retried rows."""
import gzip
import json
from collections import Counter
from verify_q9_center_avoidance import forms, verify


def read(path):
    with open(path) as f:return list(map(json.loads,f))


def audit():
    bank={}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,line.split()))
        if len(p)==192:
            verify(p)
            bank.setdefault(forms(p,191)[0],p)
    assert len(bank)==131
    masks=[t for t in range(1,512) if not t.bit_count()%2]
    paths=list(bank.values())
    cases={}
    def record(row,retry):
        i,s,t,k,st,w=row
        key=i,s,t
        if retry:assert cases[key]=="UNKNOWN"
        else:assert key not in cases
        assert 0<=i<len(paths) and s in (0,1) and t in masks
        side=set(paths[i][s::2])
        assert len(side)==96 and len([v for v in side if v^t not in side])==k
        assert st in ("FOUND","UNSAT","UNKNOWN") and (w is not None)==(st=="FOUND")
        if w:
            verify(w)
            assert len(w)==193
            m=set(w[1::2])
            assert all((v in m)+(v^t in m)==(v in side)+(v^t in side) for v in range(512))
        cases[key]=st
    for row in read("q9_all_color_orbits_192.jsonl"):record(row,False)
    assert len(cases)==len(paths)*2*len(masks)
    original=Counter(cases.values())
    for row in read("q9_all_color_orbits_deep_192.jsonl"):record(row,True)
    final=Counter(cases.values())
    ctrl=json.load(open("q9_pair_selector_control.json"))
    assert ctrl["all_agreed"] and ctrl["statuses"]["FOUND"]>0 and ctrl["statuses"]["UNSAT"]>0
    return dict(parent_shapes=len(paths),color_choices=2,translations=len(masks),
                cases=len(cases),first_pass=original,after_retry=final,
                explicit_assignment_controls=ctrl)
if __name__=="__main__":print(json.dumps(audit(),indent=2))
