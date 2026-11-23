"""Check that the recorded splits really partition the remaining even-endpoint problem."""
from collections import deque
from pathlib import Path
import json

def rows(name):
    return list(map(json.loads,Path(name).read_text().splitlines()))

def main():
    outer=rows("q9_junction_first_omission.jsonl")
    assert len(outer)==12
    anchor=set(outer[0]["fixed"])
    for r in outer:
        assert set(r["fixed"])==anchor and r["omitted"] not in anchor
        anchor.add(r["omitted"])
    assert len(anchor)==87
    undecided=[r for r in outer if r["status"]!="UNSAT"]
    assert len(undecided)==1 and undecided[0]["status"]=="UNKNOWN"
    base=set(undecided[0]["fixed"])
    omitted={undecided[0]["omitted"]}
    assert omitted=={508} and 144 in base
    inner=rows("q9_junction_second_omission.jsonl")
    for index,r in enumerate(inner):
        assert set(r["fixed"])==base
        extra=set(r["excluded"])-omitted
        assert set(r["excluded"])==extra|omitted
        if index==len(inner)-1:assert not extra
        else:assert len(extra)==1 and not base&extra
        base.update(extra)
    open_nodes=deque((set(r["fixed"]),set(r["excluded"])) for r in inner if r["status"]=="UNKNOWN")
    assert open_nodes and all(144 in a and {26,508}<=b for a,b in open_nodes)
    tree=rows("q9_junction_branch.jsonl")
    for r in tree:
        fixed,excluded=open_nodes.popleft()
        assert (set(r["fixed"]),set(r["excluded"]))==(fixed,excluded)
        if r["status"]=="UNKNOWN":
            v=r["split"]
            assert v in range(512) and v not in fixed|excluded
            open_nodes.extend([(fixed|{v},excluded),(fixed,excluded|{v})])
        else:assert r["status"]=="UNSAT"
        assert len(open_nodes)==r["pending"]
    return dict(nodes_checked=len(tree),pending_leaves=len(open_nodes),
                unresolved_require=[144],unresolved_exclude=[26,508])
if __name__=="__main__":print(json.dumps(main()))
