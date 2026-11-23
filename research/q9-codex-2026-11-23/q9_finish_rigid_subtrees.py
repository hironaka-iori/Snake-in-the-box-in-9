"""Finish still-open rigid subtrees in breadth-first order, using exactly the inherited pins."""
import json,subprocess
from pathlib import Path
from collections import deque
from q9_resume_rigid_leaves import B,D,OUT,open_nodes,replay
def main():
    r=[json.loads(line) for line in Path("q9_rigid_continuations.jsonl").read_text().splitlines()]
    init=[x for x in r if "initial" in x];stage=[x for x in r if "leaf" in x]
    assert len(init)==144 and len(stage)==sum(x["initial"]["open"] for x in init)
    root=OUT/"next";root.mkdir(exist_ok=True)
    queue=deque()
    for x in stage:
        if not x["verified"]["open"]:continue
        seg=x["tag"]+"_leaf"+str(x["leaf"]);ref=OUT/seg
        pins=[tuple(map(int,l.split())) for l in ref.with_suffix(".pins").read_text().splitlines()]
        children=list(open_nodes(ref.with_suffix(".tree")));assert len(children)==x["verified"]["open"]
        for k,p in enumerate(children):queue.append((x["tag"],seg+"_"+str(k),pins+p))
    while queue:
        tag,name,pins=queue.popleft()
        assert len({v for v,_ in pins})==len(pins)
        base=D/tag;out=root/name;ass=out.with_suffix(".pins");tree=out.with_suffix(".tree")
        trace="".join(f"{v} {b}\n" for v,b in pins)
        if ass.exists():assert ass.read_text()==trace
        ass.write_text(trace)
        if not tree.exists():
            tmp=out.with_suffix(".partial")
            subprocess.run([str(B/"tree"),str(base),str(tmp),"193","2000000",str(ass)],capture_output=True,check=True)
            tmp.replace(tree)
        counts=replay(base,tree,ass)
        print(json.dumps(dict(tag=tag,key=name,pins=len(pins),verified=counts)),flush=True)
        if counts["witnesses"]:return
        if counts["open"]:
            children=list(open_nodes(tree));assert len(children)==counts["open"]
            for k,p in enumerate(children):queue.append((tag,name+"_"+str(k),pins+p))
if __name__=="__main__":main()
