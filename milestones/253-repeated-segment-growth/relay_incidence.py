"""Identify the relay arms required for two-step growth and compare the small components."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "251-eighty-edge-segments" / "census-72.json"


def main():
    inputs = [HERE/"closure.json", HERE/"thresholds.json", PREVIOUS]
    closure, data, earlier = [json.loads(p.read_bytes()) for p in inputs]
    ids = data["identities"]
    size = [len(closure["paths"][key])-1 for key in ids]
    near = [{i} for i in range(len(ids))]
    for i,row in enumerate(data["direct_upper_triangle"]):
        for j,retained in enumerate(row,i+1):
            if retained>=68:
                near[i].add(j)
                near[j].add(i)
    def bfs(start,minimum):
        distance = {start:0}
        queue = [start]
        for i in queue:
            if size[i]<minimum:continue
            for j in sorted(near[i]-distance.keys()):
                distance[j]=distance[i]+1
                queue.append(j)
        return distance
    root = data["reference_indices"]["20"]
    distance = bfs(root,97)
    relays = [i for i in distance if size[i]>=97]
    additions = {j for j in distance if j not in near[root]}
    contributors = {ids[i]:sorted(ids[j] for j in near[i]&additions) for i in relays if near[i]&additions}
    if (len(relays)!=8 or any(i not in near[root] for i in relays) or len(contributors)!=2
        or sorted(map(len,contributors.values()))!=[9,9]
        or len({x for v in contributors.values() for x in v})!=len(additions) or len(additions)!=18):
        raise ValueError("Two-step family differs")
    old=set(earlier["inherited_ids"])|{r["id"] for r in earlier["new_shapes"]}
    groups={}
    for label in ("20","69","99"):
        visited=bfs(data["reference_indices"][label],96)
        keys={ids[i] for i in visited}
        groups[label]=dict(size=len(keys),shapes=sorted(keys),in_72_catalogue=sorted(keys & old))
    if any(groups[k]["shapes"]!=groups[k]["in_72_catalogue"] for k in ("69","99")):
        raise ValueError("Small component escapes archived endpoint catalogue")
    out=dict(pins={p.name:sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),*inputs]},
             donor20_minimum97=dict(relays=sorted(ids[i] for i in relays),
             distances=Counter(distance.values()),second_step_by_relay=contributors),components=groups)
    (HERE/"relay-incidence.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("Two relays have nine exclusive new terminal arms each. Small components checked against all 28 earlier shapes.")


if __name__=="__main__":main()
