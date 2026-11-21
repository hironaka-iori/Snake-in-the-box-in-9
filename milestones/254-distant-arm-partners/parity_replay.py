"""Independent edge-subset enumeration of the three fixed parity classes."""
from collections import Counter, defaultdict
from itertools import combinations, product
import json
from pathlib import Path
from hashlib import sha256

HERE=Path(__file__).resolve().parent


def spanning_paths(vertices,labels):
    # Once endpoints are specified, the degree quotas force most edge choices.
    edges=sorted(k for k in labels if len(k)==2)
    incident={v:{i for i,e in enumerate(edges) if v in e} for v in vertices}
    def finish(chosen,omitted,quotas,ends):
        while True:
            forced_in=set()
            forced_out=set()
            for v in vertices:
                accepted=incident[v]&chosen
                undecided=incident[v]-chosen-omitted
                left=quotas[v]-len(accepted)
                if left<0 or left>len(undecided):return
                if left==0:forced_out|=undecided
                if left==len(undecided):forced_in|=undecided
            if forced_in & forced_out:return
            if not (forced_in or forced_out):break
            chosen=chosen|forced_in
            omitted=omitted|forced_out
        undecided=set(range(len(edges)))-chosen-omitted
        if undecided:
            e=min(undecided)
            yield from finish(chosen|{e},omitted,quotas,ends)
            yield from finish(chosen,omitted|{e},quotas,ends)
            return
        adjacency=defaultdict(list)
        for i in chosen:
            a,b=edges[i];adjacency[a].append(b);adjacency[b].append(a)
        order=[ends[0]];visited={ends[0]}
        while order[-1]!=ends[1]:
            step=[x for x in adjacency[order[-1]] if x not in visited]
            if len(step)!=1:return
            order.append(step[0]);visited.add(step[0])
        if len(order)==len(vertices):yield tuple(order)
    for ends in combinations(vertices,2):
        quotas={v:1 if v in ends else 2 for v in vertices}
        yield from finish(set(),set(),quotas,ends)


def main():
    file=HERE/"parity-families.json"
    records=json.loads(file.read_bytes())
    closure=HERE.parent/"253-repeated-segment-growth"/"closure.json"
    original=json.loads(closure.read_bytes())["paths"]
    receipts=[]
    for case in records["classes"]:
        sources=[set(original[k][j::2]) for k,j in case["origins"]]
        side=set(case["side"])
        if not sources or any(s!=side for s in sources):raise ValueError("Incorrect source side")
        labels=defaultdict(list)
        for v in range(256):
            nb=tuple(sorted({v^(1<<i) for i in range(8)} & side))
            if len(nb) in (1,2):labels[nb].append(v)
        paths=set();orders=0
        for order in spanning_paths(sorted(side),labels):
            orders+=1
            for steps in product(*(labels[tuple(sorted(e))] for e in zip(order,order[1:]))):
                mid=tuple(u for pair in zip(order,steps) for u in pair)+(order[-1],)
                for a,b in product([(),*((v,) for v in labels[(order[0],)])],
                                   [(),*((v,) for v in labels[(order[-1],)])]):
                    p=a+mid+b
                    if 97<=len(p)<=99:paths.add(min(p,p[::-1]))
        expected={tuple(r["vertices"]) for r in case["paths"]}
        if expected!=paths or orders!=len(case["orders"]):raise ValueError("Enumerations disagree")
        receipts.append(dict(size=len(side),endpoint_pairs=len(side)*(len(side)-1)//2,orders=orders,
                             paths_by_length=Counter(len(p)-1 for p in paths)))
    pins={p.name:sha256(p.read_bytes()).hexdigest() for p in (file,closure,Path(__file__))}
    (HERE/"parity-replay.json").write_text(json.dumps(dict(pins=pins,classes=receipts),indent=2)+"\n",
                                          encoding="utf-8",newline="\n")
    print(receipts)


if __name__=="__main__":main()
