"""Check complete branch coverage before counting a parent family as excluded."""
from collections import Counter,defaultdict
from itertools import product
from pathlib import Path
import json


def read(name):
    return [json.loads(l) for l in Path(name+".jsonl").read_text().splitlines()]


def index(rows,key):
    result={key(r):r[0] for r in rows}
    assert len(result)==len(rows)
    return result


def merge(parent,child,allowed):
    required={(k,b) for k,s in parent.items() if s=="UNKNOWN" for b in allowed(k)}
    assert set(child)==required
    for key,s in list(parent.items()):
        if s=="UNKNOWN":
            results={child[key,b] for b in allowed(key)}
            assert results and results<={"UNSAT","UNKNOWN","FOUND"}
            parent[key]="FOUND" if "FOUND" in results else ("UNKNOWN" if "UNKNOWN" in results else "UNSAT")


def main():
    endpoint="q9_flexible_endpoint_relative_192.jsonl"
    old=json.loads(Path("q9_flexible_frontier.json").read_text())["unresolved"][endpoint]
    single={tuple(k):"UNKNOWN" for k in old}
    split=index(read("q9_one_end_split_192"),lambda r:(tuple(r[1][:2]),r[1][2]))
    last=read("q9_one_end_final_192")
    def options(branch):
        (raw,_),b=branch
        q=bytes.fromhex(raw)
        q=q[:-1]+bytes([q[-2]^(1<<b)])
        positions={r[2] for r in last if tuple(r[1][:2])==branch[0] and r[1][2]==b}
        pos,=positions
        neighbors=[q[j] for j in (pos-1,pos+1) if 0<=j<len(q)]
        return [k for k in range(7) if all(((neighbors[0]^(1<<k))^v).bit_count()==1 for v in neighbors)]
    merge(split,index(last,lambda r:((tuple(r[1][:2]),r[1][2]),r[3])),options)
    merge(single,split,lambda k:range(7))
    two=index(read("q9_two_ends_192"),lambda r:tuple(r[1]))
    first=index(read("q9_two_end_split_192"),lambda r:(tuple(r[1]),r[3]))
    second=index(read("q9_two_end_directions_192"),lambda r:((tuple(r[1]),r[2]),r[3]))
    refinements=read("q9_two_end_refined_192")
    refined=index(refinements,lambda r:((tuple(r[1]),r[2]),r[3]))
    assert set(refined)=={k for k,s in second.items() if s=="UNKNOWN"}
    for r in refinements:
        if r[0]=="UNSAT": assert r[4] and set(r[4])=={"UNSAT"}
    second.update(refined)
    merge(first,second,lambda k:range(7))
    merge(two,first,lambda k:range(7))
    rev=index(read("q9_projected_reversal_192"),lambda r:r[4])
    seeds=read("q9_reversal_191_seeds")
    assert len(seeds)==1500 or any(r[-1] for r in seeds)
    control,=read("q9_two_ends_control")
    w=control[-1];assert len(w)==192 and len(set(w))==192 and all(0<=x<512 for x in w)
    assert all(((x^w[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(w) for j in range(i+1,len(w)))
    print(json.dumps({"last_single_end_cases":dict(Counter(single.values())),
                      "two_ends":dict(Counter(two.values())),
                      "two_ends_unresolved":[k for k,s in two.items() if s=="UNKNOWN"],
                      "reversed_segments":dict(Counter(rev.values())),
                      "reversal_seed_search":dict(Counter(r[0] for r in seeds)),
                      "new_191_seeds":sum(int(r[2]) for r in seeds),
                      "extended_witnesses":[r[-1] for r in seeds if r[-1]]},indent=2))


if __name__=="__main__":main()
