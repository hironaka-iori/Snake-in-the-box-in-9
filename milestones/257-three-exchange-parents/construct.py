"""Place every donor prefix of the specified length and exhaust all its continuations."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"251-eighty-edge-segments"))
import bank_capacity as bank

ADJ=[sum(1<<(v^(1<<axis)) for axis in range(8)) for v in range(256)]
NEIGHBOURS=[[v^(1<<axis) for axis in range(8)] for v in range(256)]


def load(f):
    return json.loads(f.read_bytes())


def follow(start, rooted_parent):
    """Grow every legal continuation of an already placed prefix, choosing its free endpoint."""
    blocked=sum(1<<v for v in set(rooted_parent[1:])|set(start))
    for v in start[:-1]:
        blocked |= ADJ[v]
    best=list(start)
    nodes=0
    def dfs(path,ban):
        nonlocal nodes,best
        nodes+=1
        if len(path)>len(best): best=path.copy()
        tip=path[-1]
        choices=ADJ[tip]&~ban
        while choices:
            bit=choices & -choices
            choices^=bit
            path.append(bit.bit_length()-1)
            dfs(path,ban|ADJ[tip]|bit)
            path.pop()
    dfs(list(start),blocked)
    return best,nodes


def replay_tail(prefix, parent):
    occupied=set(prefix)
    forbidden=set(parent[1:])
    counts=[0]*256
    for u in prefix:
        for v in NEIGHBOURS[u]:
            counts[v]+=1
    def visit(tip, length):
        work,best=1,length
        for v in NEIGHBOURS[tip]:
            if v in occupied or v in forbidden or counts[v]!=1:
                continue
            occupied.add(v)
            for u in NEIGHBOURS[v]: counts[u]+=1
            child,depth=visit(v,length+1)
            for u in NEIGHBOURS[v]: counts[u]-=1
            occupied.remove(v)
            work+=child
            best=max(best,depth)
        return work,best
    return visit(prefix[-1],len(prefix)-1)


def main():
    core_edges=int(sys.argv[1]) if len(sys.argv)>1 else 72
    if not 51<=core_edges<=95: raise ValueError("Every retained word must use all eight coordinates")
    prev=MS/"255-parity-exchange-arms"
    files=[prev/"partner-pool.json",prev/"constructive.json",MS/"248-rooted-arm-capacity/attainers.json",
           HERE/"shell-distant.json",HERE/"two-exchange-comparison/shell-distant.json"]
    pool,positive,attaining,outer,inner=map(load,files)
    donor_paths=list(pool["shapes"].values())+[r["partner"] for r in positive["cases"].values()]
    donor_paths.extend(d["vertices"] for d in positive["donors"])
    donor_paths.extend(p["path"] for r in attaining["records"] for p in r["paths"])
    # A translated, permuted or reversed copy generates the same set of rooted prefixes.
    sys.path.insert(0,str(MS/"252-shorter-reference-segments"))
    from replay_core import word as shape_word
    donors=list({shape_word(p):p for p in donor_paths}.values())
    words,origins=bank.donor_suffixes(donors)
    cores={}
    for word in words:
        if len(word)<core_edges: continue
        core=word[:core_edges]
        if core in cores: continue
        v=0
        seq=[0]
        for a in core:
            v^=1<<a
            seq.append(v)
        cores[core]=bytes(seq)
    images=list(bank.permutation_images())
    cases={}
    for key,p in sorted((outer["shapes"]|inner["shapes"]).items()):
        for end,order in enumerate((p,p[::-1])):
            parent=[v^order[0] for v in order]
            allowed=bank.allowed_maps(parent,images)
            longest=bank.longest(words,allowed)
            candidate=bank.make_witness(donors,origins[longest[1]],longest,parent)
            best=None
            count=nodes=0
            for core,vertices in cores.items():
                maps=bank.ALL_MAPS
                for v in reversed(vertices[1:]):
                    maps &= allowed[v]
                    if not maps: break
                while maps:
                    bit=maps & -maps
                    maps ^=bit
                    rank=bit.bit_length()-1
                    # Every Q8 arm longer than 50 uses all eight directions since a(7)=50.
                    # Thus no placement is repeated once its normalized direction word is fixed.
                    if len(set(core))!=8: raise ValueError("Unrepresented permutation multiplicity")
                    start=[images[rank][v] for v in vertices]
                    if set(start)&set(parent)!={0}: raise ValueError("Unintended projected intersection")
                    partner,work=follow(start,parent)
                    if replay_tail(start,parent)!=(work,len(partner)-1):
                        raise ValueError("Counter-based tail replay disagrees")
                    count+=1
                    nodes+=work
                    if best is None or len(partner)>len(best): best=partner
            if (best is None)!=(candidate["partner_edges"]<core_edges):
                raise ValueError("Core occurrence disagrees with independent longest donor scan")
            if best is not None and len(best)-1<candidate["partner_edges"]: raise ValueError("Continuation lost donor")
            result=best if best is not None else candidate["partner"]
            joined=parent[::-1]+[256+v for v in result]
            pairs=bank.check_path(joined,9)
            cases[key+":"+str(end)]=dict(shape=key,end=end,original_root=order[0],
                    rooted_cores=count,continuation_nodes=nodes,entire_donor_bank_max=candidate["partner_edges"],
                    unrestricted_tail_max=len(best)-1 if best else None,partner=result,joined=joined,
                    joined_edges=len(joined)-1,all_pairs=pairs)
    output=dict(core_edges=core_edges,donor_shapes=len(donors),rooted_core_words=len(cores),cases=cases,
                parents=len(cases)//2,ordered_placements=sum(r["rooted_cores"] for r in cases.values()),
                continuation_nodes=sum(r["continuation_nodes"] for r in cases.values()),
                best_join=max(r["joined_edges"] for r in cases.values()),
                inputs={f.relative_to(MS).as_posix():sha256(f.read_bytes()).hexdigest()
                        for f in [*files,Path(__file__),Path(bank.__file__)]})
    destination=HERE/("constructed.json" if core_edges==72 else "constructed-"+str(core_edges)+".json")
    destination.write_text(json.dumps(output,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print({k:v for k,v in output.items() if k not in ("inputs","cases")})

if __name__=="__main__": main()
