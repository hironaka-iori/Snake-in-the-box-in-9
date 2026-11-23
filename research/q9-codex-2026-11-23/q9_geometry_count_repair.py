"""Repair a long local-geometry trace by varying its count sequence."""
import argparse
import json
from pathlib import Path

from q9_geometry_count_edits import decode, updated_counts
from q9_window_geometry_dp import optimize,read_graph


def admissible(counts):
    word=decode(counts[0]//6,6)+[x%6+1 for x in counts]
    return (not any((a==1 and b<4) or (b==1 and a<4) for a,b in zip(word,word[1:]))
            and all(word[i:i+3]!=[2,2,2] for i in range(len(word)-2)))


def search(graph,bad,max_round,max_layer,seeds=()):
    original=graph[-1]
    def probe(counts):
        assert admissible(counts)
        return optimize(*graph[:-1],counts,17,bad,max_layer)
    count=original
    edits=[]
    for position,value in seeds:
        edits.append([position,count[position]%6+1,value])
        count=updated_counts(count,position,value)
    base=probe(count)
    print(json.dumps(dict(edits=edits,**base)),flush=True)
    if base["status"]=="FEASIBLE_LOCAL_RELAXATION":
        return
    for _ in range(max_round):
        if base["status"]!="EXHAUSTED_FIXED_COUNTS":
            break
        at=base["step"]
        best=None
        for position in range(at-1,max(-1,at-7),-1):
            old=count[position]%6+1
            for val in (old+1,old-1,old+2,old-2):
                if not 1<=val<=6:
                    continue
                revised=updated_counts(count,position,val)
                if not admissible(revised):
                    continue
                row=probe(revised)
                if row["status"]=="FEASIBLE_LOCAL_RELAXATION":
                    print(json.dumps(dict(edits=edits+[[position,old,val]],**row)),flush=True)
                    return
                if row["status"]=="EXHAUSTED_FIXED_COUNTS" and row["step"]>at:
                    rank=(row["step"],-abs(val-old))
                    if best is None or rank>best[0]:
                        best=(rank,revised,row,[position,old,val])
                    if row["step"]>=at+20:
                        break
            if best is not None:
                break
        if best is None:
            print(json.dumps(dict(status="NO_GREEDY_REPAIR",step=at,edits=edits)),flush=True)
            return
        _,count,base,edit=best
        edits.append(edit)
        print(json.dumps(dict(edits=edits,**base)),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("repo",type=Path)
    p.add_argument("catalogue",type=Path)
    p.add_argument("--rounds",type=int,default=8)
    p.add_argument("--seed-edit",type=int,nargs=2,action="append",default=[])
    a=p.parse_args()
    bad=frozenset(tuple(map(tuple,k)) for k in json.loads(a.catalogue.read_text())["forbidden_triples"])
    search(read_graph(a.repo),bad,a.rounds,40000,a.seed_edit)
