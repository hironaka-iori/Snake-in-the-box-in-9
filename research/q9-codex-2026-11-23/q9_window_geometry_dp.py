"""Minimum three-cube charge with a fixed count trace and longer local geometry."""
import argparse
from functools import lru_cache
import gzip
import io
import json
import lzma
from pathlib import Path
import resource
import sys

import numpy as np

from q9_window_geometry import canonical
from q9_window11_catalogue import induced


def read_graph(repo):
    milestone=repo/"milestones/28-combined-identities"
    sys.path.insert(0,str(repo/"milestones/25-k7-234"))
    import k7
    with gzip.open(repo/"milestones/25-k7-234/data/keys_best234.json.gz","rt") as f:
        entries=json.load(f)["keys"]
    k7.rss_mb=lambda:resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1048576
    graph=k7.K7(object(),[(tuple(a),tuple(b)) for mark,a,b in entries if mark=="k6"])
    for mark,a,b in entries:
        if mark!="k6":
            graph.add_new((mark,tuple(a),tuple(b)))
    data=milestone/"data"
    table=np.load(io.BytesIO(lzma.decompress((data/"k6_dense_W.npy.xz").read_bytes()))).reshape(-1)
    trace=(data/"full_alpha_w3_nogo_path.txt").read_text().splitlines()
    start=int(trace[0].split()[1])
    counts=[]
    for line in trace[1:214]:
        _,u,_,v,alpha,_=map(int,line.split())
        index=(u%k7.NT)*6+(v%6)
        assert index%k7.NT==v%k7.NT and index%6+1==alpha
        counts.append(index)
    return k7,graph,table,start,counts


def optimize(k7,graph,table,start,counts,width,forbidden,max_layer,all_starts=False):
    if all_starts:
        states={tuple(row[3]):0 for j,row in enumerate(graph.Pr.ext)
                if graph.alive[j,counts[0]//6]}
    else:
        states={tuple(graph.Pr.ext[start//k7.NT][3]):0}
    starting_states=len(states)
    histories=[]
    max_states=starting_states
    @lru_cache(maxsize=None)
    def outgoing(tail):
        result=[]
        for d in range(min(9,1+len(set(tail)))):
            word=tail+(d,)
            if not induced(word):
                continue
            if len(word)>=11:
                triple=tuple(canonical(word[i:i+9]) for i in range(len(word)-11,len(word)-8))
                if triple in forbidden:
                    continue
            edge=graph.xid.get(canonical(word[-9:]))
            if edge is not None:
                result.append((canonical(word[-(width-1):]),edge,d))
        return result
    for step,index in enumerate(counts):
        src,dst=index//6,index%k7.NT
        next_states={}
        backs={}
        for tail,charge in states.items():
            for next_tail,edge,d in outgoing(tail):
                a,b=graph.XE[edge]
                if not graph.alive[a,src] or not graph.alive[b,dst] or graph.newcnt[edge,index]:
                    continue
                vertex=b*k7.NT+dst
                total=charge+int(table[vertex])
                if total<next_states.get(next_tail,10**9):
                    next_states[next_tail]=total
                    backs[next_tail]=(tail,d,vertex)
        if len(next_states)>max_layer:
            return dict(width=width,status="STATE_LIMIT",step=step+1,states=len(next_states))
        if not next_states:
            return dict(width=width,status="EXHAUSTED_FIXED_COUNTS",step=step+1,
                        max_states=max_states,starting_states=starting_states)
        max_states=max(max_states,len(next_states))
        histories.append(backs)
        states=next_states
    tail=min(states,key=states.get)
    score=states[tail]
    replay=[]
    for history in reversed(histories):
        tail,d,vertex=history[tail]
        replay.append((d,vertex))
    word=list(tail)
    for d,vertex in reversed(replay):
        labels=list(dict.fromkeys(word[-(width-1):]))
        word.append(labels[d] if d<len(labels) else next(i for i in range(9) if i not in labels))
        assert canonical(word[-8:])==graph.Pr.ext[vertex//k7.NT][3]
    assert len(word)==len(counts)+8
    assert all(induced(word[i:i+width]) for i in range(len(word)-width+1))
    vertices=[0]
    for d in word:
        vertices.append(vertices[-1]^(1<<d))
    chords=[j-i for j,v in enumerate(vertices) for i,w in enumerate(vertices[:j])
            if j-i>1 and (w^v).bit_count()<2]
    counts_alpha=17+sum(i%6+1 for i in counts)
    max_share=2400*counts_alpha+max(20*20,600)*len(counts)
    return dict(width=width,status="FEASIBLE_LOCAL_RELAXATION",W6=score,
                W6_corrected=score+12*(221-3),A=counts_alpha,max_share=max_share,
                max_states=max_states,starting_states=starting_states,shortest_global_conflict=min(chords) if chords else None,
                word="".join(map(str,word)))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("repo",type=Path)
    p.add_argument("catalogue",type=Path)
    p.add_argument("--width",nargs="+",type=int,default=[11,12,13])
    p.add_argument("--max-layer",type=int,default=25000)
    p.add_argument("--all-starts",action="store_true")
    p.add_argument("--start-offset",type=int,default=0)
    p.add_argument("--stop-offset",type=int,default=213)
    a=p.parse_args()
    bad=frozenset(tuple(map(tuple,row)) for row in json.loads(a.catalogue.read_text())["forbidden_triples"])
    k7,graph,wtable,start,counts=read_graph(a.repo)
    assert not a.start_offset or a.all_starts
    counts=counts[a.start_offset:a.stop_offset]
    assert counts
    for width in a.width:
        print(json.dumps(optimize(k7,graph,wtable,start,counts,width,bad,a.max_layer,a.all_starts)),flush=True)
