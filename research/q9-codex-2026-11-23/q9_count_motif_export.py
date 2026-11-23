"""Export only the state transitions required to replay one finite count motif."""
import argparse
import hashlib
import json
from pathlib import Path

from q9_window_geometry_dp import read_graph


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("repo",type=Path)
    p.add_argument("output",type=Path)
    p.add_argument("--start",type=int,default=0)
    p.add_argument("--stop",type=int,default=24)
    p.add_argument("--edit",type=int,nargs=2,action="append",default=[])
    a=p.parse_args()
    k7,graph,table,start,counts=read_graph(a.repo)
    from q9_geometry_count_edits import updated_counts
    for position,value in a.edit:
        counts=updated_counts(counts,position,value)
    counts=counts[a.start:a.stop]
    initial=[row[3] for i,row in enumerate(graph.Pr.ext) if graph.alive[i,counts[0]//6]]
    layers=[]
    for index in counts:
        left,right=index//6,index%k7.NT
        words=[word for i,(word,(u,v)) in enumerate(zip(graph.X,graph.XE))
               if graph.alive[u,left] and graph.alive[v,right] and not graph.newcnt[i,index]]
        layers.append(words)
    keys=a.repo/"milestones/25-k7-234/data/keys_best234.json.gz"
    a.output.write_text(json.dumps(dict(dimension=9,initial=initial,layers=layers,
                                       count_codes=counts,edits=a.edit,start=a.start,stop=a.stop,
                                       key_file_sha256=hashlib.sha256(keys.read_bytes()).hexdigest()))+"\n")
