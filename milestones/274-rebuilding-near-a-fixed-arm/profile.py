"""Report the seed geometry, independently checked joins, and overlap with the earlier archives."""
from collections import Counter
from pathlib import Path
from near import HERE,MS,read,write,shape,valid,sources,ArgumentParser,ADJ
import sys
sys.path.insert(0,str(MS/"265-joint-arm-regrowth"))
from exchange import input_paths

def main(name):
    src=sources()[name]
    seed=src["seed"]; other=src["other"]; q=src["reference"]
    valid(seed,8); valid(other,8); valid(q,9)
    assert q in (seed[::-1]+[256+v for v in other], other[::-1]+[256+v for v in seed])
    ds=read(HERE/(name+"-paths.json"))
    archive_file=MS/"272-forty-nine-edge-parents/q8-arms.json"
    import gzip,json
    arms267={w for w,_ in json.loads(gzip.decompress((MS/"267-fixed-arm-extensions/donor-paths.json.gz").read_bytes()))}
    arms270=set(read(MS/"270-optimal-seven-dimensional-arms/q8-primer-arms.json"))
    arms270.update(v["canonical"] for v in read(MS/"270-optimal-seven-dimensional-arms/uga270.json")["paths"].values())
    prior=arms267|arms270|set(read(archive_file))
    lengths={len(s)//2 for s in ds["shapes"]}
    sliced={min(_norm(w[i:i+n]),_norm(w[i:i+n][::-1])).hex() for v in prior for w in (bytes.fromhex(v),) for n in lengths for i in range(len(w)-n+1)}
    end_degrees=[]
    for tip_order in (seed,seed[::-1]):
        tip=tip_order[-1]
        end_degrees.append({str(x):[i for i,v in enumerate(tip_order[:-1]) if (v^x).bit_count()==1] for x in ADJ[tip] if x not in seed})
    profile={}
    for r,lev in ds["levels"].items():
        H=[tuple(map(int,k.split(","))) if k else () for k in lev["nonempty"]]
        involved=sorted({i for q1 in H for i in q1})
        shared=sorted(set.intersection(*(set(q1) for q1 in H))) if H else []
        profile[r]=dict(distinct_omission_patterns=len(H),possible_omitted_indices=involved,indices_omitted_in_every_nonempty_pattern=shared)
    face=HERE/"face274"/name/"summary.json"
    placed=HERE/(name+"-placements.json")
    found={}
    if placed.exists():
        for k,row in read(placed)["roots"].items():
            w=row["best"]; p=w["joined"];valid(p,9)
            assert w["edges"]==len(p)-1
            found[shape(p)]=w
    if face.parent.exists():
        for f in face.parent.glob("queries-*/*.json"):
            for row in read(f)["rows"].values():
                for k,p in row.get("literal_joins",{}).items():
                    n=len(p)-1;valid(p,9);found[shape(p)]=dict(joined=p,edges=n,root=k)
    best=max((w["edges"] for w in found.values()),default=None)
    winners={s:w for s,w in found.items() if w["edges"]==best}
    hits={s:[] for s in winners};counts=Counter()
    if winners:
        for label,p in input_paths():
            counts[len(p)-1]+=1
            for i in range(len(p)-best):
                s=shape(p[i:i+best+1])
                if s in winners:hits[s].append([label,i])
    write(HERE/(name+"-structure.json"),dict(seed_edges=len(seed)-1,source_join_edges=len(q)-1,
          free_tip_obstructions=end_degrees,shapes=len(ds["shapes"]),outside_prior_whole=sum(s not in prior for s in ds["shapes"]),
          outside_prior_intervals=sum(s not in sliced for s in ds["shapes"]),omissions=profile,best_edges=best,
          best_witnesses=winners,earlier_q9_sources=counts,earlier_q9_interval_matches=hits))
    print(name,len(ds["shapes"]),"shapes",sum(s not in sliced for s in ds["shapes"]),"outside earlier intervals; best",best,"with",len(winners),"shapes",flush=True)

from near import norm as _norm
if __name__=="__main__":
    cli=ArgumentParser();cli.add_argument("--source",default="common92");main(cli.parse_args().source)
