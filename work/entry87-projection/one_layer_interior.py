"""Make an interior bridge in the opposite layer, then rebuild both neighbouring layers."""
import argparse
from pathlib import Path
from joint_four_repair import sources
from opposite_anchors import arrangements
from one_layer_core import N,study
from solve import defects,save


def bridges(a,c,width):
    out={};nodes=0
    oldcores={tuple(c[i:i+len(c)-15]) for i in range(16)}
    for i in range(1,len(c)-width-1):
        prefix=c[:i+1];suffix=c[i+width:];target=suffix[0]
        fixed=set(prefix+suffix);inside=set(prefix);route=prefix.copy()
        def grow(left):
            nonlocal nodes
            nodes+=1;v=route[-1]
            distance=(v^target).bit_count()
            if distance>left or (distance-left)%2:return
            if distance==1:
                if left!=1 or N[target]&inside!={v}:return
                q=tuple(route+suffix)
                if any(q[j:j+len(c)-15] in oldcores for j in range(len(q)-(len(c)-15)+1)):return
                assert not defects(q);out[q]=None;return
            for w in N[v]-fixed-inside-{a[-1]}:
                if N[w]&inside!={v} or N[w]&set(suffix[1:]):continue
                inside.add(w);route.append(w);grow(left-1);route.pop();inside.remove(w)
        for length in (width-2,width,width+2,width+4):
            if 40<=len(c)+length-width<=51:grow(length)
    return out,nodes


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--width",type=int,default=10);p.add_argument("--keep",type=int,default=1000)
    p.add_argument("--nodes",type=int,default=500000);a=p.parse_args();rows=[]
    for i,(_,axes,q) in enumerate(sources()):
        for orientation,paths in enumerate(arrangements(q)):
            idx=2*i+orientation
            if not a.first<=idx<a.stop:continue
            data=bridges(paths[0],paths[2],a.width)
            r=study(paths,0,a.keep,a.nodes,True,data)
            rows.append(dict(index=idx,source=i,axes=axes,**r))
            save(Path(f"interior-layer-{a.first}-{a.stop}-{a.width}-{a.keep}-{a.nodes}.json"),rows)
            if r["best_edges"]>=192:break
        if rows and rows[-1]["best_edges"]>=192:break
    print(len(rows),sum(r["candidates"] for r in rows),max((r["best_edges"] for r in rows),default=0))
