"""Make an interior bridge in the opposite layer, then rebuild both neighbouring layers."""
import argparse
from pathlib import Path
from joint_four_repair import sources
from opposite_anchors import arrangements
from one_layer_core import N,mutations,study
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
    p.add_argument("--nodes",type=int,default=500000)
    p.add_argument("--end-trim",type=int,default=0);a=p.parse_args();rows=[]
    for i,(_,axes,q) in enumerate(sources()):
        for orientation,paths in enumerate(arrangements(q)):
            idx=2*i+orientation
            if not a.first<=idx<a.stop:continue
            data=bridges(paths[0],paths[2],a.width)
            if a.end_trim:
                interior,data_nodes=data;combined={};base=paths[2]
                oldcores={tuple(base[j:j+len(base)-15]) for j in range(16)}
                for c in interior:
                    changed,visited=mutations(paths[0],list(c),a.end_trim);data_nodes+=visited
                    for qnew in changed:
                        if qnew in interior:continue
                        if any(qnew[j:j+len(base)-15] in oldcores for j in range(len(qnew)-len(base)+16)):continue
                        combined[qnew]=None
                data=combined,data_nodes
            r=study(paths,0,a.keep,a.nodes,True,data)
            rows.append(dict(index=idx,source=i,axes=axes,**r))
            suffix=f"-ends{a.end_trim}" if a.end_trim else ""
            save(Path(f"interior-layer-{a.first}-{a.stop}-{a.width}-{a.keep}-{a.nodes}{suffix}.json"),rows)
            if r["best_edges"]>=192:break
        if rows and rows[-1]["best_edges"]>=192:break
    print(len(rows),sum(r["candidates"] for r in rows),max((r["best_edges"] for r in rows),default=0))
