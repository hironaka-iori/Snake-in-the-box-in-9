"""Bound the total number of edges in every induced eight-cube linear forest."""
import json
from pathlib import Path
from solve import save


def calculate():
    profile=json.loads(Path("face-component-bound.json").read_bytes())["seven_min_components"]
    def lower(n):return profile.get(str(n),2 if n>51 else int(n>0))
    rows=[]
    for m in range(1,129):
        for c in range(1,m+1):
            if c==1 and m>99:continue
            costs=[]
            for j in range(max(0,m-64),min(m,64)+1):
                a,b=lower(j),lower(m-j)
                costs.append(max(a+b,2*max(a,b)-c))
            if 8*min(costs)<=m+7*c:break
        rows.append(dict(vertices=m,least_components=c,edge_bound=m-c))
    peak=max(r["edge_bound"] for r in rows)
    assert peak==110
    def capacity(c):
        return max((r["vertices"] for r in rows if r["least_components"]<=c),default=0)
    splits=[]
    for k in range(1,26):
        a,b=(k+2)//2,(k+1)//2
        splits.append(dict(crossings=k,components=[a,b],maximum_edges=capacity(a)+capacity(b)-1))
    return dict(upper=peak,possible_equality_sizes=[r["vertices"] for r in rows if r["edge_bound"]==peak],
                occupancies=rows,nine_coordinate_upper_by_crossings=splits)


if __name__=="__main__":
    result=calculate();save(Path("forest-edge-bound.json"),result)
    print(result["upper"],result["possible_equality_sizes"],result["nine_coordinate_upper_by_crossings"][11:13])
