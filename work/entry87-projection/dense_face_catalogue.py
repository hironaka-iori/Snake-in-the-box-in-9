"""Attach half-full parent classes to unmarked seven-faces and test their possible completions."""
import argparse
import json
from collections import Counter,deque
from pathlib import Path
from dense_rigidity import next_sites
from seven_deletions import generators
from dense_eight import facet_completion
from forest_orbit_weights import bound
from solve import save


def parents():
    by_site=[0]*128;kinds=[];gens=list(generators())
    for row in json.loads(Path("seven-deletion-classes.json").read_bytes())["64"]:
        m=sum(1<<v for v in row["forest"]);orbit={m};q=deque([m])
        while q:
            x=q.popleft()
            for _,g in gens:
                y=g(x)
                if y not in orbit:orbit.add(y);q.append(y)
        assert len(orbit)==row["labelled"]
        for x in sorted(orbit):
            flag=1<<len(kinds);kinds.append(row["full_class"])
            while x:
                v=(x&-x).bit_length()-1;x&=x-1;by_site[v]|=flag
    assert len(kinds)==9424
    return kinds,by_site


def list_classes(n,with_parent=False):
    kinds,by_site=parents();rows=[]
    for line in Path(f"seven-face-classes-{n}.txt").read_text().splitlines():
        a,b,c,weight,stab=map(int,line.split());mask=a|(b<<64)
        assert weight*stab==645120 and mask.bit_count()==n
        possible=(1<<len(kinds))-1;V=[]
        while mask:
            v=(mask&-mask).bit_length()-1;mask&=mask-1;possible&=by_site[v];V.append(v)
        assert possible.bit_count()<=1
        fi=kinds[possible.bit_length()-1] if possible else -1
        row=dict(forest=V,full_class=fi,labelled=weight,components=c)
        if with_parent and possible:
            row["parent_mask"]=sum(1<<v for v,flags in enumerate(by_site) if flags&possible)
            assert row["parent_mask"].bit_count()==64
        rows.append(row)
    return rows


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("n",type=int);p.add_argument("--start",type=int,default=0)
    p.add_argument("--stop",type=int,default=0);p.add_argument("--group",type=int)
    p.add_argument("--budget",type=int,default=750000);p.add_argument("--checker",type=Path)
    p.add_argument("--only-weights",action="store_true");a=p.parse_args()
    rows=list_classes(a.n);template={}
    for j in range(6):
        f=Path(f"variable-facet-{j}-{a.n}-3.json")
        if f.exists():template[j]=json.loads(f.read_bytes())["edge_upper"]
    if not a.stop:
        totals=Counter();nums=Counter();maximal=Counter()
        for r in rows:
            j=r["full_class"];nums[j]+=1;totals[j]+=r["labelled"]
            if j<0 and not next_sites(set(r["forest"])):maximal[j]+=r["labelled"]
        save(Path(f"dense-orbit-profile-{a.n}.json"),dict(classes=nums,labels=totals,maximal=maximal))
        print(dict(nums),dict(maximal));raise SystemExit
    for i in range(a.start,min(a.stop,len(rows))):
        r=rows[i];j=r["full_class"]
        if (a.group is not None and j!=a.group) or template.get(j,104)<104:continue
        weight=Path(f"individual-weight-{a.n}-{i}.json")
        if weight.exists():
            proof=json.loads(weight.read_bytes())
        else:
            proof=bound(set(r["forest"]),117)
            save(weight,proof)
        assert proof["fixed"]==r["forest"]
        if proof["max_edges"]<104 or a.only_weights:continue
        tag=f"individual-facet-{a.n}-{i}-{a.budget}"+("-checked" if a.checker else "")
        if Path(tag+".json").exists():continue
        facet_completion(r["forest"],117,13,a.budget,tag,a.checker.resolve() if a.checker else None,True)
