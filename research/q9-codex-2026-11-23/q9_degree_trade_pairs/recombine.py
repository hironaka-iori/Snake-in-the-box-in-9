"""Independently audit logged component sizes, combine edits, then freely assign the union of observed edit sites."""
from collections import Counter, defaultdict
from pathlib import Path
from itertools import combinations
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from q9_intact_bank_search import word_path,verify,search
D=Path(__file__).resolve().parent
N=[{v^(1<<d) for d in range(9)} for v in range(512)]
def component_path(S,a=None,b=None):
    ds={v:len(N[v]&S) for v in S}
    ends=[v for v,d in ds.items() if d==1]
    if len(ends)!=2 or any(x not in (1,2) for x in ds.values()):return []
    if a is not None:assert set(ends)=={a,b}
    p=[ends[0]];prev=-1
    while p[-1]!=ends[1]:
        v=p[-1];u,=(N[v]&S)-{prev};prev=v;p.append(u)
    assert verify(p)
    return p
def main():
    words=(D/"remaining.words").read_text().split()
    control=(D/"control.log").read_text().splitlines()
    passed=set()
    for row in control:
        z=row.split()
        if z[0]=="T":
            i,a,b,n,m,*sw=map(int,z[1:]);p=word_path(words[i]);s=set(p[:-2])^set(sw)
            if s==set(p) and len(component_path(s,a,b))==m==n==192:passed.add(i)
    assert len(passed)==22
    families=defaultdict(set)
    finished=set()
    for row in (D/sys.argv[1]).read_text().splitlines():
        z=row.split()
        if z[0]=="D":finished.add(int(z[1]));continue
        i,a,b,n,m,*vs=map(int,z[1:]);p=word_path(words[i]);sw=frozenset(vs);s=set(p)^sw
        assert len(sw)==len(vs) and len(s)==n and len(component_path(s,a,b))==m
        families[i].add(sw)
    for i in sorted(finished):
        p=word_path(words[i]);s=set(p);moves=families[i];region=set.union(set(),*moves)
        counts=Counter();best=0
        for x,y in combinations(moves,2):
            mask=x^y
            size=192+len(mask)-2*len(mask&s)
            if size<192:continue
            q=component_path(s^mask);counts["pairs_at_least_192_points"]+=1
            if q:counts["degree_compatible"]+=1;best=max(best,len(q)-1)
            if len(q)>=193:
                print(json.dumps(dict(id=i,source="pair",vertices=q)),flush=True);return
        for goal in (191,192,193):
            opts=search(p,goal,60000,s,(),goal==191,omit=region,forbid=set(range(512))-(s|region))
            if goal==191:assert any(z["status"]=="FOUND" for z in opts)
            print(json.dumps(dict(id=i,moves=len(moves),released=len(region),released_old=len(region&s),pair_counts=counts,pair_best=best,goal=goal,results=opts)),flush=True)
            if goal>=192 and any(z["status"]=="FOUND" for z in opts):return
if __name__=="__main__":main()
