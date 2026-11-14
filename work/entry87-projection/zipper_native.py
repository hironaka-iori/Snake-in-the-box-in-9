"""Evaluate both free layers with exact rooted-path recursion on the same placed anchors."""
import argparse,json,subprocess
from collections import Counter
from pathlib import Path
from zipper import candidates
from solve import defects,save


def solve_many(instances,limit):
    src=[f"{r} {t} {len(graph)} "+" ".join(map(str,sorted(graph))) for r,t,graph in instances]
    cmd=[str(Path("arc-tree.exe").resolve()),str(limit),"52"]
    text=subprocess.run(cmd,input="\n".join(src),capture_output=True,text=True,check=True).stdout
    results=[]
    for (root,tip,allowed),line in zip(instances,text.splitlines(),strict=True):
        best,nodes,complete,*q=map(int,line.split())
        assert len(q)==best and (not q or (q[0]==root and (tip==-1 or q[-1]==tip) and set(q)<=allowed and not defects(q)))
        results.append(dict(best=best,nodes=nodes,complete=bool(complete),q=q))
    return results


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("left",type=int);p.add_argument("third",type=int)
    p.add_argument("--placements",type=int,default=80000);p.add_argument("--limit",type=int,default=350)
    p.add_argument("--offset",type=int,default=0);p.add_argument("--nodes",type=int,default=90000)
    p.add_argument("--correlated",action="store_true");p.add_argument("--exe",default="zipper-correlated.exe");a=p.parse_args()
    # All domains in a three-cube can be compared against direct simple-path
    # enumeration. Sample both free endpoints and requested fixed tips.
    controls=[]
    for bits in range(1,256,2):
        allowed={v for v in range(8) if bits>>v&1}
        for tip in (-1,max(allowed)):controls.append((0,tip,allowed))
    def brute(r,t,g):
        def dfs(q):
            cur=q[-1];ans=len(q) if t==-1 or cur==t else 0
            if cur==t:return ans
            for w in g-set(q):
                if (w^cur).bit_count()==1 and all((w^v).bit_count()>1 for v in q[:-1]):ans=max(ans,dfs(q+[w]))
            return ans
        return dfs([r])
    for s,(r,t,g) in zip(solve_many(controls,100000),controls):assert s["complete"] and s["best"]==brute(r,t,g)
    summary,pairs=candidates(a);pairs=pairs[a.offset:a.offset+a.limit]
    rows=[];maxlen=0;bestq=None
    fn=Path(f"zipper-native-{a.left}-{a.third}-{a.placements}-{a.offset}-{a.limit}-{a.nodes}-{int(a.correlated)}.json")
    for start in range(0,len(pairs),25):
        batch=pairs[start:start+25];instances=[]
        for upper,A,C in batch:
            remain=set(range(128))-(set(A)|set(C))
            instances.extend([(A[-1],C[0],remain|{A[-1],C[0]}),(C[-1],-1,remain|{C[-1]})])
        answers=solve_many(instances,a.nodes)
        for j,(upper,A,C) in enumerate(batch):
            B,D=answers[2*j:2*j+2];q=None
            if B["q"] and D["q"]:
                q=[*A,*[v|128 for v in B["q"]],*[v|384 for v in C],*[v|256 for v in D["q"]]]
                assert not defects(q)
                if len(q)>maxlen:maxlen=len(q);bestq=q
            rows.append(dict(left=A,third=C,upper=upper,B=B,D=D,edges=len(q)-1 if q else None))
        save(fn,dict(placements=summary,best_edges=maxlen-1,best_path=bestq,rows=rows))
        if maxlen>=193:break
    print(len(rows),maxlen-1,sum(r["B"]["complete"] and r["D"]["complete"] for r in rows),flush=True)
