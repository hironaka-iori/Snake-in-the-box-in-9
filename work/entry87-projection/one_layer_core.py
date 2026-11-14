"""Keep one whole Q7 layer and regrow the opposite layer around a contiguous core."""
import argparse,heapq,json
from pathlib import Path
from collections import Counter
from joint_four_repair import sources
from opposite_anchors import arrangements
from solve import save,defects
from zipper_native import solve_many

N=[{v^(1<<j) for j in range(7)} for v in range(128)]


def mutations(A,original,trim):
    # Remove trim vertices in total, split arbitrarily between both ends.
    # Each result contains a literal, oriented original subpath at this placement.
    a=A[-1];aset=set(A);low=max(40,193-len(A)-102)
    bank={};examined=0
    for left in range(trim+1):
        fixed=original[left:len(original)-trim+left]
        if a in fixed:continue
        prefix=set(fixed);occupied=prefix.copy()
        def extend(head,previous,arm,done):
            nonlocal examined
            examined+=1;done(arm)
            if len(occupied)>=51:return
            for y in sorted(N[head]-occupied-{a}):
                if (N[y]&occupied)!={head}:continue
                occupied.add(y);arm.append(y);extend(y,head,arm,done);arm.pop();occupied.remove(y)
        def first(arm1):
            start=arm1[-1] if arm1 else fixed[0]
            if start in aset:return
            def last(arm2):
                finish=arm2[-1] if arm2 else fixed[-1]
                if finish in aset or len(occupied)<low:return
                q=tuple(arm1[::-1]+fixed+arm2)
                bank[q]=None
            extend(fixed[-1],None,[],last)
        extend(fixed[0],None,[],first)
    return bank,examined


def parity_bound(domain,root,tip=None):
    seen={root};front=[root]
    while front:
        new=N[front.pop()]&domain-seen;seen|=new;front.extend(new)
    if tip is not None and tip not in seen:return 0
    n=sum((v^root).bit_count()%2==0 for v in seen);m=len(seen)-n
    if tip is None:return min(2*n,2*m+1,51)
    return min(51,2*min(n,m) if (root^tip).bit_count()%2 else 2*min(n-1,m)+1)


def study(paths,trim,limit,nodes,write_index=False,candidate_data=None):
    A,B0,C0,D0=paths;allv=set(range(128));ac=set(A);bset=set(B0);dset=set(D0)
    forms,generation=candidate_data if candidate_data is not None else mutations(A,C0,trim)
    if candidate_data is None:assert tuple(C0) in forms
    selected=[];viable=0
    for order,C in enumerate(forms):
        u=allv-ac-set(C);lb={A[-1],C[0]}|u;ld={C[-1]}|u
        maxB=parity_bound(lb,A[-1],C[0]);maxD=parity_bound(ld,C[-1])
        if len(A)+len(C)+maxB+maxD<193:continue
        viable+=1
        # Favor candidates for which both actual old partners still nearly fit.
        loss=len(bset-lb)+len(dset-ld)+(B0[-1]^C[0]).bit_count()+(D0[0]^C[-1]).bit_count()
        score=(-loss,len(C),len(set(C)&ac),-order)
        item=(score,C,maxB,maxD)
        if len(selected)<limit:heapq.heappush(selected,item)
        elif item[0]>selected[0][0]:heapq.heapreplace(selected,item)
    selected.sort(reverse=True);instances=[]
    for _,C,_,_ in selected:
        u=allv-ac-set(C);instances.extend(((A[-1],C[0],u|{A[-1],C[0]}),(C[-1],-1,u|{C[-1]})))
    results=solve_many(instances,nodes);best=191;bestq=None;resolved=0;open_cases=[]
    for j,(_,C,maxB,maxD) in enumerate(selected):
        b,d=results[2*j:2*j+2];B=b['q'];D=d['q']
        if B0[-1]==C[0] and bset<=instances[2*j][2] and len(B0)>len(B):B=B0
        if D0[0]==C[-1] and dset<=instances[2*j+1][2] and len(D0)>len(D):D=D0
        upperB=b['best'] if b['complete'] else maxB
        upperD=d['best'] if d['complete'] else maxD
        if len(A)+len(C)+upperB+upperD<193:resolved+=1
        elif write_index:
            open_cases.append(dict(third=C,middle_upper=upperB,last_upper=upperD,
                                   middle_lower=len(B),last_lower=len(D),required_sum=193-len(A)-len(C)))
        if B and D and len(A)+len(B)+len(C)+len(D)>best:
            q=A+[v|128 for v in B]+[v|384 for v in C]+[v|256 for v in D]
            assert not defects(q);best=len(q);bestq=q
    row=dict(candidates=len(forms),generation=generation,capacity_survivors=viable,selected=len(selected),
             excluded_selected=resolved,best_edges=best-1,best_path=bestq)
    if write_index:row.update(first=A,open_cases=open_cases)
    return row


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--trim",type=int,default=4);p.add_argument("--keep",type=int,default=150)
    p.add_argument("--nodes",type=int,default=140000);p.add_argument("--index",action="store_true");a=p.parse_args();rows=[]
    for i,(_,axes,q) in enumerate(sources()):
        for orientation,paths in enumerate(arrangements(q)):
            idx=2*i+orientation
            if not a.first<=idx<a.stop:continue
            r=study(paths,a.trim,a.keep,a.nodes,a.index);rows.append(dict(index=idx,source=i,axes=axes,**r))
            suffix="-index" if a.index else ""
            save(Path(f"one-layer-core-{a.first}-{a.stop}-{a.trim}-{a.keep}-{a.nodes}{suffix}.json"),rows)
            if r["best_edges"]>=192:break
        if rows and rows[-1]["best_edges"]>=192:break
    print(len(rows),max((r["best_edges"] for r in rows),default=0),flush=True)
