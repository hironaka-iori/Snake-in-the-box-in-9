"""Enumerate the first three compatible Q7 bank paths; solve the final layer without a shape restriction."""
import argparse,json
from collections import Counter
from pathlib import Path
from four_layer_bank import menus
from four_layer_lengths import profiles
from zipper import arm
from solve import defects,save


def trie(words):
    root={}
    for word in words:
        node=root
        for c in word:node=node.setdefault(c-48,{})
        node[-1]=True
    return root


def placements(tree,previous):
    first=previous[-1];forbidden=set(previous);image=[];used=set()
    def visit(node,q):
        if -1 in node:yield tuple(q)
        for key,child in node.items():
            if key==-1:continue
            if key<len(image):
                new=q[-1]^(1<<image[key])
                if new not in forbidden:yield from visit(child,q+[new])
            else:
                assert key==len(image)
                for b in range(7):
                    if b in used:continue
                    new=q[-1]^(1<<b)
                    if new in forbidden:continue
                    used.add(b);image.append(b)
                    yield from visit(child,q+[new])
                    image.pop();used.remove(b)
    yield from visit(tree,[first])


def vert(word):
    q=[0]
    for c in word:q.append(q[-1]^(1<<(c-48)))
    return tuple(q)


def bound(allowed,root):
    todo=[root];used={root}
    while todo:
        v=todo.pop();new={v^(1<<b) for b in range(7)}&allowed-used;used|=new;todo.extend(new)
    nsame=sum((v^root).bit_count()%2==0 for v in used)
    return min(2*nsame,2*(len(used)-nsame)+1)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--seconds",type=float,default=2);a=p.parse_args()
    bank={s.encode():v for s,v in json.loads(Path("highdim-seven-39.json").read_text())["forms"].items()}
    allmenus={n:menus(bank,n) for n in range(40,52)}
    tries={n:trie(m) for n,m in allmenus.items()}
    orders=sorted({s for x in profiles() for s in (x,x[::-1])},key=lambda s:(-s[0],-s[1],-s[2],s[3]))
    assert len(orders)==364
    allv=set(range(128));memo={};rows=[];best=0;casebest=None
    out=Path(f"free-last-{a.first}-{a.stop}-{a.seconds}.json")
    for j in range(a.first,min(a.stop,len(orders))):
        s=orders[j];counts=Counter();open_cases=[]
        for A in map(vert,allmenus[s[0]]):
            for B in placements(tries[s[1]],A):
                counts["pairs"]+=1
                for C in placements(tries[s[2]],B):
                    counts["triples"]+=1
                    root=C[-1]
                    if root in A:counts["occupied join"]+=1;continue
                    allowed=(allv-(set(A)|set(C)))|{root}
                    ub=bound(allowed,root)
                    if ub<s[3]:counts["parity/component"]+=1;continue
                    counts["requests"]+=1
                    key=tuple(sorted(x^root for x in allowed))
                    if key not in memo:memo[key]=arm(set(key),0,None,a.seconds,1)
                    hit=memo[key];d=[x^root for x in hit.get("path",[])]
                    if hit["upper"]<s[3]:counts["exact bound"]+=1
                    elif len(d)<s[3]:open_cases.append(dict(A=A,B=B,C=C,upper=hit["upper"],lower=len(d)))
                    if d:
                        q=[*A,*[v|128 for v in B],*[v|384 for v in C],*[v|256 for v in d]]
                        assert not defects(q)
                        if len(q)-1>best:
                            best=len(q)-1;casebest=q;print("best",j,best,flush=True)
                    if best>=192:break
                if best>=192:break
            if best>=192:break
        rows.append(dict(index=j,sizes=s,counts=counts,open=open_cases))
        save(out,dict(best=best,vertices=casebest,profiles=rows,optimized_domains=len(memo)))
        if best>=192:break
    print("done",len(rows),best,len(memo),flush=True)
