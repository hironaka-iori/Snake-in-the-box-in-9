"""Restrict an induced path between anchors to its biconnected blocks."""
from collections import defaultdict
from search_q9_wynn_plateau import NB


def anchor_blocks(verts,a,b):
    children={};disc={};low={};stack=[];blocks=[]
    def visit(x,parent):
        disc[x]=low[x]=len(disc)+1
        for y in NB[x]:
            if y not in verts or y==parent:continue
            if y not in disc:
                stack.append((x,y));visit(y,x);low[x]=min(low[x],low[y])
                if low[y]>=disc[x]:
                    block=set()
                    while True:
                        edge=stack.pop();block.update(edge)
                        if edge==(x,y):break
                    blocks.append(block)
            elif disc[y]<disc[x]:
                stack.append((x,y));low[x]=min(low[x],disc[y])
    visit(a,None)
    if b not in disc:return []
    tree=defaultdict(list)
    for i,c in enumerate(blocks):
        block_node=512+i
        for x in c:tree[x].append(block_node);tree[block_node].append(x)
    pred={a:None};q=[a]
    for x in q:
        if x==b:break
        for y in tree[x]:
            if y not in pred:pred[y]=x;q.append(y)
    route=[];cur=b
    while cur!=a:
        bn=pred[cur];prev=pred[bn];route.append((blocks[bn-512],prev,cur));cur=prev
    return route[::-1]


def longest_small(block,a,b):
    best=[];path=[a];used={a}
    def extend(x):
        nonlocal best
        if x==b:
            if len(path)>len(best):best=path[:]
            return
        for y in NB[x]:
            if y in block and y not in used and sum(u in used for u in NB[y])==1:
                used.add(y);path.append(y);extend(y);path.pop();used.remove(y)
    extend(a)
    assert best
    return best


def simplify(verts,a,b):
    allowed=set();forced=set();large=[];total_upper=0
    for block,u,v in anchor_blocks(verts,a,b):
        if (u^v).bit_count()==1:
            chosen={u,v}
        elif len(block)<=15:
            chosen=set(longest_small(block,u,v))
        else:
            chosen=None
        if chosen is not None:
            allowed.update(chosen);forced.update(chosen);total_upper+=len(chosen)-1
        else:
            allowed.update(block);forced.update((u,v));large.append((block,u,v))
            bins=[sum(x.bit_count()%2==c for x in block) for c in (0,1)]
            c=u.bit_count()%2
            total_upper+= 2*min(bins)-1 if (u^v).bit_count()%2 else 2*min(bins[c]-1,bins[1-c])
    return allowed,forced,large,total_upper
