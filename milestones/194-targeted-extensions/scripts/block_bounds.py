"""Necessary induced-path length bound from terminal biconnected blocks."""
def bits(mask):
    while mask:
        low=mask&-mask;mask^=low;yield low.bit_length()-1

def terminal_blocks(mask,u,v,neighbours):
    discovery={};low={};stack=[];blocks=[];clock=0
    def dfs(x,parent):
        nonlocal clock
        discovery[x]=low[x]=clock;clock+=1
        for y in bits(neighbours[x]&mask):
            if y not in discovery:
                stack.append((x,y));dfs(y,x);low[x]=min(low[x],low[y])
                if low[y]>=discovery[x]:
                    vertices=set()
                    while True:
                        edge=stack.pop();vertices.update(edge)
                        if edge==(x,y):break
                    blocks.append(vertices)
            elif y!=parent and discovery[y]<discovery[x]:
                stack.append((x,y));low[x]=min(low[x],discovery[y])
    dfs(u,None)
    if v not in discovery:return dict(upper_edges=-1,mask=0,blocks=[])
    assert not stack
    tree={x:[] for x in discovery}
    for i,block in enumerate(blocks):
        node=512+i;tree[node]=list(block)
        for x in block:tree[x].append(node)
    parent={u:None};queue=[u]
    for x in queue:
        for y in tree[x]:
            if y==parent[x]:continue
            assert y not in parent, 'Block incidence graph must be a tree.'
            parent[y]=x;queue.append(y)
    chain=[v]
    while chain[-1]!=u:chain.append(parent[chain[-1]])
    chain.reverse();kept=0;upper=0;record=[]
    for pos in range(1,len(chain),2):
        block=blocks[chain[pos]-512];entry=chain[pos-1];exit=chain[pos+1]
        even=sum(x.bit_count()%2==0 for x in block);odd=len(block)-even
        adjacent=bool(neighbours[entry]&(1<<exit))
        if adjacent:bound=1
        elif (entry.bit_count()^exit.bit_count())%2:bound=2*min(even,odd)-1
        else:
            start=even if entry.bit_count()%2==0 else odd
            other=len(block)-start;bound=2*min(start-1,other)
        kept|=sum(1<<x for x in block);upper+=bound
        record.append(dict(vertices=sorted(block),entry=entry,exit=exit,even=even,odd=odd,adjacent=adjacent,upper_edges=bound))
    return dict(upper_edges=upper,mask=kept,blocks=record)
