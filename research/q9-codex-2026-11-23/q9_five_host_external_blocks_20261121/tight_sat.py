from pathlib import Path
import sys
from pool_sat import NB,solve,rows
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from search_q9_anchored_sets import search
def tighten(cells,goal):
    S=set(cells);M=set()
    while True:
        if len(S)<goal or not M<=S:return None,M
        nb={v:NB[v]&S for v in S};tin={};low={};sz={};children={};order=[]
        def dfs(x,parent):
            tin[x]=low[x]=len(order);order.append(x);sz[x]=1;children[x]=[]
            for y in nb[x]:
                if y==parent:continue
                if y not in tin:
                    dfs(y,x);low[x]=min(low[x],low[y]);sz[x]+=sz[y]
                    if low[y]>=tin[x]:children[x].append(y)
                else:low[x]=min(low[x],tin[y])
        large=None
        for x in S:
            if x in tin:continue
            dfs(x,-1)
            if sz[x]>=goal:assert large is None;large=set(order[tin[x]:tin[x]+sz[x]])
        if large is None:return None,M
        if large!=S:S=large;continue
        drop=set();n=len(S)
        for x in S:
            kids=children[x];rest=n-1-sum(sz[y] for y in kids);sizes=[sz[y] for y in kids]+[rest]
            big=sorted(sizes,reverse=True)
            if big[0]<goal:M.add(x)
            if len(big)>1 and big[0]+big[1]+1<goal:return None,M
            for j,val in enumerate(sizes):
                if not val or val+max((s for i,s in enumerate(sizes) if i!=j),default=0)+1>=goal:continue
                if j<len(kids):
                    y=kids[j];drop.update(order[tin[y]:tin[y]+sz[y]])
                else:
                    other=S-{x}
                    for y in kids:other.difference_update(order[tin[y]:tin[y]+sz[y]])
                    drop.update(other)
        # A degree-one tail longer than the total omission budget must intersect any successful path.
        # That path can be extended to the terminal leaf while retaining its existing vertices.
        allowance=n-goal
        for x in S:
            if len(nb[x])!=1:continue
            prev=None;v=x;tail=[]
            while len(nb[v])<=2:
                tail.append(v);nxt=nb[v]-{prev}
                if not nxt:break
                prev,v=v,next(iter(nxt))
            if len(tail)>allowance:M.update(tail)
        if M&drop:return None,M
        last=-1
        while last!=len(M):
            last=len(M);ends=[x for x in M if len(nb[x])<=1]
            if any(not nb[x] for x in M) or len(ends)>2:return None,M
            for x in list(M):
                deg=len(nb[x]&M)
                if deg>2:return None,M
                if len(nb[x])==1 or (len(ends)==2 and x not in ends and len(nb[x])==2):M.update(nb[x])
                if deg==2:drop.update(nb[x]-M)
        if M&drop:return None,M
        drop.update(x for x in S-M if len(nb[x]&M)>2)
        if not drop:return S,M
        S-=drop
def exact(cells,target=192,cap=60000):
    S,M=tighten(cells,target+1)
    if S is None:return 'UNSAT',len(M),None
    if not M:
        stat,n,w=solve(S,target,cap);return stat,0,w
    st,w=search(M,S,target,cap,allowed=S,at_least=True)
    return ('LIMIT' if st=='UNKNOWN' else st),len(M),w
if __name__=='__main__':
    if sys.argv[1]=='control':
        for i in range(5):
            st,m,w=exact(rows(D/f'control{i}.in')[0],191);assert st=='FOUND';print(i,m,*w)
        raise SystemExit
    hosts=list(map(set,rows(sys.argv[1])));tags=set(sys.argv[3].split('+'))
    for l in Path(sys.argv[2]).open():
        t=l.split()
        if t[0] not in tags:continue
        i=int(t[1])
        if t[2]=='extras':ext=list(map(int,t[3:t.index('rounds')]))
        elif 'outside' in t:ext=list(map(int,t[t.index('outside')+1:]))
        else:
            mask=int(t[2]);base=int(t[3]);ext=[v for v in range(512) if v not in hosts[i] and (v&~mask)==base]
        st,m,w=exact(hosts[i]|set(ext))
        print(st,i,'extras',*sorted(ext),'pins',m,*(w or []),flush=True)
        if w:break
    print('DONE',flush=True)

