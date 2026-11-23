import json,sys,time,collections
from pathlib import Path
bank=json.loads(Path(sys.argv[1]).read_text())
N=[sum(1<<(v^(1<<i)) for i in range(9)) for v in range(512)]
def valid(p):
    return len(set(p))==len(p) and all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
nodes=0
def search(u,t,left,blocked):
    global nodes
    nodes+=1
    if left==1:
        return [t] if (u^t).bit_count()==1 else None
    if (u^t).bit_count()==1 or (u^t).bit_count()>left:return None
    opts=N[u]&~blocked&~(1<<t)
    nxt=blocked|N[u]|(1<<u)
    while opts:
        bit=opts&-opts; opts-=bit
        v=bit.bit_length()-1
        tail=search(v,t,left-1,nxt)
        if tail is not None:return [v]+tail
    return None
def shift_search(ks):
    total=viable=0
    for index,row in enumerate(bank):
        p=row['vertex_sequence']
        assert valid(p)
        pre=[0]; occupied=[0]
        for v in p:
            pre.append(pre[-1]|N[v]|(1<<v))
            occupied.append(occupied[-1]|(1<<v))
        for axis in range(9):
            q=[v^(1<<axis) for v in p]
            post=[0]; used=[0]
            for v in reversed(q):
                post.append(post[-1]|N[v]|(1<<v))
                used.append(used[-1]|(1<<v))
            for k in ks:
                for i in range(len(p)-k):
                    j=i+k
                    total+=1
                    if pre[i+1]&used[len(q)-j]:continue
                    viable+=1
                    blocked=pre[i]|post[len(q)-1-j]|(1<<p[i])
                    tail=search(p[i],q[j],k+1,blocked)
                    if tail:
                        out=p[:i+1]+tail+q[j+1:]
                        assert valid(out) and len(out)==193
                        print('FOUND',index,axis,k,i,json.dumps(out),flush=True);return
    print(dict(lengths=ks,bank=len(bank),placements=total,compatible=viable,nodes=nodes),flush=True)
shift_search(list(map(int,sys.argv[2:])))
