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
def run(lengths):
    cases=0
    for row in bank:
        p=row['vertex_sequence']
        assert len(p)==192 and valid(p)
        pre=[0];post=[0]
        for v in p:pre.append(pre[-1]|N[v]|(1<<v))
        for v in reversed(p):post.append(post[-1]|N[v]|(1<<v))
        for k in lengths:
            for i in range(len(p)-k):
                j=i+k
                blocked=pre[i]|post[len(p)-1-j]|(1<<p[i])
                tail=search(p[i],p[j],k+2,blocked)
                cases+=1
                if tail:
                    out=p[:i+1]+tail+p[j+1:]
                    assert valid(out) and len(out)==194
                    print(json.dumps(out),flush=True);return
    print(dict(lengths=lengths,bank=len(bank),cases=cases,nodes=nodes),flush=True)
run(list(map(int,sys.argv[2:])))
