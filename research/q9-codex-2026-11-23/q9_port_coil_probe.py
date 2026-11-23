from itertools import permutations
def cycles(d,L):
    path=[0]; used={0}; masks=set()
    def dfs(largest):
        end=path[-1]
        for axis in range(min(largest+2,d)):
            v=end^(1<<axis)
            if v in used:continue
            final=len(path)+1==L
            if final and v.bit_count()!=1:continue
            if any((v^w).bit_count()==1 for w in path[(1 if final else 0):-1]):continue
            if final:masks.add(tuple(sorted((*path,v))));continue
            path.append(v);used.add(v)
            dfs(max(largest,axis))
            path.pop();used.remove(v)
    dfs(-1)
    return sorted(masks)

def image(C,p,t):
    return {t^sum(((x>>i)&1)<<p[i] for i in range(len(p))) for x in C}

def disjoint():
    cs=cycles(5,14)
    print("normalized Q5 masks",len(cs),flush=True)
    allmask=(1<<32)-1
    pp=list(permutations(range(5)))
    full=set()
    for c in cs:
        for p in pp:
            q=image(c,p,0)
            for t in range(32): full.add(sum(1<<(x^t) for x in q))
    print("all masks",len(full),flush=True)
    for c in cs:
        m=sum(1<<x for x in c)
        for f in full:
            if not (f&m):
                print("FOUND",c,tuple(i for i in range(32) if f>>i&1));return
    print("no disjoint pair")
if __name__=="__main__":disjoint()
