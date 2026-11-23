"""Generate rooted local replacements of paths from a Q8 bank."""
import json,random,sys
def norm(p):
    axes={}
    return tuple(axes.setdefault(a^b,len(axes)) for a,b in zip(p,p[1:]))
def variants(p):
    nb=[{v^(1<<d) for d in range(8)} for v in range(256)]
    for width in range(1,7):
        for i in range(1,len(p)-width+1):
            prefix=p[:i];suffix=p[i+width:];last=prefix[-1]
            banned=set(prefix)|set(suffix)
            for v in prefix[:-1]+suffix[1:]:banned.update(nb[v])
            def dfs(chain,blocked):
                tip=chain[-1];boundary=bool(suffix) and tip in nb[suffix[0]]
                if len(chain)>1 and (not suffix or boundary):
                    out=prefix+chain[1:]+suffix
                    if 94<=len(out)<=99 and out!=p:yield out
                if len(chain)>=width+3 or boundary:return
                for v in nb[tip]-blocked:
                    yield from dfs(chain+[v],blocked|nb[tip]|{tip})
            yield from dfs([last],banned)
if __name__=="__main__":
    ps=[json.loads(l) for l in open(sys.argv[1])]
    existing={norm(p) for p in ps};seen=set()
    for p in ps:
        for v in variants(p):
            assert len(v)==len(set(v)) and all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(v) for j,b in enumerate(v) if j>i)
            code=norm(v)
            if code not in existing:seen.add(code)
    seq=sorted(seen);random.Random(920).shuffle(seq);seq.sort(key=len,reverse=True)
    for s in seq:
        a=[0]
        for d in s:a.append(a[-1]^1<<d)
        print(json.dumps(a,separators=(',',':')))
