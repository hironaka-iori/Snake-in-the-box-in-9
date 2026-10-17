import json, collections, itertools, statistics
B=json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
def L(x): return json.loads(x) if isinstance(x,str) else x
light_tr=[]; maxfib=[]; nfib=[]; words=set(); crossings1=0; minc=[]
seg_counts=[]; q8split=collections.Counter(); fibhist=collections.Counter()
for e in B:
    t=L(e['transition_sequence']); v=L(e['vertex_sequence'])
    assert len(v)==192 and len(t)==191
    # verify snake
    S=set(v); assert len(S)==192
    pos={x:i for i,x in enumerate(v)}
    for i,x in enumerate(v):
        for k in range(9):
            y=x^(1<<k)
            if y in pos: assert abs(pos[y]-i)==1
    c=collections.Counter(t)
    cs=sorted(c[k] for k in range(9))
    minc.append(cs)
    light=sorted(range(9),key=lambda k:(c[k],k))[:4]
    light_tr.append(sum(c[k] for k in light))
    mask=sum(1<<k for k in light)
    fib=collections.Counter(x&mask for x in v)
    nfib.append(len(fib)); maxfib.append(max(fib.values()))
    for s in fib.values(): fibhist[s]+=1
    # outer word canonical
    w=[k for k in t if k in light]
    def canon(w):
        m={}; out=[]
        for k in w:
            if k not in m: m[k]=len(m)
            out.append(m[k])
        return tuple(out)
    words.add(min(canon(w),canon(w[::-1])))
    # single-crossing coordinate
    ones=[k for k in range(9) if c[k]==1]
    if ones:
        crossings1+=1
        k=ones[0]; i=t.index(k); q8split[tuple(sorted((i,190-i)))]+=1
print('light-4 transitions: min',min(light_tr),'max',max(light_tr),'median',statistics.median(light_tr))
print('fibers used all 16:',all(n==16 for n in nfib),' min',min(nfib))
print('max fiber size overall',max(maxfib),'distribution of per-snake max',collections.Counter(maxfib))
print('distinct outer words up to relabel+reversal:',len(words))
print('snakes with a coordinate used once:',crossings1,q8split)
print('sorted coordinate counts examples',minc[:3])
print('min-count coordinate distribution',collections.Counter(m[0] for m in minc))
