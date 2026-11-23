from collections import Counter
from functools import lru_cache
from itertools import accumulate,permutations
from operator import xor
from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib,json,random,subprocess,sys
D=Path(__file__).resolve().parent; R=D.parent
NB=[tuple(v^(1<<j) for j in range(8)) for v in range(256)]
def ver(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    assert all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def words(f):return f.read_text().splitlines()
def mask(vs):return sum(1<<v for v in vs)
def elements(m):return [v for v in range(256) if (m>>v)&1]
@lru_cache(maxsize=None)
def paths(m):
    s=set(elements(m));adj={v:s.intersection(NB[v]) for v in s}
    if sum(not a for a in adj.values())>2 or any(len(a)>2 for a in adj.values()):return ()
    comps=[]
    while s:
        x=next((x for x in s if len(adj[x])<2),None)
        if x is None:return ()
        path=[x];s.remove(x)
        while nei:=adj[path[-1]]&s:
            if len(nei)!=1:return ()
            x=next(iter(nei));s.remove(x);path.append(x)
        comps.append(tuple(path))
    return tuple(comps)
def canonical(m):
    cs=paths(m);assert cs;best=None
    for c in cs:
        if len(c)!=max(map(len,cs)):continue
        for seg in (c,c[::-1]):
            order=list(dict.fromkeys((a^b).bit_length()-1 for a,b in zip(seg,seg[1:])))
            for rest in permutations(set(range(8))-set(order)):
                perm=order+list(rest);tab=[0]*256
                for v in range(1,256):tab[v]=tab[v&(v-1)]|1<<perm.index((v&-v).bit_length()-1)
                b=mask(tab[v^seg[0]] for v in elements(m));key=tuple((b>>(64*i))&((1<<64)-1) for i in range(4))
                if best is None or key<best:best=key
    return sum(v<<(64*i) for i,v in enumerate(best))
def layer(p,axis,side):
    return mask((v&((1<<axis)-1))|((v>>(axis+1))<<axis) for v in p if (v>>axis)&1==side)
def readsets(name):
    ls=words(D/(name+'.layers'));rows=[]
    for l in ls[1:]:
        t=list(map(int,l.split()[1:]));m=sum(x<<(64*i) for i,x in enumerate(t[4:]));rows.append((t[:4],m))
    assert len({m for _,m in rows})==len(rows)
    return list(map(int,ls[0].split()[1:])),rows
rng=random.Random(30927);checks={};src_all=[];banks={}
for name,file,isref in [('record',R/'q9_reordered_segments_20261120/reference191.words',True),('near',R/'q9_three_axis.in',False)]:
    meta,entries=readsets(name);seq=[];raw=Counter();ch=Counter();filewords=words(file)
    for w in filewords:
        p=list(accumulate((1<<int(c) for c in w),xor,initial=0));s=set(p)
        assert len(s)==len(p)==(192 if isref else 193)
        c=sum(sum((v^(1<<j)) in s for j in range(9)) for v in p)//2-len(w)
        if isref:assert c==0
        ch[c]+=1;seq.append(p)
        for j in range(9):
            for side in (0,1):raw[layer(p,j,side)]+=1
    ok={m:n for m,n in raw.items() if paths(m)}
    assert sum(ok.values())==meta[1] and meta[0]==len(seq) and meta[2]==len(entries)
    sample=rng.sample(entries,min(240,len(entries)))
    for (_,i,j,k),m in sample:assert canonical(layer(seq[i],j,k))==m
    banks[name]=set(m for _,m in entries);src_all.append(seq)
    checks[name]=dict(sha256=hashlib.sha256(file.read_bytes()).hexdigest(),input_chords=ch,verified_usable_layer_instances=sum(ok.values()),unique_masks=len(entries),canonical_provenance_sample=len(sample))
def standard(m):
    return tuple((m>>(64*i))&((1<<64)-1) for i in range(4))
base=sorted(set.union(*banks.values()),key=standard)
for k in (1,2):
    meta,entries=readsets('edit'+str(k));samples=rng.sample(entries,min(200,len(entries)))
    for (drops,idx,x,y),m in samples:
        old=base[idx];assert old>>x&1 and (drops==1 or old>>y&1)
        tmp=old^(1<<x)
        if k==2:tmp^=1<<y
        assert canonical(tmp)==m
    checks['edit'+str(k)]=dict(sources=meta[0],proposals=meta[1],valid=meta[2],shapes=meta[3],audited_provenance=len(samples))
p=list(map(int,next(l for l in words(D/'control191.log') if l.startswith('FOUND')).split()[2:]));ver(p);assert len(p)==192
small=[];newseen=set()
for p in src_all[0]:
    for axis in range(9):
        a,b=layer(p,axis,0),layer(p,axis,1)
        na=a.bit_count();nb=b.bit_count()
        if na==nb or min(na,nb) in newseen:continue
        newseen.add(min(na,nb));small.append((canonical(a),canonical(b)))
        if len(small)==5:break
    if len(small)==5:break
while len(small)<13:
    a,b=rng.sample(base,2)
    if a.bit_count()!=b.bit_count() and a.bit_count()+b.bit_count()>=193:small.append((a,b))
data=''.join(' '.join(map(str,[a.bit_count(),b.bit_count(),*elements(a),*elements(b)]))+'\n' for a,b in small)
lines=subprocess.check_output(['/tmp/q9_portbrute21'],input=data,text=True).splitlines()
ind=Counter();tested=0
with TemporaryDirectory() as temp:
    f=Path(temp)/'fixtures.layers'
    for (a,b),l in zip(small,lines,strict=True):
        pred,steps=map(int,l.split());tested+=steps;ind[pred]+=1
        f.write_text(''.join('F 0 0 0 0 '+' '.join(map(str,standard(m)))+'\n' for m in [a,b]))
        output=subprocess.check_output(['/tmp/q9_portmatch21',str(a.bit_count()+b.bit_count()-1),'1',str(f)],text=True).splitlines()
        assert any(t.startswith('FOUND ') for t in output)==bool(pred)
        for t in output:
            if t.startswith('FOUND '):ver(list(map(int,t.split()[2:])))
checks['independent_full_isometry_examples']=dict(cases=len(small),positive=ind[1],negative=ind[0],actual_placements=tested)
slines=words(D/'salvaged.layers')
for line in rng.sample(slines[1:],200):
    row,axis,side,x,*blocks=map(int,line.split()[1:])
    raw=layer(src_all[1][row],axis,side)
    assert raw.bit_count()>=103 and not paths(raw) and raw>>x&1
    assert canonical(raw^(1<<x))==sum(v<<(64*i) for i,v in enumerate(blocks))
checks['salvaged']=dict(metadata=list(map(int,slines[0].split()[1:])),audited_provenance=200)
checks['control_edges']=191
print(json.dumps(checks,indent=2))
