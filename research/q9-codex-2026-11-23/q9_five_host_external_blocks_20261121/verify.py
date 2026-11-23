from pathlib import Path
import json,hashlib,collections,itertools,subprocess
D=Path(__file__).resolve().parent
def rows(src):return [list(map(int,l.split())) for l in Path(src).read_text().splitlines()]
def valid(p):
    return len(p)==len(set(p)) and all(0<=x<512 for x in p) and all(((a^p[j]).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j in range(i+1,len(p)))
def read(name):return (D/(name+'.log')).read_text().splitlines()
def key(row,ext):return (int(row),tuple(sorted(map(int,ext))))
def getexternal(t,left,right=None):
    a=t.index(left)+1;b=t.index(right) if right in t else len(t)
    return key(t[1],t[a:b])
def getstat(name,left,right=None):
    out={}
    for l in read(name):
        t=l.split()
        if t[0] not in ('LIMIT','UNSAT','FOUND','AUDIT'):continue
        k=getexternal(t,left,right);assert k not in out;out[k]=t[0]
        assert t[0]!='FOUND','new target requires individual witness reporting'
    return out
raw=list(map(set,rows('q8_all_191_positive.hosts')));seeds=json.loads((D/'seeds.json').read_text());five=[set(s['host']) for s in seeds]
assert len(raw)==9 and len(five)==5 and all(len(x)==194 for x in raw+five)
docs=json.loads((D/'nine_witnesses.json').read_text());labels=set();counter=collections.Counter()
for r in docs:
    p=r['vertices'];assert len(p)==192 and valid(p) and set(p)<=raw[r['host']]
    assert r['layer_crossings']==sum((a^b)==256 for a,b in zip(p,p[1:]));counter[r['layer_crossings']]+=1;labels.add(r['reference'])
assert len(docs)==24 and labels=={27,32,37,39,57,62,96,103,128,129}
print('Nine raw 194-vertex hosts, SHA256',hashlib.sha256(Path('q8_all_191_positive.hosts').read_bytes()).hexdigest())
print('Independently checked 191-edge classes',sorted(labels),'labelled witnesses by number of layer crossings',dict(counter))
for s in seeds:assert len(s['path'])==192 and valid(s['path']) and set(s['path'])<=set(s['host'])
for name,hosts,dim in [('face3',five,3),('nine_face3',raw,3),('face4',five,4),('nine_face4',raw,4)]:
    rr=[l.split() for l in read(name) if l.startswith('ROW')];assert len(rr)==len(hosts) and read(name)[-1]=='DONE'
    counts=collections.Counter();caps=0
    for i,H in enumerate(hosts):
        seen=set()
        for axes in itertools.combinations(range(9),dim):
            mask=sum(1<<k for k in axes);bases={x&~mask for x in range(512)}
            for b in bases:
                q=tuple(x for x in range(512) if x&~mask==b and x not in H)
                if len(q)>=4:seen.add(q)
        hist=collections.Counter(map(len,seen));t=rr[i];assert int(t[1])==i and len(seen)==int(t[5]) and hist=={int(z.split('/')[0]):int(z.split('/')[1]) for z in t[11:]}
        counts.update(hist);caps+=int(t[7])
    print(name,'distinct per-host domains',sum(counts.values()),'outside pool histogram',dict(sorted(counts.items())),'initial limits',caps)
    if dim==3:assert caps==0
# Verify every 4-face is ruled out directly or by a superset with a negative SAT answer.
cover=collections.defaultdict(set)
for l in read('cover_sat'):
    t=l.split()
    if t[0]=='UNSAT':cover[int(t[1])].add((int(t[2]),int(t[3])))
    assert t[0]!='FOUND'
replay=getstat('cover_retry','extras','vertices')
limits4={key(t[1],[x for x in range(512) if x not in raw[int(t[1])] and (x&~int(t[2]))==int(t[3])]) for t in (l.split() for l in read('cover_sat')) if t[0]=='LIMIT' and int(t[2]).bit_count()==4}
assert set(replay)==limits4 and all(v=='UNSAT' for v in replay.values())
n=0
for i,H in enumerate(raw):
    masks={m for m,b in cover[i]}
    for m in range(512):
        if m.bit_count()!=4:continue
        supers=[s for s in masks if m&s==m]
        for b in range(512):
            if b&m:continue
            if not any((s,b&~s) in cover[i] for s in supers):
                k=key(i,[x for x in range(512) if (x&~m)==b and x not in H]);assert replay[k]=='UNSAT'
            n+=1
assert n==9*4032
print('All',n,'raw-host 4-faces resolved; alternative CaDiCaL checks on remaining',len(replay),'all UNSAT.')
st=getstat('nine_multi','outside');a=getstat('multi_sat','extras','rounds');b=getstat('multi_retry','extras','pins');c=getstat('multi_final','extras','vertices')
assert set(a)==set(st) and {k for k,v in a.items() if v=='LIMIT'}==set(b) and {k for k,v in b.items() if v=='LIMIT'}==set(c) and all(v=='UNSAT' for v in c.values())
nm=sum(int(l.split()[5]) for l in read('nine_multi') if l.startswith('ROW'))
print('Random unions of two to four small cubes',nm,'resolved; final independent CaDiCaL negatives',len(c))
src={getexternal(l.split(),'outside') for l in (D/'crossing.domains').read_text().splitlines()}
a=getstat('crossing_sat','extras','rounds');b=getstat('crossing_retry','extras','vertices')
assert set(a)==src and {k for k,v in a.items() if v=='LIMIT'}==set(b) and all(v=='UNSAT' for v in b.values())
print('Distributed two-layer crossing/tip repairs',len(src),'all resolved; exterior histogram',dict(sorted(collections.Counter(len(t) for i,t in src).items())))
ctrls=[]
for l in read('positive'):
    t=l.split();i=int(t[1]);p=list(map(int,t[t.index('vertices')+1:]));n=int(t[3]);dom=rows(D/f'control{i}.in')[0];small=set(dom[:n])
    assert valid(p) and len(p)==192 and set(p)<=set(dom) and len(set(p)-small)==int(t[7])>=6
    ctrls.append((small,set(dom)))
for source,offset,min_edges in [('sat_control',2,191),('tight_control',2,191),('cd_control',1,190)]:
    for line in read(source):
        t=line.split();i=int(t[0]);p=list(map(int,t[offset:]));small,dom=ctrls[i]
        assert valid(p) and len(p)-1>=min_edges and set(p)<=dom and len(set(p)-small)>=len(p)-len(small)
print('All positive controls validated pairwise; main five controls require at least',[192-len(h) for h,_ in ctrls],'points exterior to their deliberately damaged hosts.')
six=read('six_probe');assert six[-1]=='DONE' and not any(l.startswith('FOUND') for l in six)
print('Additional 6-face CaDiCaL probes',dict(collections.Counter(l.split()[0] for l in six[:-1])))

base6={(int(t[1]),int(t[2]),int(t[3])) for t in (l.split() for l in six[:-1]) if t[0]=='LIMIT'}
deep=read('six_final');assert deep[-1]=='DONE' and not any(l.startswith('FOUND') for l in deep)
deepids={(int(t[1]),int(t[2]),int(t[3])) for t in (l.split() for l in deep[:-1])};assert deepids==base6
lim=sum(l.startswith('LIMIT') for l in deep)
print('Final enlarged 6-face sample',len(six)-1,'resolved negative',len(six)-1-lim,'unresolved',lim,'outside pool sizes',min(int(l.split()[5]) for l in six[:-1]),max(int(l.split()[5]) for l in six[:-1]))

