import json,subprocess,collections,random,itertools,os
from bank import *
def walk(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def canon(w):return min(normalize(w),normalize(w[::-1]))
def validate(p):
    assert len(set(p))==len(p) and all(0<=v<512 for v in p)
    assert all(((a^b).bit_count()==1)==(j==i+1) for j,b in enumerate(p) for i,a in enumerate(p[:j]))
def shape(p,d=9):
    s=set(p);nb={x:[x^1<<i for i in range(d) if x^1<<i in s] for x in s}
    ends=[x for x in s if len(nb[x])==1]
    if len(ends)!=2 or any(len(neigh)>2 for neigh in nb.values()):return
    path=[min(ends)];prev=None
    while True:
        ahead=[x for x in nb[path[-1]] if x!=prev]
        if not ahead:break
        prev=path[-1];path.append(ahead[0])
    if len(path)!=len(s):return
    return canon(''.join(str((a^b).bit_length()-1) for a,b in zip(path,path[1:])))
def shear(p,u,v):return [x^(u if (v&x).bit_count()%2 else 0) for x in p]
def invbasis(p,gens):
    table={0:0}
    for i,g in enumerate(gens):table.update({x^g:y|1<<i for x,y in list(table.items())})
    assert len(table)==512;return [table[x] for x in p]
def shape_after(w,u,v):
    assert u and v and (u&v).bit_count()%2==0
    return shape(shear(walk(w),u,v))
def read(f):return [l.split() for l in (D/f).open()]
raw=(D/'sources.txt').read_text().split();assert len(raw)==len(set(raw));provs=json.loads((D/'provenance.json').read_text());near=[list(map(int,t[2:])) for line in (D.parent/'q9_via_q10/seven_donors.pts').open() if (t:=line.split())[0]=='SEED']
with gzip.open(D.parent/'q9_port_followup_public191.txt.gz','rt') as f:public=[list(map(int,l.split())) for l in f]
for w,(src,i,off,rev) in zip(raw,provs):
    pts=(near if src=='near' else public)[i][off:off+len(w)+1];validate(pts)
    assert shape(pts)==w
basic=read('transformed.txt')
for w,idx,u,v,orig in basic:
    if int(u):assert shape_after(raw[int(idx)],int(u),int(v))==w
    else:assert w==raw[int(idx)]
for w,(_,parent,u,v) in json.loads((D/'lineage.json').read_text()).items():assert shape_after(parent,u,v)==w
for w,(parent,mode,*z) in json.loads((D/'joint_lineage.json').read_text()).items():
    if mode=='rank1':assert shape_after(parent,*z)==w
    else:
        a,b,g,h=z;ds=[1<<i for i in range(9)];ds[a]=g;ds[b]=h;assert shape(invbasis(walk(parent),ds))==w
closure=read('closure.txt');joint=read('joint.txt');shells=[('join0.log',basic),('join1.log',basic),('closure_join0.log',closure),('closure_join1.log',closure),('joint_join0.log',joint),('joint_join1.log',joint)]
if (D/'final_shells.json').exists():
    for f,bankfile in json.loads((D/'final_shells.json').read_text()):shells.append((f,read(bankfile)))
witnesses=0;best={};tally=[]
for fn,bank in shells:
    rows=read(fn);assert rows[-1][0]=='DONE'
    tally.append([fn,*map(int,rows[-1][3:6])])
    for t in rows:
        if t[0]!='W':continue
        cls,n,lt,rt,mode,dep,bridge=map(int,t[1:8]);axes=list(map(int,t[8:17]));p=list(map(int,t[17:]));validate(p);assert len(p)==n+1
        def oriented(tag):
            w=bank[tag//2][0];return normalize(w[::-1] if tag%2 else w)
        left=walk(oriented(lt));l=left[-1];left=[v^l for v in left];right=[bridge]
        for a in oriented(rt)[:dep]:right.append(right[-1]^axes[int(a)])
        assert p==left+(right if mode else right[1:])
        assert len({z for z in axes if z})==sum(bool(z) for z in axes)
        witnesses+=1
        if n>best.get(cls,{}).get('length',0):best[cls]=dict(length=n,path=p,source=fn,left=lt,right=rt)
controls=json.loads((D/'controls.json').read_text());direct=read('control_check.log')
recoveries=[]
for j,(id,cut,g,a,b,x,y) in enumerate(controls):
    assert int(direct[2*j][-1])==0 and int(direct[2*j+1][-1])>0
    for src,dest in [(x,a),(y,b)]:
        result=subprocess.run([D/'transform','9'],input=src+'\n',text=True,capture_output=True,check=True)
        entry=next(z.split() for z in result.stdout.splitlines() if z.split()[0]==dest)
        _,_,u,v,_=entry;assert shape_after(src,int(u),int(v))==dest;recoveries.append((id,src,dest,int(u),int(v)))
(D/'inverse_controls.json').write_text(json.dumps(recoveries))
(D/'best.json').write_text(json.dumps(best))
info=dict(source_count=len(raw),first=len(basic),closure=len(closure),combined=len(joint),independent_transformed_shapes=len(json.loads((D/'lineage.json').read_text()))+len(json.loads((D/'joint_lineage.json').read_text())),control_pairs=len(controls),validated_joins=witnesses,best={k:v['length'] for k,v in best.items()},join_stats=tally)
print(json.dumps(info,indent=2))
