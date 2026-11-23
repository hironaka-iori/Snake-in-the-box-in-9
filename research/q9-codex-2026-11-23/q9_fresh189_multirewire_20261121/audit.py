from pathlib import Path
import collections,gzip,itertools,json,re
D=Path(__file__).resolve().parent;R=D.parent
def path(w,z=0):
    p=[z]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def canonical(w):
    def rel(t):
        a={};return ''.join(str(a.setdefault(d,len(a))) for d in t)
    return min(rel(w),rel(w[::-1]))
def verify(p):
    assert len(set(p))==len(p) and all(0<=v<512 for v in p)
    loc={v:j for j,v in enumerate(p)}
    for j,v in enumerate(p):
        assert {loc[x] for k in range(9) if (x:=v^(1<<k)) in loc}=={i for i in (j-1,j+1) if 0<=i<len(p)}
def paircheck(p):
    assert all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j,b in enumerate(p) if j>i)
def key(p):return canonical(''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:])))
seedwords=(R/'q9_uncovered_abab_20261121/outside_wordbanks189.words').read_text().split();assert len(set(map(canonical,seedwords)))==16
seeds=[path(w) for w in seedwords];assert all(len(p)==190 for p in seeds)
for p in seeds:verify(p);paircheck(p)
archive191=(R/'q9_far189_spring_20261121/comparison191.words').read_text().split()
poses=[list(map(int,r.split())) for r in (D/'poses.dat').read_text().splitlines()]
metadata=[r.split() for r in (D/'poses.meta').read_text().splitlines()]
for z,m in zip(poses,metadata):
    a,b,perm,t,overlap=m;i,j=int(a),int(b);assert list(z[:190])==seeds[i]
    q=[sum(1<<int(perm[k]) for k in range(9) if v>>k&1)^int(t) for v in seeds[j]];assert z[190:]==q and len(set(z[:190])&set(q))==int(overlap)
archive={n:set() for n in (189,190,191)};files=[]
for f in sorted(set(R.rglob('*.words'))|set(R.rglob('*.words.gz'))):
    if D in f.parents:continue
    text=gzip.open(f,'rb').read() if f.suffix=='.gz' else f.read_bytes()
    ws={w.decode() for w in text.split() if re.fullmatch(rb'[0-8]{189,191}',w)}
    if not ws:continue
    files.append(str(f.relative_to(R)))
    for w in ws:
        for n in range(189,len(w)+1):
            for j in range(len(w)-n+1):archive[n].add(canonical(w[j:j+n]))
out={};candidates={n:{} for n in (189,190,191,192)}
for mode,prefix in [('control','ctl'),('direct','a'),('reordered','b'),('graft','c'),('ranged','d'),('matched','matches')]:
    files2=[D/(prefix+'.long')] if mode=='matched' else [D/(prefix+str(i)+'.long') for i in range(1 if mode=='control' else 16)]
    recs=0;saved=set();novel={};outside=0
    for f in files2:
        for ln,line in enumerate(f.read_text().splitlines(),1):
            nn,exc,tag,g1,g2,start,w=line.split();n=int(nn);p=path(w,int(start));verify(p);paircheck(p);assert len(p)==n+1
            if mode=='matched':
                pose,which,lt,rt,i,j,k,l,u,v,rev=map(int,tag.split(','));a,b=poses[pose][:190],poses[pose][190:]
                if which:a,b=b,a
                arcs=[a[lt:i-u],b[k:l+1] if k<l else list(reversed(b[l:k+1])),a[j+v+1:190-rt]]
                if rev:arcs[1]=arcs[1][::-1]
                host=a
            else:
                ii,lt,rt,lo,u,hi,v,order,ori,don,ds,leng,rv,perm=tag.split(',');i,lt,rt,lo,u,hi,v,ori,don,ds,leng,rv=map(int,[ii,lt,rt,lo,u,hi,v,ori,don,ds,leng,rv])
                host=path(archive191[0]) if mode=='control' else seeds[i]
                parts=[host[lt:lo],host[lo+u:hi],host[hi+v:len(host)-rt]]
                if don!=-1:
                    q=seeds[don][ds:ds+leng];q=q[::-1] if rv else q;offset=parts[1][0];old=parts[1]
                    parts[1]=[offset^sum(1<<int(perm[k]) for k in range(9) if (v^q[0])>>k&1) for v in q]
                    assert parts[1]!=old and parts[1][0]==old[0] and parts[1][-1]==old[-1]
                arcs=[parts[int(k)][::-1] if ori>>b&1 else parts[int(k)] for b,k in enumerate(order)]
            pos=p.index(arcs[0][0])
            for z,g in zip(arcs,[int(g1),int(g2),0]):
                assert p[pos:pos+len(z)]==z;pos+=len(z)+g
            assert int(exc)==len(set(p)-set(host));outside=max(outside,int(exc));recs+=1
            k=canonical(w);saved.add(k)
            if mode!='control':candidates[n].setdefault(k,[f.name,ln])
    out[mode]=dict(records=recs,classes_by_edges={n:sum(len(k)==n for k in saved) for n in (189,190,191,192)},max_outside=outside)
fresh={}
for n in candidates:
    new=set(candidates[n])-archive.get(n,set());fresh[n]=len(new)
    (D/f'new{n}.words').write_text(''.join(w+'\n' for w in sorted(new)))
    if new:(D/f'new{n}_sources.json').write_text(json.dumps({w:candidates[n][w] for w in sorted(new)},indent=1))
out.update(pose_count=len(poses),seed_count=16,comparison_files=len(files),comparison_sizes={n:len(s) for n,s in archive.items()},combined={n:len(v) for n,v in candidates.items()},new=fresh)
(D/'bank_files.json').write_text(json.dumps(files,indent=1))
print(json.dumps(out,indent=2))
