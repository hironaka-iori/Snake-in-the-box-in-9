from pathlib import Path
import json,gzip,re,collections
D=Path(__file__).resolve().parent;R=D.parent
def canon(w):
    def norm(z):
        m={};return ''.join(str(m.setdefault(c,len(m))) for c in z)
    return min(norm(w),norm(w[::-1]))
def path(w,v=0):
    p=[v]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def validate(p):
    assert len(p)==len(set(p)) and all(0<=u<512 for u in p)
    for i,u in enumerate(p):
        for j in range(i):assert ((p[j]^u).bit_count()==1)==(j+1==i)
old={n:set() for n in range(189,193)}
for name in json.loads((D/'bank_files.json').read_text()):
    f=R/name;text=gzip.open(f,'rb').read() if f.suffix=='.gz' else f.read_bytes()
    for w in {x.decode() for x in text.split() if re.fullmatch(rb'[0-8]{189,191}',x)}:
        for n in range(189,len(w)+1):
            for i in range(len(w)-n+1):old[n].add(canon(w[i:i+n]))
a=json.loads((D/'audit.json').read_text());assert all(len(old[int(n)])==z for n,z in a['comparison_sizes'].items())
first_src=(D/'new189.words').read_text().split();assert len(first_src)==33
seed=[path(w) for w in first_src];sets={g:{n:{} for n in range(189,193)} for g in (1,2)}
for ix,pr in enumerate(('a','b','c','d','matches','e')):
    files=[D/'matches.long'] if pr=='matches' else [D/f'{pr}{i}.long' for i in range(33 if pr=='e' else 16)]
    for f in files:
        for nline,raw in enumerate(f.read_text().splitlines(),1):
            n,out,tag,g1,g2,start,w=raw.split();n=int(n);p=path(w,int(start));validate(p);assert len(p)==n+1
            if pr=='e':
                i,lt,rt,lo,u,hi,v,order,ori,don,ds,leng,rv,perm=tag.split(',');i,lt,rt,lo,u,hi,v,ori=map(int,(i,lt,rt,lo,u,hi,v,ori));rawp=seed[i]
                assert don=='-1' and ((order,ori) not in [('012',0),('210',7)])
                frags=[rawp[lt:lo],rawp[lo+u:hi],rawp[hi+v:len(rawp)-rt]]
                arcs=[frags[int(z)][::-1] if ori>>j&1 else frags[int(z)] for j,z in enumerate(order)]
                at=p.index(arcs[0][0])
                for z,g in zip(arcs,[int(g1),int(g2),0]):
                    assert p[at:at+len(z)]==z;at+=len(z)+g
                assert int(out)==len(set(p)-set(rawp))
            sets[1+(pr=='e')][n].setdefault(canon(w),[f.name,nline])
        f=f.with_suffix('.records')
        for nline,l in enumerate(f.read_text().splitlines(),1):
            n,w,*_=l.split();n=int(n);assert len(w)==n
            p=path(w);validate(p)
            if n>=189:sets[1+(pr=='e')][n].setdefault(canon(w),[f.name,nline])
report={}
for n in range(189,193):
    a=sets[1][n];b=sets[2][n];newone=set(a)-old[n];newtwo=set(b)-old[n]-set(a);combined=set(a)|set(b)
    (D/f'descendants{n}.words').write_text(''.join(w+'\n' for w in sorted(newtwo)))
    (D/f'combinednew{n}.words').write_text(''.join(w+'\n' for w in sorted(newone|newtwo)))
    if newone or newtwo:(D/f'combinednew{n}_sources.json').write_text(json.dumps({w:(a[w] if w in newone else b[w]) for w in sorted(newone|newtwo)},indent=1))
    if newtwo:(D/f'descendants{n}_sources.json').write_text(json.dumps({w:b[w] for w in sorted(newtwo)}))
    report[n]={'first_all_records':len(a),'first_outside':len(newone),'second_all_records':len(b),'second_further':len(newtwo),'combined_classes':len(combined),'combined_outside':len(newone|newtwo)}
print(json.dumps(report,indent=2))
