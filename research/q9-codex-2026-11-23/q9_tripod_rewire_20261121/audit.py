from pathlib import Path
import itertools
import json
import collections
import sys
BASE=Path(__file__).resolve().parent
def path(w,start=0):
    a=[start]
    for c in w:a.append(a[-1]^1<<int(c))
    return a
def validate(a):
    assert len(a)==len(set(a)) and all(0<=v<512 for v in a)
    assert all(((v^u).bit_count()==1)==(j==i+1) for i,v in enumerate(a) for j,u in enumerate(a) if i<j)
def normalized(w):
    d={};return ''.join(str(d.setdefault(v,len(d))) for v in w)
def key(w):return min(normalized(w),normalized(w[::-1]))
words=(BASE/'arms.words').read_text().split()
with (BASE/'provenance.json').open() as f:provenance=json.load(f)
for w in words:
    mode,i,m=provenance[w];mask=int(m,16);pts=[v for v in range(512) if mask>>v&1]
    ns={v:[z for z in pts if (v^z).bit_count()==1] for v in pts}
    center,=[v for v,g in ns.items() if len(g)==3];real=[]
    for v in ns[center]:
        p=[center,v]
        while len(ns[p[-1]])==2:p.append(next(z for z in ns[p[-1]] if z!=p[-2]))
        real.append(''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:])))
    def normarm(s):
        d={};return ''.join(':' if v==':' else str(d.setdefault(v,len(d))) for v in s)
    assert len(pts)==193 and min(normarm(':'.join(pp)) for pp in itertools.permutations(real))==w
    assert sorted(map(len,ns.values()))==[1]*3+[2]*189+[3]
bank={key(w) for w in (BASE.parent/'q9_far189_spring_20261121/comparison191.words').read_text().split()}
results={}
allkeys=set();cores=set()
for f in sys.argv[1:]:
    s=set();genuine=0;bothnew=0;max_out=-1;label=None;n=0
    for line in (BASE/(f+'.long')).read_text().splitlines():
        length,out,tag,b1,b2,start,w=line.split()
        p=path(w,int(start));validate(p);assert len(p)==int(length)+1
        idx,middle,flips,*data=map(int,tag.split(','));trims=data[:6];twist=data[6:]
        arms=[path(z)[1:] for z in words[idx].split(':')]
        host={0}|set(sum(arms,[]))
        assert len(host)==193 and len(set(p)-host)==int(out)
        pieces=[]
        for k,i in enumerate([(middle+1)%3,middle,(middle+2)%3]):
            a,b=trims[2*i:2*i+2];q=arms[i][a:len(arms[i])-b]
            pieces.append(q[::-1] if flips>>k&1 else q)
        if twist:
            pid,a,b=twist[:3];shift=len(twist)>3;anchor=pieces[pid][0];ma=1<<a;mb=1<<b
            pieces[pid]=[v^(ma|mb) if shift or bool((v^anchor)&ma)!=bool((v^anchor)&mb) else v for v in pieces[pid]]
        i=p.index(pieces[0][0])
        assert p[i:i+len(pieces[0])]==pieces[0];j=i+len(pieces[0])
        j2=j+int(b1);assert p[j2:j2+len(pieces[1])]==pieces[1]
        k=j2+len(pieces[1]);k2=k+int(b2);assert p[k2:k2+len(pieces[2])]==pieces[2]
        cores.add(key(w[i:k2+len(pieces[2])-1]))
        nb=sum(bool(set(x)-host) for x in (p[j:j2],p[k:k2]))
        genuine+=int(int(b1)>0 and int(b2)>0);bothnew+=nb==2
        if int(out)>max_out:max_out=int(out);label=tag
        s.add(key(w));n+=1
    allkeys|=s
    results[f]={'records':n,'classes':len(s),'outside_catalogue':len(s-bank),'both_bridges_nonempty':genuine,'both_bridges_use_outside_vertex':bothnew,'max_outside':max_out,'max_outside_tag':label}
for name in ['f7','f16','c12','control191']:
    for line in (BASE/(name+'.records')).read_text().splitlines():
        length,w,*rest=line.split();p=path(w);validate(p);assert len(p)==int(length)+1
results['combined191']={'classes':len(allkeys),'new_against_131':len(allkeys-bank)}
(BASE/'checked_cores.words').write_text(''.join('191 '+w+'\n' for w in sorted(cores)))
results['distinct_witness_cores']=len(cores)
print(json.dumps(results,indent=2))
