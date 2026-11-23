from pathlib import Path
from collections import Counter
import hashlib,subprocess
D=Path(__file__).resolve().parent
def unpack(w):
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def wd(p):
    return ''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
def norm(w):
    seen={};return ''.join(str(seen.setdefault(c,len(seen))) for c in w)
def canonical(w):return min(norm(w),norm(w[::-1]))
def check(p):
    assert all(0<=v<512 for v in p) and len(p)==len(set(p)) and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return sum((a^b).bit_count()==1 for i,a in enumerate(p) for b in p[i+2:])
source=Path('q9_three_axis.in');words=source.read_text().splitlines();counts=Counter();bank=[]
for w in words:
    p=unpack(w);assert len(p)==193
    c=check(p);counts[c]+=1
    if c==1:bank.append(p)
assert counts=={1:2059,2:3003} and len({canonical(wd(p)) for p in bank})==2059
print("Input checked by pairwise Hamming distances:",dict(counts),"source SHA256",hashlib.sha256(source.read_bytes()).hexdigest())
def parse(donors,labels,flat=None):
    arcs=[];offset=0;ids=[]
    for lab in labels:
        i,side,interval=lab.split('/');i=int(i);ids.append(i);a,b=map(int,interval.split('-'))
        q=donors[i] if side=='0' else donors[i][::-1];segment=q[a:b+1];assert len(segment)==b-a+1
        piece=segment if flat is None else flat[offset:offset+len(segment)]
        assert norm(wd(piece))==norm(wd(segment)) and check(piece)==0;arcs.append(piece);offset+=len(segment)
    assert len(set(ids))==4 and (flat is None or offset==len(flat));return arcs
def validate_winner(p,arcs):
    assert check(p)==0
    for arc in arcs:
        start=min(p.index(v) for v in arc);assert p[start:start+len(arc)] in (arc,arc[::-1])
raw=subprocess.check_output(['python3',str(D/'control_input.py')],text=True).splitlines()
tmpl=unpack(raw[0]);donors=list(map(unpack,raw[1:]));assert len(set(map(canonical,raw[1:])))==4 and all(check(p)==1 for p in donors)
line=(D/'damaged_control.log').read_text()
labels=line.split(' donors ')[1].split(' changed ')[0].split();arcs=parse(donors,labels);assert all(tmpl[a:a+len(r)]!=r for a,r in zip((0,50,98,146),arcs))
w=list(map(int,line.split('vertices ')[1].split()));assert len(w)==192;validate_winner(w,arcs)
sc=(D/'sat_control.log').read_text().split();q=list(map(int,sc[2:]));assert int(sc[1])==len(q)-1>=191;validate_winner(q,arcs)
print("Four different one-chord donors repaired all four changed control pieces; direct and SAT controls independently verified at",len(w)-1,"and",len(q)-1,"edges.")
fields=[]
for l in (D/'wide.log').read_text().splitlines():
    if l.startswith('FIELD '):
        a,b=l.split(' vertices');flat=list(map(int,b.split()))
        arcs=parse(bank,a.split()[2:],flat)
        assert len(set(flat))==len(flat)
        graph=sum((v^(1<<d)) in setflat for setflat in [set(flat)] for v in flat for d in range(9))//2
        assert graph==len(flat)-4
        fields.append({v for s in arcs for v in s[2:-2]})
for name in ('search','wide'):
    lines=(D/(name+'.log')).read_text().splitlines()
    assert lines[-1].startswith('DONE') and not any(l.startswith('FOUND') for l in lines)
    print(name,lines[-1])
ref={canonical(w) for w in Path('q9_three_axis_191.in').read_text().splitlines()}
for name,expected in [('sat',list(range(1,len(fields)+1))),('stepping',list(range(1,len(fields)+1,3)))]:
    lines=(D/(name+'.log')).read_text().splitlines();assert lines[-1].startswith('DONE')
    visited=[];status=Counter();keys=set();seen={}
    for line in lines[:-1]:
        s=line.split();i=int(s[1]);visited.append(i);status[s[0]]+=1;fixed=fields[i-1]
        if s[0]=='DUP':
            assert fields[int(s[2])-1]==fixed;continue
        assert len(fixed)==int(s[2])
        if s[0]=='FOUND':
            w=list(map(int,s[4:]));assert len(w)>=192 and not check(w) and fixed<=set(w);keys.add(canonical(wd(w)))
    assert visited==expected
    print(name,"independently checked retained geometry on",len(expected),"queries",dict(status),"witness classes",len(keys),"outside 131-class comparison",len(keys-ref))

cl=(D/'caps.log').read_text().splitlines();assert cl[-1]==(D/'wide.log').read_text().splitlines()[-1]
caps=[l for l in cl if l.startswith('REPLAY ')];assert len(caps)==int(cl[-1].split(' incomplete ')[1].split()[0])
cs=(D/'cap_sat.log').read_text().splitlines();assert cs[-1].startswith('DONE') and len(cs)==len(caps)+1
cf=[];capstatus=Counter()
for i,(a,z) in enumerate(zip(caps,cs),1):
    desc,num=a.split(' vertices');raw=list(map(int,num.split()));arcs=parse(bank,desc.split()[2:],raw)
    fixed=set(raw);assert len(raw)==len(fixed)
    s=z.split();assert int(s[1])==i
    if s[0]=='DUP':assert cf[int(s[2])-1]==fixed
    else:
        assert int(s[2])==len(fixed)
        if s[0]=='FOUND':validate_winner(list(map(int,s[4:])),arcs)
    cf.append(fixed);capstatus[s[0]]+=1
print("Independently reconstructed initially capped systems; SAT at least 192",dict(capstatus))
initial=(D/'stepping.log').read_text().splitlines()[:-1];known191={canonical(wd(list(map(int,l.split()[4:])))) for l in initial if l.startswith('FOUND')}
limits={int(l.split()[1]) for l in initial if l.startswith('LIMIT')}
rerun=set();rs=Counter()
for line in (D/'retry191.log').read_text().splitlines():
    idx,status,*nums=line.split();i=int(idx);assert i in limits;rerun.add(i);rs[status]+=1
    if status=='YES':
        w=list(map(int,nums));assert len(w)==192 and not check(w) and fields[i-1]<=set(w);known191.add(canonical(wd(w)))
assert rerun==limits
print("191 retry",dict(rs),"total 191 classes",len(known191),"outside reference",len(known191-ref))

