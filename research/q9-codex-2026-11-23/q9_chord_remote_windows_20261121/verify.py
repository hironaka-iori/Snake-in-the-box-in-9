from pathlib import Path
from collections import Counter,defaultdict
import hashlib,subprocess
D=Path(__file__).resolve().parent
def defects(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p) and all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    return [(i,j) for i,x in enumerate(p) for j in range(i+2,len(p)) if (x^p[j]).bit_count()==1]
def key(p):
    def enc(q):
        m={};return tuple(m.setdefault(x^y,len(m)) for x,y in zip(q,q[1:]))
    return min(enc(p),enc(p[::-1]))
def read_vertices(f):return [list(map(int,l.split())) for l in Path(f).read_text().splitlines()]
source=Path('q9_all_newsingle_hinge.vertices');bank=read_vertices(source)
bad=[defects(p) for p in bank];assert len(bank)==len({key(p) for p in bank})==58 and all(len(p)==193 for p in bank) and all(len(c)==1 for c in bad)
old={key(p) for p in read_vertices('q9_onechord_expanded_800.txt')}
assert len(old)==800 and old.isdisjoint(key(p) for p in bank)
print("Verified 58 distinct 192-edge single-chord input classes, each outside the 800 reference classes; file SHA256",hashlib.sha256(source.read_bytes()).hexdigest())
p=list(map(int,subprocess.check_output(['python3',str(D/'control_input.py')]).split()))
assert len(defects(p))==1 and len(p)==192
line=(D/'control.log').read_text();windows=list(map(int,line.split(' windows ')[1].split(' piece_order')[0].split()));assert windows==[13,17,2,6]
parts=[tuple(map(int,z.split('-'))) for z in line.split('piece_order ')[1].split(' vertices')[0].split()]
w=list(map(int,line.split('vertices ')[1].split()));assert len(w)==192 and not defects(w)
order=[];fixed=set()
for a,b in sorted(parts):
    part=p[a:b+1];fixed.update(part);i=min(map(w.index,part));assert w[i:i+len(part)] in (part,part[::-1]);order.append(i)
assert order not in (sorted(order),sorted(order,reverse=True))
assert not set(w)<=set(p)
sv=set(map(int,(D/'subset_control.log').read_text().split('vertices ')[1].split()))
sw=list(map(int,(D/'sat_control.log').read_text().split()[1:]))
assert len(sw)==192 and not defects(sw) and fixed<=set(sw)
assert len(sv)==192 and fixed<=sv
deg={x:sorted(v for v in sv if (v^x).bit_count()==1) for x in sv}
u,v=[x for x in sv if len(deg[x])==1];seq=[u];left=sv-{u}
while left:
    t,=left.intersection(deg[seq[-1]]);seq.append(t);left.remove(t)
assert seq[-1]==v and not defects(seq)
print("Three 191-edge positive controls passed, including a genuine reordering of the original retained blocks",order)
def entries(width):
    expected=[]
    for row,(p,chords) in enumerate(zip(bank,bad)):
        unique={};raw=0
        for end in chords[0]:
            a=max(0,end-width//2);b=min(len(p)-1,end+width//2)
            for c in range(len(p)-width+1):
                e=c+width-1
                if not (e+1<a or b+1<c):continue
                raw+=1
                fixed=set(range(len(p)))-set(range(a,b+1))-set(range(c,e+1))
                retained=tuple(i for i in sorted(fixed) if i-1 in fixed or i+1 in fixed)
                unique.setdefault(retained,(row,a,b,c,e))
        expected.append((raw,set(unique.values())))
    return expected
def cases(f,tag):return {tuple(map(int,l.split()[1:6])) for l in f.read_text().splitlines() if l.startswith(tag+' ')}
def rows(f):return [l.split() for l in f.read_text().splitlines() if l.startswith('ROW ')]
for width in (5,11,17,23):
    exp=entries(width);f=D/f'width{width}.log';a=rows(f)
    assert len(a)==58 and f.read_text().splitlines()[-1].startswith('DONE')
    u=cases(f,'INCOMPLETE')
    assert all((int(r[1]),int(r[3]),int(r[5]),int(r[7]))==(i,len(z),len({key for key in u if key[0]==i}),raw-len(z)) for i,((raw,z),r) in enumerate(zip(exp,a)))
    assert u.issubset(set.union(*(z for _,z in exp)))
    n=sum(len(z) for _,z in exp)
    if width==5:
        other=rows(D/'subset5.log')
        assert len(other)==58 and all(int(r[3])==len(z) and int(r[5])==0 for (_,z),r in zip(exp,other))
    if width==17:
        retry=rows(D/'width17_retry.log')
        assert len(retry)==58 and sum(int(r[3]) for r in retry)==len(u) and not cases(D/'width17_retry.log','INCOMPLETE')
    unresolved=u.copy()
    if width>=17:
        sat=D/f'sat{width}.log';no=cases(sat,'UNSAT');lim=cases(sat,'LIMIT');yes=cases(sat,'FOUND')
        assert not yes and no|lim==u and not no&lim
        unresolved-=no
        if width==17:unresolved.clear()
    print("Window width",width,"placements",sum(raw for raw,_ in exp),"distinct fixed sets counted per input",n,"initial port cutoffs",len(u),"resolved negative",n-len(unresolved),"still unresolved",len(unresolved))

grp=D/'grouped_lower.log'
logs=grp.read_text().splitlines(); assert logs[-1]=='DONE'
gno=cases(grp,'UNSAT');glim=cases(grp,'LIMIT');assert not cases(grp,'FOUND')
expected=set();covered=set();total=set()
for row,(p,cuts) in enumerate(zip(bank,bad)):
    for tip in cuts[0]:
        xa=max(0,tip-11);xb=min(192,tip+11)
        a=max(0,tip-13);b=min(192,tip+13)
        for c in range(0,len(p)-22,12):
            last=min(len(p)-23,c+11);e=last+22
            case=(row,a,b,c,e);expected.add(case)
            for j in range(c,last+1):
                k=j+22
                if not(k+1<xa or xb+1<j):continue
                kcase=(row,xa,xb,j,k);total.add(kcase)
                if case in gno:covered.add(kcase)
assert gno|glim==expected and not gno&glim
gc=(D/'group_control.log').read_text().split();assert gc[0]=='FOUND'
gw=list(map(int,gc[2:]));assert len(gw)-1==int(gc[1])>=190 and not defects(gw)
print("At-least-192 enlarged window systems",len(expected),"UNSAT",len(gno),"unresolved",len(glim),"nominal 23-wide physical window placements covered by UNSAT supersets",len(covered),"of",len(total))

