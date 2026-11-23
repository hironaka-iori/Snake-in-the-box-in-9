import sys,json
from pathlib import Path
from itertools import combinations
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
here=Path(__file__).resolve().parent
def stats(p):
    assert len(set(p))==len(p) and all(0<=x<512 for x in p) and all((v^w).bit_count()==1 for v,w in zip(p,p[1:]))
    return sum((v^w).bit_count()==1 and j!=i+1 for (i,v),(j,w) in combinations(enumerate(p),2))
def key(p):
    def form(seq):
        d={};return tuple(d.setdefault(a^b,len(d)) for a,b in zip(seq,seq[1:]))
    return min(form(p),form(p[::-1]))
def base(p,d):
    out=[]
    for x in p:
        y=(x&((1<<d)-1))|((x>>(d+1))<<d)
        if not out or out[-1]!=y:out.append(y)
    return out
def exact(q,target):
    if len(set(q))!=len(q):return 'UNSAT'
    n=len(q);f=[];switch=list(range(n+2,2*n+2))
    # c[i], c[i+1] are entry and exit colours in column i.
    for i,s in enumerate(switch):
        a=i+1;b=i+2
        f.extend([[-a,-b,-s],[a,b,-s],[a,-b,s],[-a,b,s]])
        if i:f.append([-switch[i-1],-s])
    for i,u in enumerate(q):
        for j in range(i+2,n):
            if (u^q[j]).bit_count()==1:
                f.extend([[-switch[i]],[-switch[j]],[i+1,j+1],[-(i+1),-(j+1)]])
    required=target-(n-1)
    if required>n:return 'UNSAT'
    if required>0:f.extend(CardEnc.atleast(switch,bound=required,top_id=2*n+1,encoding=EncType.seqcounter).clauses)
    with Solver(name='cadical195',bootstrap_with=f) as s:
        if not s.solve():return 'UNSAT'
        M=set(s.get_model())
    out=[]
    for i,v in enumerate(q):
        out.append(v+256*(i+1 in M))
        if switch[i] in M:out.append(v+256*(i+2 in M))
    assert len(out)-1>=target and not stats(out)
    return 'SAT'
def main():
    files=['q9_onechord_expanded_800.txt','q9_all_newsingle_hinge.vertices']
    inputs=[[list(map(int,l.split())) for l in (here.parent/name).read_text().splitlines()] for name in files]
    assert [len(x) for x in inputs]==[800,58] and all(len(p)==193 and stats(p)==1 for bank in inputs for p in bank)
    assert len({key(p) for bank in inputs for p in bank})==858
    print('Pairwise verified 858 distinct single-chord inputs')
    for name in ['control','detour-control','new-full','new-swap','old-identity','old-swap','detour-new','detour-old']:
        lines=(here/(name+'.log')).read_text().splitlines()
        count=0
        for idx,line in enumerate(lines):
            if line.startswith('BASE '):
                source=list(map(int,line.split()[1:]));assert exact(source,191)=='UNSAT'
            if not (line.startswith('WITNESS ') or line.startswith('DETOUR ')):continue
            h=line.split();score=int(h[1]);row=int(h[3]);axis=int(h[5])
            if not name.endswith('control'):source=base(inputs[int('new' in name)][row],axis)
            p=list(map(int,lines[idx+1].split()[1:]));assert len(p)==score+1 and not stats(p);count+=1
            result=source.copy();i,j=int(h[7]),int(h[9])
            if h[0]=='DETOUR':
                result=result[:i+1]+list(map(int,h[11:]))+result[j:]
            elif i>=0:
                rev,a,b,tr=map(int,(h[11],h[13],h[14],h[16]));seg=result[i:j+1]
                if rev:seg.reverse()
                mask=(1<<a)|(1<<b)
                result[i:j+1]=[x^tr^(mask if ((x>>a)^(x>>b))&1 else 0) for x in seg]
            assert base(p,8)==result and exact(result,score)=='SAT'
        if name.endswith('control'):assert count>0
        else:assert lines[-1].startswith('DONE ')
        print(name,'verified witnesses',count,flush=True)
if __name__=='__main__':main()
