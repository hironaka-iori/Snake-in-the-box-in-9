from pathlib import Path
from itertools import combinations
import sys,time
from pysat.card import CardEnc,EncType
from pysat.solvers import Cadical195
from pool_sat import NB,rows
D=Path(__file__).resolve().parent
def exact_cube(cells,edges=192,cap=125000):
    S=set(cells);n=edges+1;nb={v:NB[v]&S for v in S}
    # Every longer path in this optional-only domain has a contiguous n-vertex subpath.
    assert n%2
    overall='UNSAT'
    for majority in (0,1):
        top=1024;clauses=[]
        def count(lits,k):
            nonlocal top
            if k<0 or k>len(lits):clauses.append([]);return
            if not k:clauses.extend([[-v] for v in lits]);return
            if k==len(lits):clauses.extend([[v] for v in lits]);return
            cn=CardEnc.equals(lits,k,top_id=top,encoding=EncType.seqcounter);clauses.extend(cn.clauses);top=max(top,cn.nv)
        ends=[]
        for color in (0,1):
            vs=sorted(v for v in S if v.bit_count()%2==color)
            count([-v-1 for v in vs],len(vs)-(n//2+int(color==majority)))
            for v in vs:
                z=[u+1 for u in nb[v]]
                if color==majority:
                    e=513+v;z.append(e);ends.append(e);clauses.append([-e,v+1])
                for c in combinations(z,3):clauses.append([-v-1,*[-k for k in c]])
                if len(z)<2:clauses.append([-v-1])
                else:
                    for c in combinations(z,len(z)-1):clauses.append([-v-1,*c])
        count(ends,2)
        # A selected interior vertex of an unsubdivided degree-two chain connects to one of its ends.
        used=set()
        for x in S:
            if len(nb[x])==2:continue
            for y in nb[x]:
                if y in used or len(nb[y])!=2:continue
                path=[x];v=y;prev=x
                while len(nb[v])==2:
                    used.add(v);path.append(v);w,=nb[v]-{prev};prev,v=v,w
                path.append(v)
                if len(path)-2>=n:continue
                left=[0]*len(path);right=left[:];left[0]=path[0]+1;right[-1]=path[-1]+1
                for i in range(1,len(path)-1):
                    top+=1;left[i]=top;clauses.extend([[-top,left[i-1]],[-top,path[i]+1]])
                for i in range(len(path)-2,0,-1):
                    top+=1;right[i]=top;clauses.extend([[-top,right[i+1]],[-top,path[i]+1],[-path[i]-1,left[i],right[i]]])
        with Cadical195(bootstrap_with=clauses) as solver:
            for it in range(250):
                left=cap-solver.accum_stats()['conflicts']
                if left<=0:overall='LIMIT';break
                solver.conf_budget(left);ok=solver.solve_limited()
                if ok is False:break
                if ok is None:overall='LIMIT';break
                m=set(solver.get_model());sel={v for v in S if v+1 in m};assert len(sel)==n
                rest=set(sel);groups=[]
                while rest:
                    q=[rest.pop()]
                    for v in q:
                        k=nb[v]&rest;q.extend(k);rest-=k
                    groups.append(q)
                if len(groups)==1:
                    s=next(v for v in sel if len(nb[v]&sel)==1);walk=[s];rest=sel-{s}
                    while rest:
                        t,=nb[walk[-1]]&rest;rest.remove(t);walk.append(t)
                    return 'FOUND',walk
                groups.sort(key=len,reverse=True);out=groups[0][0]
                for g in groups[1:]:
                    border=set.union(*(nb[v] for v in g))-set(g)
                    solver.add_clause([-out-1,-g[0]-1,*[u+1 for u in border]])
            else:overall='LIMIT'
    return overall,None
if __name__=='__main__':
    if sys.argv[1]=='control':
        # Truncate one known control tip so that a 190-edge even-length target can be represented.
        for i in range(5):
            dom=rows(D/f'control{i}.in')[0];st,w=exact_cube(dom,190);assert st=='FOUND';print(i,*w)
        raise SystemExit
    hosts=list(map(set,rows('q8_all_191_positive.hosts')));source=Path(sys.argv[1])
    with source.open() as f:
        while True:
            line=f.readline()
            if not line:
                if len(sys.argv)>2 and sys.argv[2]=='follow':time.sleep(.25);continue
                break
            t=line.split()
            if t[0]=='DONE':break
            if t[0]!='LIMIT':continue
            i=int(t[1])
            if t[2]=='extras':ext=set(map(int,t[3:t.index('pins') if 'pins' in t else t.index('rounds')]))
            else:
                mask,base=map(int,t[2:4])
                if mask.bit_count()!=4:continue
                ext={v for v in range(512) if v&~mask==base}-hosts[i]
            st,w=exact_cube(hosts[i]|ext)
            print(st,i,'extras',*sorted(ext),'vertices',*(w or []),flush=True)
            if w:break
    print('DONE',flush=True)

