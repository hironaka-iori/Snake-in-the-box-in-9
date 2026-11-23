from itertools import combinations
from pathlib import Path
import subprocess,sys
D=Path(__file__).resolve().parent
cube=[tuple(v^(1<<k) for k in range(9)) for v in range(512)]
exe=Path.home()/".elan/toolchains/leanprover--lean4---v4.19.0/bin/cadical"
def graph(fixed,target,at_least=False):
    n=target+1
    deg=[len(set(row)&fixed) for row in cube]
    assert all(deg[v]<=2 for v in fixed)
    sat={v for v in fixed if deg[v]==2}
    free={v for v in range(512) if v not in fixed and deg[v]<=2 and sat.isdisjoint(cube[v])}
    clauses=[]; top=1024
    def add(*row):clauses.append(row)
    def atmost(lits,k):
        nonlocal top
        if k<0:add();return
        if k>=len(lits):return
        if k==0:
            for t in lits:add(-t)
            return
        def build(a):
            nonlocal top
            if len(a)==1:return a
            mid=len(a)//2;x=build(a[:mid]);y=build(a[mid:])
            out=list(range(top+1,top+min(len(a),k+1)+1));top+=len(out)
            for i in range(len(x)+1):
                for j in range(min(len(y),len(out)-i)+1):
                    if i+j==0:continue
                    add(*([-x[i-1]] if i else []),*([-y[j-1]] if j else []),out[i+j-1])
            return out
        add(-build(lits)[k])
    def exactly(lits,k):
        atmost(lits,k);atmost([-x for x in lits],len(lits)-k)
    need=n-len(fixed)
    if at_least:atmost([-v-1 for v in sorted(free)],len(free)-need)
    else:exactly([v+1 for v in sorted(free)],need)
    ends=[]
    for v in sorted((fixed|free)-sat):
        e=513+v;ends.append(e)
        guard=[] if v in fixed else [-v-1];zs=[w+1 for w in cube[v] if w in free]+[e]
        if guard:add(-e,v+1)
        k=2-deg[v]
        if not 0<=k<=len(zs):add(*guard);continue
        for z in combinations(zs,k+1):add(*guard,*[-t for t in z])
        for z in combinations(zs,len(zs)-k+1):add(*guard,*z)
    exactly(ends,2)
    for color in (0,1):
        f=sum(v.bit_count()%2==color for v in fixed)
        vs=[v+1 for v in free if v.bit_count()%2==color]
        if not at_least:atmost(vs,(n+1)//2-f)
        atmost([-t for t in vs],len(vs)-(n//2-f))
    root=min(fixed);calls=0
    while calls<20:
        calls+=1
        dimacs='p cnf %d %d\n'%(top,len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
        proc=subprocess.run([str(exe),'-q','-c','30000'],input=dimacs,text=True,capture_output=True)
        if proc.returncode==20:return 'UNSAT',calls,None
        if proc.returncode==0:return 'LIMIT',calls,None
        assert proc.returncode==10,(proc.returncode,proc.stderr)
        model={int(t) for l in proc.stdout.splitlines() if l.startswith('v ') for t in l.split()[1:]}
        selected=fixed|{v for v in free if v+1 in model}
        assert len(selected)>=n and (at_least or len(selected)==n)
        rest=set(selected);groups=[]
        while rest:
            part=[rest.pop()]
            for v in part:
                for w in cube[v]:
                    if w in rest:rest.remove(w);part.append(w)
            groups.append(part)
        if len(groups)==1:
            endpoint,other=(v for v in selected if len(selected.intersection(cube[v]))==1)
            walk=[endpoint];left=selected-{endpoint}
            while left:
                w,=left.intersection(cube[walk[-1]]);left.remove(w);walk.append(w)
            assert walk[-1]==other
            return 'FOUND',calls,walk
        for part in groups:
            if root in part:continue
            boundary=sorted(({x for v in part for x in cube[v]}&free)-set(part))
            guard=[] if fixed.intersection(part) else [-min(part)-1]
            add(*guard,*[w+1 for w in boundary])
    return 'LIMIT',calls,None
def keep(p,a,b,c,e):
    rem=[not(a<=i<=b or c<=i<=e) for i in range(len(p))]
    return {v for i,v in enumerate(p) if rem[i] and ((i and rem[i-1]) or (i+1<len(p) and rem[i+1]))}
if __name__=='__main__':
    if sys.argv[1]=='control':
        p=list(map(int,subprocess.check_output(['python3',str(D/'control_input.py')]).split()))
        state,n,w=graph(keep(p,13,17,2,6),191);assert state=='FOUND'
        print(state,*w);sys.exit()
    bank=[list(map(int,l.split())) for l in Path('q9_all_newsingle_hinge.vertices').read_text().splitlines()]
    def source_rows():
        import time
        with Path(sys.argv[1]).open() as f:
            while True:
                line=f.readline()
                if line:
                    yield line
                    if line.startswith("DONE") or line.startswith("FOUND"):return
                elif len(sys.argv)>2 and sys.argv[2]=="follow":time.sleep(0.3)
                else:return
    for line in source_rows():
        if line.startswith('INCOMPLETE'):
            row,a,b,c,e,*_=map(int,line.split()[1:])
            state,n,w=graph(keep(bank[row],a,b,c,e),192)
            print(state,row,a,b,c,e,n,*(w or []),flush=True)
            if w:break

