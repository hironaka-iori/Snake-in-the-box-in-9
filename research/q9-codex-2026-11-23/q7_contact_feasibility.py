"""Contact feasibility against one 52-edge Q7 forest; each rejection has a SAT trace."""
import argparse,gzip,itertools,json,subprocess,tempfile
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import CNF
from pysat.solvers import Cadical195
ROOT=Path(__file__).resolve().parent
NEIGH=[{v^(1<<i) for i in range(7)} for v in range(128)]
def catalogue():
    out=[]
    for row in (ROOT/"q7_extreme_interfaces.pts").read_text().splitlines():
        a,b=(int(s,16) for s in row.split())
        M=a|(b<<64);S={v for v in range(128) if M>>v&1}
        assert len(S)==56 and sum(len(S&NEIGH[v]) for v in S)==104
        out.append(S)
    return out
def make(A,contact,edges=51,size=55):
    tips={v for v in A if len(NEIGH[v]&A)==1}
    assert len(tips)==8
    allow=set(range(128))-(A-tips)
    form=CNF();top=128
    def card(xs,b,exact=False):
        nonlocal top
        f=(CardEnc.equals if exact else CardEnc.atleast)(xs,bound=b,top_id=top,encoding=EncType.totalizer)
        form.extend(f.clauses);top=max(top,f.nv)
    card([v+1 for v in sorted(allow)],abs(size),size>0)
    card([v+1 for v in sorted(tips)],contact)
    ys=[]
    for v in sorted(allow):
        ns=sorted(NEIGH[v]&allow)
        for bad in itertools.combinations(ns,2 if v in tips else 3):
            form.append([-v-1]+[-w-1 for w in bad])
        for w in ns:
            if v<w:
                top+=1;ys.append(top)
                form.extend([[-top,v+1],[-top,w+1],[top,-v-1,-w-1]])
    card(ys,edges)
    for v in sorted(allow):
        for a,b in itertools.combinations(range(7),2):
            D=(1<<a)|(1<<b)
            if not v&D:
                sq={v,v^(1<<a),v^(1<<b),v^D}
                if sq<=allow:form.append([-x-1 for x in sorted(sq)])
    return form,allow

def cycle_cuts(A,B):
    S=A|{v+128 for v in B};todo=set(S);cuts=[]
    while todo:
        root=todo.pop();seen={root};stack=[root];iscycle=True
        while stack:
            v=stack.pop();neighbors={v^(1<<i) for i in range(8)}&S
            assert len(neighbors)<=2
            if len(neighbors)!=2:iscycle=False
            new=neighbors-seen;seen.update(new);todo-=new;stack.extend(new)
        if iscycle:cuts.append(sorted(x-128 for x in seen if x>=128))
    return sorted(cuts)
def trial(A,contact,budget,edges,size):
    f,allow=make(A,contact,edges,size);cuts=[]
    for _ in range(40):
        with Cadical195(bootstrap_with=f,with_proof=True) as sat:
            sat.conf_budget(budget);ans=sat.solve_limited()
            if ans is None:return dict(status="UNKNOWN",cuts=cuts)
            if ans:
                m=set(sat.get_model());B={v for v in allow if v+1 in m}
                cycles=cycle_cuts(A,B)
                if not cycles:return dict(status="MODEL",B=sorted(B),cross=len(A&B),internal=sum(len(NEIGH[v]&B) for v in B)//2)
                cuts+=cycles
                for c in cycles:f.append([-v-1 for v in c])
                continue
            proof="\n".join(sat.get_proof())+"\n"
        return dict(status="UNSAT",cuts=cuts,proof=proof)
    return dict(status="UNKNOWN",cuts=cuts)
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--contact",type=int,default=4);p.add_argument("--budget",type=int,default=10000)
    p.add_argument("--edges",type=int,default=51);p.add_argument("--size",type=int,default=55);p.add_argument("--output",required=True)
    p.add_argument("rows",nargs="*",type=int);opt=p.parse_args();bank=catalogue()
    with gzip.open(opt.output,"wt") as out:
        for i in opt.rows or range(len(bank)):
            r=trial(bank[i],opt.contact,opt.budget,opt.edges,opt.size)
            print(i,r["status"],len(r.get("cuts",[])),flush=True)
            out.write(json.dumps(dict(row=i,contact=opt.contact,edges=opt.edges,size=opt.size,**r))+"\n");out.flush()

