"""Independently replace any collection of short projected subpaths by other routes of equal length."""
import argparse,json
from itertools import permutations
from pathlib import Path
from punctured_lift import project
from solve import BANK,BANK_HASH,sha256,save,defects


def add_sites(trace,width):
    domain=[{v} for v in trace]
    for i in range(len(trace)-width):
        bits=[v^w for v,w in zip(trace[i:i+width],trace[i+1:i+width+1])]
        for order in set(permutations(bits)):
            x=trace[i]
            for j,b in enumerate(order,1):
                x^=b;domain[i+j].add(x)
            assert x==trace[i+width]
    return domain


def solve_domain(trace,dom,old,budget,desired=193):
    # Position-indexed CSP. Equal projected addresses are allowed in different
    # slots only as two consecutive copies in the erased-coordinate direction.
    from pysat.formula import IDPool
    from pysat.solvers import Solver
    from pysat.card import CardEnc,EncType
    pool=IDPool(); n=len(trace)
    # At each position choose an address and one of the four orientations:
    # singleton layer 0 or 1, or double 0→1 or 1→0.
    patterns=((0,),(1,),(0,1),(1,0))
    menus=[[(v,p) for v in sorted(options) for p in range(4)] for options in dom]
    choices=[{vp:pool.id((i,*vp)) for vp in menu} for i,menu in enumerate(menus)]
    with Solver(name="cadical195") as sat:
        def add(c):sat.add_clause(c)
        def eq1(lits):
            for c in CardEnc.equals(lits,bound=1,vpool=pool,encoding=EncType.seqcounter).clauses:add(c)
        doubles=[];atoms=[]
        for i,menu in enumerate(choices):
            eq1(list(menu.values()))
            flag=pool.id(("double",i));doubles.append(flag)
            options=[lit for (v,p),lit in menu.items() if p>=2]
            add([-flag,*options])
            for lit in options:add([-lit,flag])
            if i==0:
                for (v,p),lit in menu.items():
                    if patterns[p][0]!=0:add([-lit])
            # Occupancy variables per distinct possible lifted site at this slot
            # reduce far-pair clauses to one per offending occupied pair.
            at={}
            for v in dom[i]:
                for z in (0,1):
                    atom=pool.id(("occupy",i,v,z));at[v|(z<<8)]=atom
                    opts=[menu[v,p] for p,seq in enumerate(patterns) if z in seq]
                    add([-atom,*opts])
                    for t in opts:add([-t,atom])
            atoms.append(at)
            if i:
                for (u,p),lit in choices[i-1].items():
                    seq=patterns[p]; supports=[]
                    for (v,t),other in menu.items():
                        new=patterns[t]
                        if (u^v).bit_count()==1 and seq[-1]==new[0] and len(set(seq)&set(new))==1:
                            supports.append(other)
                    add([-lit,*supports])
        for j,at in enumerate(atoms):
            for i in range(j-1):
                prev=atoms[i]
                for x,lit in at.items():
                    # Repeated projected addresses cannot occur in separate
                    # slots: equal layers coincide, opposite layers are adjacent.
                    for w in (x,*[x^(1<<b) for b in range(9)]):
                        if w in prev:add([-lit,-prev[w]])
        target=desired-n
        for c in CardEnc.atleast(doubles,bound=target,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        layer=0;phases=[]
        for i,v in enumerate(trace):
            p=layer+2 if i in old else layer
            phases.extend(x if vp==(v,p) else -x for vp,x in choices[i].items())
            if i in old:layer^=1
        sat.set_phases(phases)
        sat.conf_budget(budget);yes=sat.solve_limited()
        r=dict(status="UNSAT" if yes is False else "OPEN" if yes is None else "FOUND",conflicts=sat.accum_stats()["conflicts"],
               positions=n,changed_positions=sum(len(s)>1 for s in dom),choices=sum(map(len,dom)))
        if yes:
            pos=set(sat.get_model());q=[]
            for menu in choices:
                v,p=next(vp for vp,x in menu.items() if x in pos)
                q.extend(v|(z<<8) for z in patterns[p])
            assert len(q)>=desired and not defects(q);r["vertices"]=q
        return r


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("source",type=int);p.add_argument("width",type=int)
    p.add_argument("--axes",type=int,nargs="*",default=list(range(9)));p.add_argument("--budget",type=int,default=20000)
    a=p.parse_args(); raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;q=json.loads(raw)[a.source]["vertex_sequence"]
    rows=[]
    for axis in a.axes:
        trace,old=project(q,axis);dom=add_sites(trace,a.width)
        assert all(v in s for v,s in zip(trace,dom))
        if not rows:assert solve_domain(trace,dom,set(old),150000,192)["status"]=="FOUND"
        r=solve_domain(trace,dom,set(old),a.budget);rows.append(dict(source=a.source,axis=axis,**r))
        save(Path(f"surface-reroute-{a.source}-{a.width}-{a.axes[0]}-{a.budget}.json"),rows)
        print(axis,r["status"],r["conflicts"],flush=True)
        if r["status"]=="FOUND":break
