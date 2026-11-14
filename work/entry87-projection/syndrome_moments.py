"""Exact necessary incidence counts for hypothetical odd-dimensional snakes."""
import argparse,json
from pathlib import Path
from ortools.sat.python import cp_model
from solve import BANK,save


def moment(size_even,size_odd,ends_even,ends_odd,extremum,side=None,limit=60):
    m=cp_model.CpModel();classes=[]
    for n,selected_other,opposite_ends in ((size_even,size_odd,ends_odd),(size_odd,size_even,ends_even)):
        bins=[m.new_int_var(0,256,"n"+str(len(classes))+"_"+str(k)) for k in range(10)]
        m.add(sum(bins)==256);m.add(sum(k*v for k,v in enumerate(bins))==9*n)
        m.add(bins[1]>=opposite_ends);m.add(bins[2]>=selected_other-opposite_ends)
        sig=sum(bins[k] for k in (1,3,5,7,9));multiple=m.new_int_var(-64,64,"mod"+str(n))
        m.add(sig==n+4*multiple)
        # Second moment counts every distance-two pair twice. Third moment
        # then enforces the separate modulo-eight identity for this side.
        dist=m.new_int_var(0,4608,"dist"+str(n))
        m.add(sum((k*(k-1)//2)*v for k,v in enumerate(bins))==2*dist)
        triples=sum((k*(k-1)*(k-2)//6)*v for k,v in enumerate(bins))
        z=m.new_int_var(-12000,12000,"mod8"+str(n))
        m.add(sig==9*n-4*dist+4*triples+8*z)
        classes.append((sig,bins))
    objective=sum(p[0] for p in classes) if side is None else classes[side][0]
    if extremum=="max":m.maximize(objective)
    else:m.minimize(objective)
    s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.max_time_in_seconds=limit
    status=s.solve(m);return dict(status=s.status_name(status),value=int(s.value(objective)),
                                 bins=[[s.value(v) for v in row] for _,row in classes])


if __name__=="__main__":
    rows={}
    for which in ("min","max"):
        rows[which]=moment(97,96,2,0,which)
    # For Y the induced odd-degree sources are the same two endpoints, by
    # D²=I. The following range uses exact integer counting at class level.
    possibilities=[]
    for e in range(0,162,4):
        for o in range(1,162,4):
            # e even-coloured Y sites include the pair of endpoints. Each
            # neighbour count on Y gives at most 9 times its size under D.
            if e<2 or 9*e<96 or 9*o<97:continue
            if e>256-97+2 or o>256-96:continue
            possibilities.append((e,o))
    rows["elementary_window"]=[min(sum(t) for t in possibilities),max(sum(t) for t in possibilities)]
    save(Path("syndrome-incidence-window.json"),rows);print(rows,flush=True)
