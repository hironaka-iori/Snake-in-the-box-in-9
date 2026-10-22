"""Test three five-centre windows on one common selected-vertex set.

The 94/94/71 values are collaborator solver records. Any UNSAT result here
remains solver evidence until independently certified and geometrically bridged.
"""
import argparse,hashlib,itertools,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'milestones/28-direct-share-certificates/scripts'),str(ROOT/'work/share_packages'),str(ROOT/'work/solver_packages'),str(ROOT/'milestones/10-window-aggregate/scripts')]
from direct import model,census,cp_model,window
from gen_lean_sat import TaggedEncoding
from pysat.solvers import Cadical153

def canonical(ds):
    names={};out=[]
    for d in ds:
        if d not in names:names[d]=len(names)
        out.append(names[d])
    return tuple(out)
def dkey(ds):return min(canonical(ds),canonical(ds[::-1]))
def candidates():
    A=dkey((0,1,2,3,0,4));B=dkey((0,1,2,3,0,1));shapes=[()]
    for length in range(8):
        nxt=[]
        for ds in shapes:
            for d in range(min(max(ds,default=-1)+2,9)):
                x=ds+(d,);p=window(x)
                if len(p)==len(set(p)) and all((p[i]^p[j]).bit_count()!=1 for i in range(len(p)) for j in range(i+2,len(p))):nxt.append(x)
        shapes=nxt
    rows=[]
    for ds in shapes:
        ks=[dkey(ds[i:i+6]) for i in range(3)]
        if sorted(ks)==sorted([A,A,B]):rows.append(dict(dirs=list(ds),types=['A' if k==A else 'B' for k in ks],caps=[94 if k==A else 71 for k in ks]))
    assert len(shapes)==132 and len(rows)==4
    return rows
def plain(case,seconds):
    t=time.monotonic();W=window(case['dirs']);enc=TaggedEncoding(W,[(4,4)]*7,radius=4);cuts=[];iterations=[];status='UNKNOWN';selected=None
    with Cadical153(bootstrap_with=enc.clauses) as s:
        deadline=time.monotonic()+seconds
        while time.monotonic()<deadline:
            s.conf_budget(10000);ok=s.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            m=s.get_model();S={v for v in enc.ball if m[enc.var[v]-1]>0};c=census(S,9,W[1:-1])
            if not c['cycles']:status='SAT';selected=sorted(S);break
            for cc in c['cycles']:cuts.append(cc);s.add_clause([-enc.var[v] for v in cc])
    out=dict(case,status=status,selected=selected,cycle_cuts=cuts,seconds=round(time.monotonic()-t,3))
    if selected:
        c.pop('degree');out['census']=c;out['five_window_shares']=[sum(c['share'][i:i+5]) for i in range(3)]
    return out
def joint(case,seconds,mode):
    t=time.monotonic();md,x,total,W,B,cuts=model(9,case['dirs'],[(4,4)]*7)
    # Recover the model's exact quotient variables, not unary approximations.
    q={int(v.name[1:]):md.get_int_var_from_proto_index(i) for i,v in enumerate(md.proto.variables) if v.name.startswith('u')}
    shares=[]
    for i,c in enumerate(W[1:-1],1):
        terms=[q[c^(1<<j)] for j in range(9) if c^(1<<j) not in (W[i-1],W[i+1])]
        shares.append(sum(terms))
    five=[sum(shares[i:i+5]) for i in range(3)]
    if mode=='individual':
        for s,cap in zip(five,case['caps']):md.add(s<=cap)
    elif mode=='total':md.add(sum(five)<=259)
    else:raise ValueError(mode)
    initial=len(cuts);added=[];iterations=[];deadline=time.monotonic()+seconds;status='UNKNOWN';selected=None
    while time.monotonic()<deadline:
        solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=max(.01,deadline-time.monotonic());solver.parameters.num_search_workers=2;solver.parameters.random_seed=196
        st=solver.solve(md);status=solver.status_name(st);iterations.append(dict(status=status,seconds=solver.wall_time,conflicts=solver.num_conflicts,branches=solver.num_branches))
        if st not in (cp_model.OPTIMAL,cp_model.FEASIBLE):break
        S={v for v in B if solver.value(x[v])};c=census(S,9,W[1:-1]);assert c['share']==[solver.value(s) for s in shares]
        if not c['cycles']:selected=sorted(S);break
        for cc in c['cycles']:
            assert frozenset(cc) not in cuts;cuts.add(frozenset(cc));added.append(cc);md.add(sum(x[v] for v in cc)<=len(cc)-1)
    out=dict(case,mode=mode,status=status,selected=selected,initial_cycle_cuts=initial,cycle_cuts=added,iterations=iterations,seconds=round(time.monotonic()-t,3),ball_vertices=len(B))
    if selected:
        c.pop('degree');out['census']=c;out['five_window_shares']=[sum(c['share'][i:i+5]) for i in range(3)]
    return out
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=['plain','individual','total'],default='plain');ap.add_argument('--seconds',type=float,default=30);ap.add_argument('--case',type=int);a=ap.parse_args()
    rows=candidates();(HERE/'data/candidates.json').write_text(json.dumps(rows,indent=2)+'\n')
    for i,case in enumerate(rows):
        if a.case is not None and a.case!=i:continue
        result=plain(case,a.seconds) if a.mode=='plain' else joint(case,a.seconds,a.mode)
        result['script_sha256_lf']=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
        (HERE/'data'/f'{a.mode}-{i}.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:v for k,v in result.items() if k not in ('selected','cycle_cuts','iterations','census')}),flush=True)
if __name__=='__main__':main()
