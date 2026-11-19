"""Exact dual upper bounds for rooted partners constrained by local Q4 path patterns."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from time import monotonic
import json
import sys

HERE=Path(__file__).resolve().parent
PREV=HERE.parent/"247-relative-middle-placements"
sys.path.insert(0,str(PREV))
from partner import parent_arms, rooted_parent, next_vertices, validate_prefix

Q=[tuple(v^(1<<j) for j in range(8)) for v in range(256)]
ORIENTATIONS=[(0,1,2,3),(4,5,6,7),(0,2,4,6),(1,3,5,7),(0,1,4,5),(2,3,6,7)]
D=10**6


def bits(mask):
    while mask:
        b=mask & -mask
        yield b.bit_length()-1
        mask-=b


def faces(axes):
    offsets=[0]
    for i in axes:
        offsets += [v|(1<<i) for v in offsets]
    return [(low,[low|v for v in offsets]) for low in range(256) if not low&offsets[-1]]


def graph(parent,prefix):
    validate_prefix(parent,prefix)
    fixed=set(prefix)
    free=set(range(256))-set(parent)-fixed
    for v in prefix[:-1]:
        free.difference_update(Q[v])
    reach={prefix[-1]}
    stack=list(reach)
    while stack:
        v=stack.pop()
        extra=(set(Q[v])&free)-reach
        reach.update(extra)
        stack.extend(extra)
    V=sorted(reach|fixed)
    S=set(V)
    N={v:sorted(S.intersection(Q[v])) for v in V}
    E=[(u,v) for u in V for v in N[u] if u<v]
    x={v:i for i,v in enumerate(V)}
    odd=[v for v in V if v.bit_count()%2 and v not in fixed]
    e={v:len(V)+i for i,v in enumerate(odd)}
    y={edge:len(V)+len(e)+i for i,edge in enumerate(E)}
    return V,N,x,e,y


def linear_rows(g,prefix,cutsets=()):
    V,N,x,e,y=g
    yield "eq",[(x[v],1 if v.bit_count()%2==0 else -1) for v in V],0
    yield "eq",[(idx,1) for idx in e.values()],1
    for v in prefix:
        yield "eq",[(x[v],1)],1
    for (a,b),z in y.items():
        yield "le",[(z,1),(x[a],-1)],0
        yield "le",[(z,1),(x[b],-1)],0
        yield "le",[(x[a],1),(x[b],1),(z,-1)],1
    for v in V:
        incident=[(y[tuple(sorted((v,w)))],1) for w in N[v]]
        terms=incident+[(x[v],-2)]
        if v in e:
            yield "le",[(e[v],1),(x[v],-1)],0
            terms.append((e[v],1))
        yield "eq",terms,-int(v==prefix[0])
    for dim,cap in ((2,3),(3,5)):
        for axes in combinations(range(8),dim):
            for _,face in faces(axes):
                vs=[v for v in face if v in x]
                if len(vs)>cap:
                    yield "le",[(x[v],1) for v in vs],cap
                if dim!=2 or len(vs)!=4:
                    continue
                edges=[(a,b) for a,b in combinations(sorted(vs),2) if (a,b) in y]
                # Disagreements around an occupied/unoccupied square form an even set.
                for signs in (1,3):
                    for positive in combinations(edges,signs):
                        coeff=Counter()
                        for a,b in edges:
                            sign=1 if (a,b) in positive else -1
                            coeff[x[a]]+=sign
                            coeff[x[b]]+=sign
                            coeff[y[a,b]]-=2*sign
                        yield "le",[(i,c) for i,c in sorted(coeff.items()) if c],signs-1
    for w,inside in cutsets:
        side=set(inside)
        if w not in side or prefix[0] in side or not side<=set(V):
            raise ValueError("Invalid anchored cut")
        terms=[(x[w],2)]+[(z,-1) for (a,b),z in y.items() if (a in side)!=(b in side)]
        terms.extend((e[v],-1) for v in sorted(side) if v in e)
        yield "le",terms,0


def patterns(g,prefix,axes,low):
    """Feature masks for the possible restrictions of a 96-vertex partner.

    The local graph is an induced forest of maximum degree two. Fixed external
    neighbours count toward degree; too few external choices can force the one
    odd terminal. Each local component must be able to leave this proper face.
    """
    V,N,x,e,y=g
    fixed=set(prefix)
    axes_mask=sum(1<<i for i in axes)
    F=[v for v in V if v&~axes_mask==low]
    ix={v:i for i,v in enumerate(F)}
    inner=[(a,b) for a,b in y if a in ix and b in ix]
    features=[x[v] for v in F]+[y[t] for t in inner]
    adj=[sum(1<<ix[w] for w in N[v] if w in ix) for v in F]
    edge_bits=[[(ix[a],1<<(len(F)+i)) for i,(a,b) in enumerate(inner) if b==v] for v in F]
    max_deg=[1 if v==prefix[0] else 2 for v in F]
    outside=[sum(w not in ix for w in N[v]) for v in F]
    imposed=[sum(w not in ix and w in fixed for w in N[v]) for v in F]
    mandatory=sum(1<<ix[v] for v in F if v in fixed)
    result=[]
    for mask in range(1<<len(F)):
        if mask&mandatory!=mandatory:
            continue
        needed=-1
        leaves=0
        exits=0
        word=mask
        for j in bits(mask):
            degree=(adj[j]&mask).bit_count()
            if degree+imposed[j]>max_deg[j]:
                break
            deficit=max_deg[j]-degree-outside[j]
            if deficit>0:
                if deficit!=1 or F[j] not in e or needed!=-1:
                    break
                needed=e[F[j]]
            if degree<=1:
                leaves |= 1<<j
            if degree<max_deg[j] and outside[j]:
                exits |= 1<<j
            for a,edge in edge_bits[j]:
                if mask & (1<<a):
                    word |= edge
        else:
            unseen=mask
            while unseen:
                comp=unseen & -unseen
                frontier=comp
                while frontier:
                    nxt=0
                    for j in bits(frontier):
                        nxt |= adj[j]
                    frontier=(nxt&mask)&~comp
                    comp |= frontier
                if not comp&leaves or not comp&exits:
                    break
                unseen &= ~comp
            if not unseen:
                result.append((word,needed))
    return features,result


def upper(g,prefix,cert):
    """Integer-only verification. No solver import is required."""
    V,N,x,e,y=g
    scale=cert["scale"]
    residual=[scale]*len(x)+[0]*(len(e)+len(y))
    rhs=0
    weights=dict(cert["base_weights"])
    rows=list(linear_rows(g,prefix,cert["cuts"]))
    if any(i<0 or i>=len(rows) for i in weights):
        raise ValueError("Unknown row")
    for i,w in weights.items():
        sense,terms,bound=rows[i]
        if sense=="le" and w<0:
            raise ValueError("Negative inequality weight")
        rhs+=w*bound
        for j,c in terms:
            residual[j]-=w*c
    for f in cert["face_weights"]:
        feature,masks=patterns(g,prefix,f["axes"],f["low"])
        coeff=f["coefficients"]
        price=dict(f["terminal_prices"])
        if len(coeff)!=len(feature) or any(w<0 or i not in e.values() for i,w in price.items()):
            raise ValueError("Bad face multipliers")
        maximum=max(sum(coeff[i] for i in bits(word))-price.get(needed,0) for word,needed in masks)
        if maximum!=f["maximum"]:
            raise ValueError("Incorrect face maximum")
        rhs+=maximum
        for j,w in zip(feature,coeff):
            residual[j]-=w
        for j,w in price.items():
            residual[j]+=w
    return rhs+sum(max(0,r) for r in residual)


def violated_cuts(g,vars_,root,seen):
    V,N,x,e,y=g
    vx={v:vars_[i].solution_value() for v,i in x.items()}
    ey={edge:vars_[i].solution_value() for edge,i in y.items()}
    result=[]
    for threshold in (0.05,0.2,0.45,0.7):
        unseen=set(V)
        while unseen:
            w=min(unseen)
            group={w}
            stack=[w]
            while stack:
                v=stack.pop()
                new={u for u in N[v] if u not in group and ey[tuple(sorted((u,v)))]>threshold}
                group.update(new)
                stack.extend(new)
            unseen-=group
            if root in group or len(group)<2:
                continue
            w=max(sorted(group),key=vx.get)
            key=w,tuple(sorted(group))
            cap=sum(z for (a,b),z in ey.items() if (a in group)!=(b in group))
            cap+=sum(vars_[e[v]].solution_value() for v in group if v in e)
            if cap+1e-6<2*vx[w] and key not in seen:
                result.append(key)
                seen.add(key)
    return result


def solve(parent,prefix,orientation_count,column_limit,seconds):
    sys.path.insert(0,str(HERE.parents[1]/"work/solver_packages"))
    from ortools.linear_solver import pywraplp
    g=graph(parent,prefix)
    V,N,x,e,y=g
    solver=pywraplp.Solver.CreateSolver("GLOP")
    solver.SetNumThreads(1)
    solver.SetTimeLimit(round(seconds*1000))
    infinity=solver.infinity()
    z=[solver.NumVar(0,1,"") for i in range(len(x)+len(e)+len(y))]
    h=solver.NumVar(0,1,"")
    # Setting h=0 and all variables zero ensures feasibility. Every genuine
    # candidate uses h=1; the integer certificate is verified at h=1.
    for variable in z:
        c=solver.Constraint(-infinity,0)
        c.SetCoefficient(variable,1)
        c.SetCoefficient(h,-1)
    def add_row(row):
        sense,terms,bound=row
        c=solver.Constraint(0 if sense=="eq" else -infinity,0)
        for j,w in terms:
            c.SetCoefficient(z[j],w)
        if bound:
            c.SetCoefficient(h,-bound)
        return c
    linear=list(linear_rows(g,prefix))
    base=[add_row(row) for row in linear]
    blocks=[]
    columns=0
    for axes in ORIENTATIONS[:orientation_count]:
        for low,face in faces(axes):
            if sum(v in x for v in face)<5:
                continue
            feature,masks=patterns(g,prefix,axes,low)
            if not masks:
                return dict(status="no_face_pattern",axes=axes,low=low,prefix=prefix)
            if columns+len(masks)>column_limit:
                continue
            columns+=len(masks)
            total=solver.Constraint(0,0)
            total.SetCoefficient(h,-1)
            marg=[solver.Constraint(0,0) for i in feature]
            for c,j in zip(marg,feature):
                c.SetCoefficient(z[j],1)
            prices={}
            for j in sorted({need for _,need in masks if need>=0}):
                c=solver.Constraint(-infinity,0)
                c.SetCoefficient(z[j],-1)
                prices[j]=c
            for word,need in masks:
                variable=solver.NumVar(0,1,"")
                total.SetCoefficient(variable,1)
                for i in bits(word):
                    marg[i].SetCoefficient(variable,-1)
                if need>=0:
                    prices[need].SetCoefficient(variable,1)
            blocks.append((axes,low,feature,masks,marg,prices))
        if columns>=column_limit:
            break
    obj=solver.Objective()
    for j in x.values():
        obj.SetCoefficient(z[j],1)
    obj.SetMaximization()
    cuts=[]
    seen=set()
    passed=0
    start=monotonic()
    for iteration in range(3):
        status=solver.Solve()
        if status!=pywraplp.Solver.OPTIMAL:
            return dict(status="unresolved_optimizer",code=int(status),columns=columns,prefix=prefix)
        passed+=1
        if iteration==2 or obj.Value()<96-0.001:
            break
        extra=violated_cuts(g,z,prefix[0],seen)
        if not extra:
            break
        cuts.extend(extra)
        more=list(linear_rows(g,prefix,cuts))[len(linear):]
        base.extend(add_row(row) for row in more)
        linear.extend(more)
    cert=dict(scale=D,base_weights=[],cuts=cuts,face_weights=[])
    for i,(row,c) in enumerate(zip(linear,base)):
        w=round(D*c.dual_value())
        if row[0]=="le":
            w=max(0,w)
        if w:
            cert["base_weights"].append([i,w])
    for axes,low,feature,masks,marg,prices in blocks:
        coeff=[round(D*c.dual_value()) for c in marg]
        price={i:max(0,round(D*c.dual_value())) for i,c in prices.items()}
        if not any(coeff) and not any(price.values()):
            continue
        maximum=max(sum(coeff[i] for i in bits(word))-price.get(need,0) for word,need in masks)
        cert["face_weights"].append(dict(axes=axes,low=low,coefficients=coeff,
            terminal_prices=[[i,w] for i,w in price.items() if w],maximum=maximum))
    value=upper(g,prefix,cert)
    return dict(status="excluded" if value<96*D else "open",prefix=prefix,
                upper_numerator=value,scale=D,native=float(obj.Value()),columns=columns,
                face_blocks=len(blocks),cut_rounds=passed,seconds=monotonic()-start,
                solver_version=solver.SolverVersion(),certificate=cert)


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--depth",type=int,default=1,help="Maximum prefix length in edges")
    cli.add_argument("--jobs",type=int,default=16)
    cli.add_argument("--columns",type=int,default=9500)
    cli.add_argument("--orientations",type=int,default=3,choices=range(1,7))
    cli.add_argument("--seconds",type=float,default=4,help="Time limit per optimizer call")
    cli.add_argument("--output",default="capacity.json")
    args=cli.parse_args()
    if min(args.depth,args.jobs,args.columns,args.seconds)<=0:
        cli.error("Positive limits required")
    summary=PREV/"partner-children-summary.json"
    arms=parent_arms()
    cases=[(r["class_id"],r["endpoint"],[0,step]) for r in json.loads(summary.read_bytes())["endpoint_cases"]
           for step in r.get("unknown",[])]
    dest=HERE/args.output
    pins=dict(script=sha256(Path(__file__).read_bytes()).hexdigest(),summary=sha256(summary.read_bytes()).hexdigest(),
              geometry=sha256((PREV/"partner.py").read_bytes()).hexdigest(),
              bank=sha256((PREV.parent/"246-eight-dimensional-parents"/"comparison.json").read_bytes()).hexdigest())
    settings=dict(depth=args.depth,columns=args.columns,orientations=args.orientations,seconds=args.seconds)
    data=dict(pins=pins,settings=settings,open_roots=cases,queue=list(cases),records=[])
    if dest.exists():
        data=json.loads(dest.read_bytes())
        if data["pins"]!=pins or data["settings"]!=settings:
            raise ValueError("Checkpoint differs; use a separate output filename")
    for _ in range(args.jobs):
        if not data["queue"]:
            break
        i,end,prefix=data["queue"].pop(0)
        parent=rooted_parent(arms[i],end)
        report=solve(parent,prefix,args.orientations,args.columns,args.seconds)
        if report["status"] in ("open","unresolved_optimizer") and len(prefix)-1<args.depth:
            children=next_vertices(parent,prefix)
            report["children"]=children
            data["queue"].extend([i,end,prefix+[v]] for v in children)
        data["records"].append(dict(class_id=i,endpoint=end,**report))
        tmp=dest.with_suffix(".tmp")
        tmp.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
        tmp.replace(dest)
        print("class",i,"end",end,"prefix",prefix,report["status"],report.get("upper_numerator"),flush=True)


if __name__=="__main__":
    main()
