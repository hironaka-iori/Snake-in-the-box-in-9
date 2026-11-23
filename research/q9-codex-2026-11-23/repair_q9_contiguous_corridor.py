"""Find a chordless variable-length bridge while fixing every outside vertex in order."""
import argparse
from collections import deque
from itertools import combinations
import json
from pathlib import Path
from pysat.solvers import Cadical195
from pysat.card import CardEnc,EncType
from pysat.formula import CNF
from search_q9_wynn_plateau import NB,verify
from verify_q9_six_cube_coverage import pairwise


def search(p,start,k,conflicts,strengthen=False,gain=0):
    if not start:
        p=p[::-1];start=len(p)-k
    left=p[:start];right=p[start+k:];a=left[-1];b=right[0] if right else None
    fixed=set(left+right)
    anchors={a} if b is None else {a,b}
    positions={v:i for i,v in enumerate(p) if v in fixed}
    if any(u in positions and abs(positions[u]-i)>1 for v,i in positions.items() for u in NB[v]):return 'UNSAT',None
    if right and (a^b).bit_count()==1:return 'UNSAT',None
    excluded=fixed-anchors
    domain={x for x in range(512) if x not in fixed and not excluded.intersection(NB[x])}
    verts=domain|anchors
    reached={a};queue=deque([a])
    while queue:
        x=queue.popleft()
        for y in NB[x]:
            if y in verts and y not in reached:reached.add(y);queue.append(y)
    need=k+len(anchors)+gain
    if not anchors<=reached or len(reached)<need:return 'UNSAT',None
    verts=reached
    forced=set(anchors);large=[]
    if strengthen and b is not None:
        from q9_corridor_blocks import simplify
        verts,forced,large,upper=simplify(verts,a,b)
        if upper<need-1:return 'UNSAT',None
    form=CNF();top=1024
    for v in forced:form.append([v+1])
    def add_card(lits,kind,bound):
        nonlocal top
        if not 0<=bound<=len(lits):form.append([]);return
        if kind=='atleast' and bound==0:return
        cnf=getattr(CardEnc,kind)(lits,bound=bound,top_id=top,encoding=EncType.totalizer)
        form.extend(cnf.clauses);top=max(top,cnf.nv)
    for side in [0,1]:
        need_c=need//2+(need%2 and a.bit_count()%2==side)
        add_card([v+1 for v in verts if v.bit_count()%2==side],'atleast',need_c)
    if strengthen==2:
        from q9_corridor_face_bounds import strongest
        face_upper,inequalities=strongest(verts)
        if face_upper<need:return 'UNSAT',None
        for lits,ub in inequalities:add_card(lits,'atmost',ub)
    if strengthen:
        # Every occupied vertex of an induced square cannot be selected.
        for v in sorted(verts):
            adj=[u for u in NB[v] if u in verts and u>v]
            for x,y in combinations(adj,2):
                z=x^y^v
                if z>v and z in verts:form.append([-v-1,-x-1,-y-1,-z-1])
        for block,u,v in large:
            for end in (u,v):
                lits=[x+1 for x in NB[end] if x in block]
                form.append(lits)
                for x,y in combinations(lits,2):form.append([-x,-y])
            # Sum(selected even)-sum(selected odd) depends only on the endpoints.
            delta=0 if (u^v).bit_count()%2 else 1-2*(u.bit_count()%2)
            evens=[x+1 for x in block if x.bit_count()%2==0]
            odds=[x+1 for x in block if x.bit_count()%2==1]
            add_card(evens+[-x for x in odds],'equals',len(odds)+delta)
    eps=[]
    for v in verts:
        ext=v in anchors
        lits=[u+1 for u in NB[v] if u in verts]
        deg=1 if ext else 2
        guard=[] if ext else [-v-1]
        if b is None and not ext:
            eid=513+v;eps.append(eid);form.append([-eid,v+1]);lits.append(eid)
        for c in combinations(lits,deg+1):form.append(guard+[-x for x in c])
        if len(lits)<deg:form.append(guard)
        else:
            for c in combinations(lits,len(lits)-deg+1):form.append(guard+list(c))
    if b is None:add_card(eps,'equals',1)
    with Cadical195(bootstrap_with=form) as sat:
        original=set(p)
        sat.set_phases([v+1 if v in original else -v-1 for v in verts])
        while True:
            budget=conflicts-sat.accum_stats()['conflicts']
            if budget<=0:return 'UNKNOWN',None
            sat.conf_budget(budget)
            r=sat.solve_limited()
            if not r:return ('UNSAT' if r is False else 'UNKNOWN'),None
            model=set(sat.get_model());chosen={v for v in verts if v+1 in model}
            todo=set(chosen);parts=[]
            while todo:
                q=[todo.pop()]
                for v in q:
                    for u in NB[v]:
                        if u in todo:todo.remove(u);q.append(u)
                parts.append(set(q))
            if len(parts)==1:
                walk=[a];rest=chosen-{a}
                while rest:
                    v,=rest.intersection(NB[walk[-1]]);walk.append(v);rest.remove(v)
                if b is not None:assert walk[-1]==b
                w=left[:-1]+walk+right[1:]
                pairwise(w,len(w)-1);assert len(w)>=len(p)+gain
                return 'FOUND',w
            for c in parts:
                if a in c:continue
                border={y+1 for x in c for y in NB[x] if y in verts-c}
                if not c.intersection(anchors):border.add(-next(iter(c))-1)
                sat.add_clause(list(border))


def norm(p,s,k):
    def encode(p,s):
        labels={};q=bytearray([s,len(p)-s-k])
        for i in range(1,len(p)):
            if s<=i<=s+k:continue
            d=(p[i]^p[i-1]).bit_length()-1;q.append(labels.setdefault(d,len(labels)))
        disp=(p[s-1]^p[s+k]) if s>0 and s+k<len(p) else 0
        mask=sum(1<<d for axis,d in labels.items() if disp>>axis&1)
        q+=mask.to_bytes(2,'little')+bytes([disp.bit_count()-mask.bit_count()])
        return bytes(q)
    return min(encode(p,s),encode(p[::-1],len(p)-s-k))


if __name__=='__main__':
    args=argparse.ArgumentParser(description=__doc__);args.add_argument('bank',type=Path);args.add_argument('cases',type=Path)
    args.add_argument('k',type=int);args.add_argument('budget',type=int);args.add_argument('--max',type=int,default=0);ns=args.parse_args()
    rows=[list(map(int,s.split())) for s in ns.bank.read_text().splitlines()]
    def jobs():
        if str(ns.cases)=='all':
            from verify_q9_onechord_bank import check
            for row,p in enumerate(rows):
                i,j=check(p);starts=set()
                for t in (i,j):starts.update(range(max(0,t-ns.k+1),min(t,len(p)-ns.k)+1))
                for start in sorted(starts):yield row,start
        else:
            for line in ns.cases.read_text().splitlines():
                f=line.split()
                if f and f[0]=='CAP':yield tuple(map(int,f[1:3]))
    seen=set()
    for row,start in jobs():
        p=rows[row];key=norm(p,start,ns.k)
        if key in seen:continue
        seen.add(key);st,w=search(p,start,ns.k,ns.budget)
        print(json.dumps(dict(row=row,start=start,k=ns.k,status=st,witness=w),separators=(',',':')),flush=True)
        if w or (ns.max and len(seen)>=ns.max):break
