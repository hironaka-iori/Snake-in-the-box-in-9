"""Solve a same-color pair-preserving completion using one selector per movable pair."""
import itertools
from pysat.solvers import Minicard
from search_q9_wynn_plateau import NB
from verify_q9_center_avoidance import verify


def search(side, pairs, t, seed, target, cap, forbidden=None):
    side=set(side)
    assert len(side)*2==target and all(a in side and b==a^t and b not in side for a,b in pairs)
    fixed=side-{a for a,b in pairs}
    assert fixed
    orientations={}
    for i,(a,b) in enumerate(pairs,1):
        orientations[a]=i
        orientations[b]=-i
    other=[w for w in range(512) if (w^next(iter(side))).bit_count()%2]
    members={}
    ends={}
    requirements={}
    for w in other:
        signed={orientations[v] for v in NB[w] if v in orientations}
        # Complementary literals always contribute exactly one to the degree.
        forced=sum(v in fixed for v in NB[w])+sum(x>0 and -x in signed for x in signed)
        rest=[x for x in signed if -x not in signed]
        if forced<=2 and forced+len(rest)>=1:
            members[w]=128+w
            ends[w]=640+w
            requirements[w]=(forced,rest)
    if len(members)<len(side)+1:return "UNSAT",None
    with Minicard() as sat:
        def guarded_equal(guard,lits,k):
            if not 0<=k<=len(lits):
                sat.add_clause(guard)
                return
            for sub in itertools.combinations(lits,k+1):
                sat.add_clause(guard+[-x for x in sub])
            for sub in itertools.combinations(lits,len(lits)-k+1):
                sat.add_clause(guard+list(sub))
        def exactly(lits,n):
            sat.add_atmost(lits,n)
            sat.add_atmost([-x for x in lits],len(lits)-n)
        exactly(list(ends.values()),2)
        exactly(list(members.values()),len(side)+1)
        for w,m in members.items():
            e=ends[w];f,ls=requirements[w]
            sat.add_clause([-e,m])
            guarded_equal([-m],ls+[e],2-f)
            y=w^t
            if y>w and y in members:
                d=sum(v in side for v in NB[w])+sum(v in side for v in NB[y])
                guarded_equal([-m,-members[y]],[e,ends[y]],4-d)
        for v in fixed|orientations.keys():
            guarded_equal([] if v in fixed else [-orientations[v]],
                          [members[w] for w in NB[v] if w in members],2)
        sat.set_phases([i for i in range(1,len(pairs)+1)]+
                       [m if w in seed else -m for w,m in members.items()])
        choices=orientations|members
        root=min(fixed)
        while True:
            remaining=cap-sat.accum_stats()["conflicts"]
            if remaining<=0:return "UNKNOWN",None
            sat.conf_budget(remaining)
            outcome=sat.solve_limited()
            if outcome is not True:return ("UNKNOWN" if outcome is None else "UNSAT"),None
            model=set(sat.get_model())
            picked=fixed|{v for v,x in choices.items() if x in model}
            unseen=set(picked);parts=[]
            while unseen:
                q=[unseen.pop()]
                for v in q:
                    for w in NB[v]:
                        if w in unseen:unseen.remove(w);q.append(w)
                parts.append(set(q))
            if len(parts)==1:
                p=[next(v for v in picked if len(picked.intersection(NB[v]))==1)]
                remaining_nodes=picked-{p[0]}
                while remaining_nodes:
                    w,=remaining_nodes.intersection(NB[p[-1]])
                    p.append(w);remaining_nodes.remove(w)
                verify(p);assert len(p)==target+1
                rejected=False
                if forbidden is not None:
                    for fragment in forbidden(p):
                        sat.add_clause([-choices[v] for v in fragment if v in choices])
                        rejected=True
                if rejected:continue
                return "FOUND",p
            for part in parts:
                if root in part:continue
                clause={choices[w] for v in part for w in NB[v] if w in choices and w not in part}
                if part.isdisjoint(fixed):clause.add(-choices[min(part)])
                sat.add_clause(list(clause))
