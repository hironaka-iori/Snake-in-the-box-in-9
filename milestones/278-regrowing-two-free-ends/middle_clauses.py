"""Independent expansion of the fixed-middle necessary conditions and literal donor assignments."""
from collections import Counter
from hashlib import sha256
from itertools import combinations


class Ledger:
    def __init__(self, evaluate):
        self.values = [False]
        self.rows = []
        self.evaluate = evaluate

    def variable(self, value):
        self.values.append(bool(value))
        return len(self.values)-1

    def truth(self, lit):
        return self.values[abs(lit)] == (lit > 0)

    def clause(self, lits):
        if self.evaluate and not any(self.truth(x) for x in lits):
            raise ValueError(f"Archived assignment falsifies clause {len(self.rows)+1}: {lits}")
        self.rows.append(" ".join(map(str,lits))+" 0\n")

    def digest(self):
        h = sha256(f"p cnf {len(self.values)-1} {len(self.rows)}\n".encode())
        for line in self.rows:
            h.update(line.encode())
        return {"variables":len(self.values)-1, "clauses":len(self.rows), "cnf":h.hexdigest()}

    def cardinal(self, xs, n):
        self.at_most(xs,n)
        self.at_most([-v for v in xs],len(xs)-n)

    def at_most(self,leaves,cap):
        if cap < 0:
            self.clause([])
            return
        if cap >= len(leaves):
            return
        def tree(items):
            if len(items)==1:
                return items
            half = len(items)//2
            lhs=tree(items[:half])
            rhs=tree(items[half:])
            total=sum(self.truth(x) for x in items)
            out=[self.variable(total>=j) for j in range(1,min(cap+1,len(items))+1)]
            for a in range(1+len(lhs)):
                for b in range(1+len(rhs)):
                    if 1<=a+b<=len(out):
                        needed=([-lhs[a-1]] if a else [])+([-rhs[b-1]] if b else [])
                        self.clause(needed+[out[a+b-1]])
            return out
        self.clause([-tree(leaves)[cap]])

    def degree(self, guard, xs, minimum, maximum):
        if minimum>len(xs) or maximum<0:
            self.clause(guard)
            return
        if maximum < len(xs):
            for c in combinations(xs,maximum+1):
                self.clause(guard+[-v for v in c])
        if minimum>0:
            for c in combinations(xs,len(xs)-minimum+1):
                self.clause(guard+list(c))


def reconstruct(m, edges, maj, cuts, path=None, four=False):
    """CNF and, if path is given, one satisfying value for every physical and threshold variable."""
    q=Ledger(path is not None)
    physical=set(path or [])
    tips=set() if path is None else {path[0],path[-1]}
    allowed=sorted(set(range(256))-set(m[1:-1]))
    selected={u:q.variable(u in physical) for u in allowed}
    parity=lambda u:u.bit_count()&1
    start=maj if edges%2==0 else 0
    total_counts=Counter((start+i)%2 for i in range(edges+1))
    high_counts=Counter(parity(256+u) for u in m)
    for side in range(2):
        q.cardinal([x for u,x in selected.items() if parity(u)==side],total_counts[side]-high_counts[side])
    endpoint_counts=Counter([start,(start+edges)%2])
    endpoint={u:q.variable(u in tips) for u in allowed if endpoint_counts[parity(u)]>0}
    for side in range(2):
        q.cardinal([x for u,x in endpoint.items() if parity(u)==side],endpoint_counts[side])
    for u,var in selected.items():
        fixed_edge=int(u==m[0] or u==m[-1])
        if fixed_edge:q.clause([var])
        neighbours=[selected[z] for d in range(8) if (z:=u^(1<<d)) in selected]
        if u in endpoint:
            end=endpoint[u]
            q.clause([-end,var])
            q.degree([-var],neighbours,1-fixed_edge,2-fixed_edge)
            q.degree([-end],neighbours,0,1-fixed_edge)
            q.degree([-var,end],neighbours,2-fixed_edge,len(neighbours))
        else:
            q.degree([-var],neighbours,2-fixed_edge,2-fixed_edge)
    for dim,cap in ((2,3),(3,5)):
        for axes in combinations(range(8),dim):
            mask=sum(1<<d for d in axes)
            subs=sorted(sum(1<<axes[i] for i in range(dim) if bits>>i&1) for bits in range(1<<dim))
            for v in range(256):
                if v&mask:continue
                available=[selected[v^z] for z in subs if v^z in selected]
                for c in combinations(available,cap+1):
                    q.clause([-x for x in c])
    if four:
        from middle_four import apply
        apply(q,selected,m)
    upper={256+u for u in m}
    for raw in cuts:
        sites=set(raw)
        assert len(sites)==len(raw) and len(sites)>=4 and sites<=set(allowed)|upper
        ring={v:[w for w in sites if (v^w).bit_count()==1] for v in sites}
        assert all(len(adj)==2 for adj in ring.values())
        seen={raw[0]}
        pending=[raw[0]]
        while pending:
            v=pending.pop()
            for w in ring[v]:
                if w not in seen:
                    seen.add(w)
                    pending.append(w)
        assert seen==sites
        q.clause([-selected[v] for v in sorted(sites-upper)])
    return q.digest()
