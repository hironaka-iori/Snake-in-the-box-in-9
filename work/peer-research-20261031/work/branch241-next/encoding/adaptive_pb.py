"""Dependency-free adaptive-share CNF gate prototype; not a formal proof.
Each square has 4 face bits and 7 disjoint translated outer faces of 4 bits.
For fixed x in outer face j, charge = 2/(h*q_j) if F empty and x selected.
The returned weighted events represent 1260 times that charge exactly.
"""
from functools import lru_cache
from fractions import Fraction
import itertools, json, random

class CNF:
    def __init__(self):
        self.nv=0; self.clauses=[]; self.gates=[]
        self.one=self.fresh(); self.clauses.append([self.one])
    def fresh(self):
        self.nv+=1; return self.nv
    def AND(self,*ls):
        if not ls:return self.one
        z=self.fresh()
        self.clauses.extend([[-z,l] for l in ls]); self.clauses.append([z]+[-l for l in ls])
        self.gates.append((z,'and',ls)); return z
    def OR(self,*ls):return -self.AND(*[-l for l in ls])
    def ITE(self,x,t,e):return self.OR(self.AND(x,t),self.AND(-x,e))
    def exact(self,ls):
        row=[self.one]
        for x in ls:
            row=[self.ITE(x,row[k-1] if k else -self.one,row[k] if k<len(row) else -self.one) for k in range(len(row)+1)]
        return row
    def leq(self,terms,cap):
        """Exact weighted PB via memoized decision diagram; potentially expensive.
        Returns a literal, caller adds [literal] to assert the threshold.
        """
        suffix=[0]*(len(terms)+1)
        for i in range(len(terms)-1,-1,-1):suffix[i]=suffix[i+1]+terms[i][1]
        @lru_cache(None)
        def go(i,b):
            if b<0:return -self.one
            if suffix[i]<=b:return self.one
            l,w=terms[i]
            assert w>=0
            return self.ITE(l,go(i+1,b-w),go(i+1,b))
        return go(0,cap)
    def witness(self,inputs):
        a={self.one:True,**inputs}
        def val(l):return a[abs(l)]==(l>0)
        for z,op,ls in self.gates:a[z]=all(map(val,ls))
        return a
    def satisfied(self,a):return all(any(a[abs(l)]==(l>0) for l in c) for c in self.clauses)

def square_events(C,face,outer,j,x):
    assert len(face)==4 and len(outer)==7 and all(len(r)==4 for r in outer)
    assert x in outer[j]
    empty=C.AND(*[-v for v in face])
    q=[C.exact(r) for r in outer]
    nonempty=[-r[0] for r in q]
    h=C.exact(nonempty)
    # Each outer translated square cannot be fully selected in an induced path.
    for r in outer:C.clauses.append([-v for v in r])
    terms=[]
    for a in range(1,8):
        for b in range(1,4):
            assert 2520%(a*b)==0
            event=C.AND(empty,x,h[a],q[j][b])
            terms.append((event,2520//(a*b)))
    return terms

def run_tests():
    # Independent truth-table oracle for AND/OR/ITE and weighted PB. Exhaust all inputs.
    tested=0
    for cap in range(-1,19):
        C=CNF(); xs=[C.fresh() for _ in range(4)]; weights=[2,3,5,7]
        z=C.leq(list(zip(xs,weights)),cap)
        for bits in itertools.product([False,True],repeat=4):
            a=C.witness(dict(zip(xs,bits))); assert C.satisfied(a)
            assert (a[abs(z)]==(z>0))==(sum(w*b for w,b in zip(weights,bits))<=cap)
            tested+=1
    C=CNF(); f=[C.fresh() for _ in range(4)]; out=[[C.fresh() for _ in range(4)] for _ in range(7)]
    terms=square_events(C,f,out,0,out[0][0]); rng=random.Random(234)
    cases=[]
    for h in range(1,8):
        for q in range(1,4):
            bits=[[int(k<q) if j==0 else int(j<h and k==0) for k in range(4)] for j in range(7)]
            cases.append(([0]*4,bits))
    for _ in range(500):
        rows=[]
        for j in range(7):
            row=[rng.randrange(2) for _ in range(4)]
            if all(row):row[rng.randrange(4)]=0
            rows.append(row)
        cases.append(([rng.randrange(2) for _ in range(4)],rows))
    for fb,ob in cases:
        inputs=dict(zip(f,fb))
        inputs.update((v,b) for row,bits in zip(out,ob) for v,b in zip(row,bits))
        a=C.witness(inputs); assert C.satisfied(a)
        h=sum(any(row) for row in ob); q=sum(ob[0])
        direct=Fraction(2520,h*q) if not any(fb) and ob[0][0] else 0
        got=sum(w for l,w in terms if a[abs(l)]==(l>0))
        assert got==direct,(fb,ob,got,direct)
    return dict(status='passed',pb_truth_table_cases=tested,share_cases=len(cases),share_variables=C.nv,share_clauses=len(C.clauses),scale=1260,objective_events=len(terms),formal_status='not Lean certified; no SAT/LRAT generated')

if __name__=='__main__':print(json.dumps(run_tests(),indent=2))
