"""Direction-aware minimum mean (exploratory; solver tables, not certificates).

States: the last seven transition directions (up to relabelling) and three counts.
Transitions must keep every 8-direction segment an induced path; each 3- and
4-center window must be admitted by the survey for its own shape.  Counts above
the surveyed range are unrestricted.  Reads the survey JSON files in ../data.
"""
import ast, itertools
from fractions import Fraction as Fr
def canon(ds):
    m={};r=[]
    for d in ds: m.setdefault(d,len(m)); r.append(m[d])
    return tuple(r)
import json, os
D=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','data')
def load(fn):
    return {(tuple(r['directions']),tuple(r['alpha'])): r['status']!='UNSAT'
            for r in json.load(open(os.path.join(D,fn)))['results']}
F3=load('survey_c3_r3.json'); F4=load('survey_c4_r3_k5.json')
K=5
def feas(F,ds,al,kmax,ncent):
    if any(a>kmax for a in al): return True
    c=canon(ds); r=canon(ds[::-1])
    for key in ((c,al),(r,al[::-1])):
        if key in F: return F[key]
    return None
def ok3(ds,al):
    v=feas(F3,ds,al,6,3); return True if v is None else v
def ok4(ds,al):
    if not(ok3(ds[:4],al[:3]) and ok3(ds[1:],al[1:])): return False
    v=feas(F4,ds,al,K,4); return True if v is None else v   # pruned-by-subwindow handled above
def valid(ds):
    vs=[0]
    for d in ds: vs.append(vs[-1]^1<<d)
    return len(set(vs))==len(vs) and all(bin(vs[i]^vs[j]).count('1')!=1 for i in range(len(vs)) for j in range(i+2,len(vs)))
L=7  # directions kept in state
vals=range(1,K+2)
# state: (canon dirs of length L, last 3 alphas)
dstates=set()
for ds in itertools.product(range(L),repeat=L):
    c=canon(ds)
    if valid(c): dstates.add(c)
dstates=sorted(dstates); print('dir states',len(dstates))
trans={}
for c in dstates:
    nxt=set()
    for d in range(max(c)+2):
        ds=c+(d,)
        if valid(ds): nxt.add((canon(ds[1:]),ds[-5:]))
    trans[c]=nxt
states={}
def sid(s):
    if s not in states: states[s]=len(states)
    return states[s]
edges=[]
for c in dstates:
    for a in itertools.product(vals,repeat=3):
        # alpha a corresponds to centers at the last 3 vertices whose windows use last directions
        if not ok3(c[-4:],a): continue
        u=sid((c,a))
        for (nc,last5) in trans[c]:
            for w in vals:
                q=a+(w,)
                if ok3(last5[-4:],q[1:]) and ok4(last5,q):
                    edges.append((u,sid((nc,q[1:])),w))
n=len(states); print('states',n,'edges',len(edges))
# min mean via binary search with Bellman-Ford negative cycle detection on weight w - lam
def has_cycle_below(lam):
    dist=[0.0]*n
    for it in range(n):
        ch=False
        for u,v,w in edges:
            nd=dist[u]+w-lam
            if nd<dist[v]-1e-12: dist[v]=nd; ch=True
        if not ch: return False
    return True
lo,hi=2.5,4.0
for _ in range(14):
    mid=(lo+hi)/2
    if has_cycle_below(mid): hi=mid
    else: lo=mid
print('min mean approx',lo,hi)
