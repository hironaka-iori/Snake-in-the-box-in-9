"""Generalisation of wkmin.py: ball radius R around x = 0 (path nbrs e0, e1),
objective = sum over centres c in CENTRES of w_k(c) (subcubes must lie in the ball).
usage: python3 wkmin2.py k R centres   (centres: '0' or '0,1,2' meaning vertices 0, e0=1, e1=2)
Also supports 'lam' : objective lam*w_2(0) + w_3(0) combination via argv[4]."""
import sys
from itertools import combinations
from pysat.formula import WCNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from fractions import Fraction as F
from wkmin import cycles
n=9; W=840
JMAX={2:3,3:5,4:8,5:16}
pc=lambda u: bin(u).count('1')
def cube_pts(base,dirs):
    pts=[base]
    for d in dirs: pts+=[p^(1<<d) for p in pts]
    return pts
def build(R, terms, cuts):
    ball=[u for u in range(1<<n) if pc(u)<=R]
    pool=IDPool(); s={u:pool.id(('s',u)) for u in ball}; wc=WCNF()
    wc.append([s[0]]); wc.append([s[1]]); wc.append([s[2]])
    for i in range(2,n): wc.append([-s[1<<i]])
    deg1=[]
    for u in ball:
        if u==0: continue
        lits=[s[u^(1<<i)] for i in range(n) if pc(u^(1<<i))<=R]
        for cl in CardEnc.atmost(lits,bound=2,vpool=pool,encoding=EncType.seqcounter).clauses: wc.append(cl+[-s[u]])
        if pc(u)<=R-1:
            wc.append([-s[u]]+lits)
            d=pool.id(('d1',u)); deg1.append(d); pl=[]
            for a,b in combinations(range(len(lits)),2):
                p=pool.id(('p',u,a,b)); pl.append(p); wc.append([-p,lits[a]]); wc.append([-p,lits[b]])
            wc.append([-s[u],d]+pl)
    for cl in CardEnc.atmost(deg1,bound=2,vpool=pool,encoding=EncType.seqcounter).clauses: wc.append(cl)
    for cyc in cuts: wc.append([-s[u] for u in cyc])
    import os
    amin=int(os.environ.get('AMIN','0'))
    if amin:
        sq=[]
        for i,j in combinations(range(n),2):
            q=pool.id(('sq',i,j)); sq.append(q)
            for u in (1<<i,1<<j,(1<<i)|(1<<j)): wc.append([-q,-s[u]])
        for cl in CardEnc.atleast(sq,bound=amin,vpool=pool,encoding=EncType.seqcounter).clauses: wc.append(cl)
    # terms: list of (weight multiplier m (int), centre c, k)
    for (mult,c,k) in terms:
        for dirs in combinations(range(n),k):
            pts=cube_pts(c,dirs)
            if any(pc(p)>R for p in pts): raise SystemExit('cube outside ball')
            others=[s[p] for p in pts if p!=c]
            for j in range(2,JMAX[k]+1):
                t=pool.id(('t',c,k,dirs,j))
                for cl in CardEnc.atleast(others,bound=j-1,vpool=pool,encoding=EncType.seqcounter).clauses: wc.append(cl+[-t])
                # centre c must be in S for the term; centres are forced selected
                wc.append([t],weight=mult*W//(j*(j-1)))
    return ball,s,wc
def value(sel,terms):
    sel=set(sel); tot=F(0)
    for (mult,c,k) in terms:
        for dirs in combinations(range(n),k):
            tot+=mult*F(1,sum(1 for p in cube_pts(c,dirs) if p in sel))
    return tot
def solve(R,terms):
    cuts=[]
    while True:
        ball,s,wc=build(R,terms,cuts)
        with RC2(wc,solver='g4',exhaust=True,minz=True) as rc: m=rc.compute()
        sel=[u for u in ball if m[s[u]-1]>0]
        cyc=cycles(sel)
        if not cyc: return value(sel,terms),sel,len(cuts)
        cuts.extend(cyc)
if __name__=='__main__':
    k=int(sys.argv[1]); R=int(sys.argv[2]); cs=[int(c) for c in sys.argv[3].split(',')]
    terms=[(1,c,k) for c in cs]
    if len(sys.argv)>4:  # lam for w_2 term at same centres
        lam=int(sys.argv[4]); terms+= [(lam,c,2) for c in cs]
    val,sel,nc=solve(R,terms)
    print('k',k,'R',R,'centres',cs,'extra w2 mult',sys.argv[4] if len(sys.argv)>4 else 0,'min total =',val,'=',float(val),'per centre',float(val/len(cs)),'cuts',nc,'|sel|',len(sel),flush=True)
