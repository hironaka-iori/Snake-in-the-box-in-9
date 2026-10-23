"""Production static-cap share CNF, with meanings for the contributor's Lean checker."""
import argparse,gzip,hashlib,itertools,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'work/share_packages'),str(ROOT/'work/solver_packages'),str(ROOT/'milestones/10-window-aggregate/scripts')]
from gen_lean_sat import TaggedEncoding
from pysat.solvers import Cadical153
from wincert import window_from_dirs,cycles_of

class TaggedPairShare:
    def __init__(self,dirs,bounds,cap,M=12):
        self.window=window_from_dirs(dirs);self.bounds=bounds;self.cap=cap;self.M=M
        base=TaggedEncoding(self.window,bounds,radius=4)
        joint=[]
        for j in (1,6):
            axes=[a for a in range(9) if a not in (dirs[j-1],dirs[j])]
            joint.extend(-base.var[self.window[j]^(1<<a)^(1<<b)] for a,b in itertools.combinations(axes,2))
        base.atmost(joint,9,('ends',))
        self.nv=base.nv;self.meaning=base.meaning;self.smeaning={};self.ctrs=base.ctrs
        self.clauses=base.clauses;self.tags=[('old',t) for t in base.tags];self.var=base.var;self.ball=base.ball
        self.tots=[];spec=[];ulits=[]
        for ci,c in enumerate(self.window[1:-1],1):
            if ci not in (1,6):continue
            used={(c^self.window[ci-1]).bit_length()-1,(c^self.window[ci+1]).bit_length()-1};cs=[]
            for kk in range(9):
                if kk in used:continue
                q=c^(1<<kk);es=[]
                for a,b in itertools.combinations(range(9),2):
                    if kk in (a,b):continue
                    e=self.fresh(('sq',q,a,b));es.append(e)
                    self.add([self.var[v] for v in (q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b))]+[e],('emptyE',))
                et,ge=self.totalizer(es,('emp',q),up=True)
                dt,gd=self.totalizer([self.var[q^(1<<a)] for a in range(9)],('nb',q),up=False,down=True)
                tmax=min(cap+1,M*len(es));cs.append((kk,tmax))
                for t in range(1,tmax+1):
                    u=self.fresh(('u',q,t));ulits.append(u)
                    for d in range(1,10):
                        need=(t*d+M-1)//M
                        if need>len(es):continue
                        clause=[u,-ge[need]]
                        if d<9:clause.append(gd[d+1])
                        self.add(clause,('shareCl',et,dt))
            spec.append(cs)
        ti,out=self.totalizer(ulits,('cap',spec),up=True,limit=cap+1)
        self.add([-out[cap+1]],('shareCap',ti))

    def fresh(self,meaning):
        self.nv+=1;self.smeaning[self.nv]=meaning;return self.nv
    def add(self,clause,tag):self.clauses.append(clause);self.tags.append(tag)
    def totalizer(self,lits,kind,up,down=False,limit=None):
        ti=len(self.tots);self.tots.append((lits,kind));limit=len(lits) if limit is None else limit
        def rec(lo,hi):
            if hi-lo==1:return [None,lits[lo]]
            mid=(lo+hi)//2;a=rec(lo,mid);b=rec(mid,hi);na=len(a)-1;nb=len(b)-1
            out=[None]+[self.fresh(('t',ti,lo,hi,c)) for c in range(1,min(hi-lo,limit)+1)]
            for i in range(na+1):
                for j in range(nb+1):
                    if up and 0<i+j<len(out):self.add([out[i+j]]+([-a[i]] if i else [])+([-b[j]] if j else []),('totUp',ti))
                    if down and i+j+1<len(out):self.add([-out[i+j+1]]+([a[i+1]] if i<na else [])+([b[j+1]] if j<nb else []),('totDown',ti))
            return out
        return ti,rec(0,len(lits))
