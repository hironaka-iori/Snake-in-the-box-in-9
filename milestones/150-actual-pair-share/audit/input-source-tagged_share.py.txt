"""Production static-cap share CNF, with meanings for the contributor's Lean checker."""
import argparse,gzip,hashlib,itertools,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'work/share_packages'),str(ROOT/'work/solver_packages'),str(ROOT/'milestones/10-window-aggregate/scripts')]
from gen_lean_sat import TaggedEncoding
from pysat.solvers import Cadical153
from wincert import window_from_dirs,cycles_of

class TaggedShare:
    def __init__(self,dirs,bounds,cap,M=12):
        self.window=window_from_dirs(dirs);self.bounds=bounds;self.cap=cap;self.M=M
        base=TaggedEncoding(self.window,bounds,radius=4)
        self.nv=base.nv;self.meaning=base.meaning;self.smeaning={};self.ctrs=base.ctrs
        self.clauses=base.clauses;self.tags=[('old',t) for t in base.tags];self.var=base.var;self.ball=base.ball
        self.tots=[];spec=[];ulits=[]
        for ci,c in enumerate(self.window[1:-1],1):
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

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--row',type=int,default=0);ap.add_argument('--seconds',type=float,default=60);a=ap.parse_args()
    rec=json.loads((HERE/'data/cache-obstruction.json').read_text())['records'][a.row];dirs,bounds=rec['five_window_key'];cap=107
    t=time.monotonic();enc=TaggedShare(dirs,bounds,cap);prefix=HERE/'certificates'/f'obstruction{a.row}'
    print('encoded',enc.nv,len(enc.clauses),'seconds',round(time.monotonic()-t,2),flush=True)
    status='UNKNOWN';selected=None;cuts=0
    with Cadical153(bootstrap_with=enc.clauses,with_proof=True) as s:
        deadline=time.monotonic()+a.seconds
        while time.monotonic()<deadline:
            s.conf_budget(20000);ok=s.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            m=s.get_model();selected=[v for v in enc.ball if m[enc.var[v]-1]>0];cycles=cycles_of(selected)
            if not cycles:status='SAT';break
            for cyc in cycles:
                cl=[-enc.var[v] for v in cyc];enc.add(cl,('old',('cut',)));s.add_clause(cl);cuts+=1
        if status=='UNSAT':
            proof=s.get_proof();prefix.with_suffix('.drat').write_text('\n'.join(proof)+'\n')
    with prefix.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {enc.nv} {len(enc.clauses)}\n')
        for cl in enc.clauses:f.write(' '.join(map(str,cl))+' 0\n')
    # Initial production target requires no late clauses; later clauses would require
    # ordering them before the proof replay and a fresh solve of the final CNF.
    if status=='UNSAT' and cuts:raise RuntimeError('Regenerate proof from the final clause set before certification')
    metadata=dict(dirs=dirs,bounds=bounds,cap=cap,M=12,window=enc.window,variables=enc.nv,clauses=len(enc.clauses),status=status,seconds=round(time.monotonic()-t,3),added_cycles=cuts,selected=selected,
        script_sha256_lf=hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest())
    prefix.with_suffix('.json').write_text(json.dumps(metadata,indent=2)+'\n')
    with gzip.open(prefix.with_suffix('.meanings.json.gz'),'wt') as f:json.dump(dict(meaning=enc.meaning,smeaning=enc.smeaning,ctrs=enc.ctrs,tots=enc.tots,tags=enc.tags),f)
    print(json.dumps(metadata),flush=True)
if __name__=='__main__':main()
