"""Independent degree/cardinality relaxation for externally checked negative certificates."""
import sys,json,gzip,tempfile,subprocess,hashlib
from pathlib import Path
from itertools import combinations
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool,CNF
from pysat.solvers import Glucose4
from prepare import D,unpack
NB=[{v^(1<<d) for d in range(9)} for v in range(512)]
def clauses(fixed):
    deg=[len(z&fixed) for z in NB];assert max(deg[v] for v in fixed)<=2
    saturated={v for v in fixed if deg[v]==2}
    free={v for v in range(512) if v not in fixed and deg[v]<=2 and NB[v].isdisjoint(saturated)}
    f=[];pool=IDPool(start_from=1025)
    def at_least(lits,k):
        if k<=0:return
        if k>len(lits):f.append([]);return
        f.extend(CardEnc.atleast(lits,k,vpool=pool,encoding=EncType.seqcounter).clauses)
    at_least([v+1 for v in sorted(free)],193-len(fixed))
    for parity in (0,1):
        at_least([v+1 for v in sorted(free) if v.bit_count()%2==parity],96-sum(v.bit_count()%2==parity for v in fixed))
    ends=[]
    for v in sorted(free|fixed):
        guard=[] if v in fixed else [-(v+1)]
        t=v+513;ends.append(t)
        if guard:f.append([-t,v+1])
        z=[q+1 for q in sorted(NB[v]&free)]+[t];need=2-deg[v]
        if need>len(z):f.append(guard);continue
        for g in combinations(z,need+1):f.append(guard+[-a for a in g])
        for g in combinations(z,len(z)-need+1):f.append(guard+list(g))
    f.extend(CardEnc.equals(ends,2,vpool=pool,encoding=EncType.seqcounter).clauses)
    return f
def main():
    mode=sys.argv[2] if len(sys.argv)>2 else ''
    for label in ('single','double','singlewide','doublewide'):
        cases=[json.loads(l) for l in (D/f'{label}.jsonl').read_text().splitlines()]
        for i in range(min(25,len(cases))):
            k=unpack(int(cases[i]['fixed'],16));f=clauses(k);name=f'{label}-{i}.drat.gz';file=D/name
            if mode=='--replay':
                if not file.exists():continue
                data=gzip.decompress(file.read_bytes())
            else:
                with Glucose4(bootstrap_with=f,with_proof=True) as s:
                    s.conf_budget(3500)
                    if s.solve_limited() is not False:continue
                    data=('\n'.join(s.get_proof())+'\n').encode()
                file.write_bytes(gzip.compress(data))
            with tempfile.TemporaryDirectory() as td:
                a=Path(td)/'a.cnf';b=Path(td)/'b.drat';CNF(from_clauses=f).to_file(str(a));b.write_bytes(data)
                proc=subprocess.run([sys.argv[1],str(a),str(b)],capture_output=True)
                assert b's VERIFIED' in proc.stdout
                print(json.dumps([label,i,len(k),name,hashlib.sha256(a.read_bytes()).hexdigest(),'VERIFIED']),flush=True)
            break
        else:raise RuntimeError(label)
if __name__=='__main__':main()
