import gzip,hashlib,itertools,json,subprocess,sys,tempfile
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import CNF,IDPool
from pysat.solvers import Solver,Glucose4
from verify import D,permitted
def build(A):
    H=permitted(A);adj={v:set(neigh)|{512} for v,neigh in H.items()};adj[512]=A
    pool=IDPool();edge={(v,w):pool.id() for v in sorted(adj) for w in sorted(adj[v]) if v<w}
    blocks={}
    for v in sorted(adj):
        inc=[edge[min(v,w),max(v,w)] for w in sorted(adj[v])]
        blocks[v]=CardEnc.equals(inc,2,vpool=pool,encoding=EncType.seqcounter).clauses if len(inc)>=2 else [[]]
    return blocks,pool
def main():
    sets=[set(map(int,l.split()[1:])) for l in (D/'resolved.sets').read_text().splitlines()]
    bin=sys.argv[1];replay=len(sys.argv)>2
    output=[]
    for i,A in enumerate(sets):
        blocks,pool=build(A);guards={v:pool.id() for v in sorted(blocks)}
        clauses=[[-guards[v],*row] for v,b in blocks.items() for row in b]
        with Solver(name='cadical195',bootstrap_with=clauses) as s:
            assert not s.solve(assumptions=list(guards.values()));core=s.get_core()
            for a in list(core):
                test=[t for t in core if t!=a]
                if not s.solve(assumptions=test):core=test
            assert not s.solve(assumptions=core) and all(s.solve(assumptions=[k for k in core if k!=z]) for z in core)
        verts=sorted(v for v,a in guards.items() if a in core);output.append([i,verts])
    current=''.join(json.dumps(r,separators=(',',':'))+'\n' for r in output)
    if replay:assert (D/'degree_cores.jsonl').read_text()==current
    else:(D/'degree_cores.jsonl').write_text(current)
    i,vertices=min(output,key=lambda row:len(row[1]));bl,_=build(sets[i]);f=[l for v in vertices for l in bl[v]];fname=D/'degree_core.drat.gz'
    if not replay:
        with Glucose4(bootstrap_with=f,with_proof=True) as s:
            assert not s.solve();fname.write_bytes(gzip.compress(('\n'.join(s.get_proof())+'\n').encode()))
    with tempfile.TemporaryDirectory() as td:
        a=Path(td)/'a.cnf';b=Path(td)/'b.drat';CNF(from_clauses=f).to_file(str(a));b.write_bytes(gzip.decompress(fname.read_bytes()))
        r=subprocess.run([bin,str(a),str(b)],capture_output=True);assert b's VERIFIED' in r.stdout
        print(json.dumps(dict(sets=len(output),size_range=[min(len(r[1]) for r in output),max(len(r[1]) for r in output)],smallest_index=i,smallest_core=vertices,cnf_sha256=hashlib.sha256(a.read_bytes()).hexdigest(),drat='VERIFIED')))
if __name__=='__main__':main()
