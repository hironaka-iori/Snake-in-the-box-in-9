"""Rebuild both lower arms with arbitrary lengths while retaining only an upper-face middle."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import subprocess, sys
from archive import HERE, MS, charts, input_paths, code, read, write
from grow import independent_check
sys.path.insert(0,str(next(MS.glob("266-*"))))
import rebuild
geometry=rebuild.geometry

def physical_graph(sites):
    return {v:[v^(1<<j) for j in range(9) if v^(1<<j) in sites] for v in sites}

def inputs():
    output={}
    for name,path in input_paths():
        for axis,org,a,m,b in charts(path):
            k=code(m).hex()
            if k not in output: output[k]=dict(m=m,source=name,axis=axis,origin=org,occurrences=0,records=0)
            output[k]["occurrences"]+=1
            output[k]["records"]+=len(path)==192
    return output

def encode(m,target,majority,cycles,four=False):
    cnf=geometry.Formula()
    block=set(m[1:-1]); port={m[0],m[-1]}
    chosen={v:cnf.variable() for v in range(256) if v not in block}
    upper0=sum(v.bit_count()%2==1 for v in m)
    lower_n=target+1-len(m)
    lower0=(target+1)//2+int(target%2==0 and majority==0)-upper0
    for parity,count in [(0,lower0),(1,lower_n-lower0)]:
        cnf.exactly([x for v,x in chosen.items() if v.bit_count()%2==parity],count)
    ends={v:cnf.variable() for v in chosen if target%2 or v.bit_count()%2==majority}
    for parity in (0,1):
        cnf.exactly([x for v,x in ends.items() if v.bit_count()%2==parity],1 if target%2 else 2*int(parity==majority))
    for v,x in chosen.items():
        r=int(v in port)
        if r: cnf.clauses.append([x])
        near=[chosen[w] for w in geometry.NEIGHBOURS[v] if w in chosen]
        if v in ends:
            tip=ends[v];cnf.clauses.append([-tip,x])
            geometry.bounds(cnf,near,1-r,2-r,[-x])
            geometry.bounds(cnf,near,0,1-r,[-tip])
            geometry.bounds(cnf,near,2-r,len(near),[-x,tip])
        else: geometry.bounds(cnf,near,2-r,2-r,[-x])
    geometry.face_bounds(cnf,chosen)
    if four:
        from local_faces import add
        add(cnf,chosen,m)
    for cycle in cycles:
        graph=physical_graph(set(cycle))
        assert all(len(ns)==2 for ns in graph.values()) and len(cycle)==len(set(cycle))
        seen=set(); queue=[cycle[0]]
        for v in queue:
            if v in seen:continue
            seen.add(v);queue.extend(graph[v])
        assert seen==set(cycle) and all(v<256 or v-256 in m for v in cycle)
        cnf.clauses.append([-chosen[v] for v in sorted(cycle) if v<256])
    return cnf,chosen

def build_answer(m,sites):
    graph=physical_graph(set(sites)|{256+v for v in m})
    tips=sorted(v for v,ns in graph.items() if len(ns)==1)
    assert len(tips)==2 and all(len(ns) in (1,2) for ns in graph.values())
    route=[tips[0]]; used={route[0]}
    for v in route:
        links=set(graph[v])-used
        if links:
            w,=links
            route.append(w);used.add(w)
    assert route[-1]==tips[1]
    left=graph.keys()-used
    cycles=[]
    while left:
        cycle=[next(iter(left))];left.remove(cycle[0])
        for v in cycle:
            add=sorted(left.intersection(graph[v]));left.difference_update(add);cycle.extend(add)
        cycles.append(sorted(cycle))
    return route,cycles

def main(opt):
    middles=inputs()
    records=read("whole-middle.json") if (HERE/"whole-middle.json").exists() else {}
    with TemporaryDirectory(prefix="q9-whole-middle-") as scratch:
        temp=Path(scratch);tools=rebuild.masks.compilers(temp)
        for k,mr in sorted(middles.items(),key=lambda kv:(-kv[1]["records"],-kv[1]["occurrences"],kv[0]))[:opt.top]:
            m=mr["m"]
            job=records.setdefault(k,dict(**mr,targets={}))
            for maj in ([0,1] if opt.target%2==0 else [0]):
                tag="%d-%d"%(opt.target,maj)
                old=job["targets"].get(tag,{}); cycles=old.get("cycles",[])
                if old.get("status") in ("excluded","witness"):continue
                stop=monotonic()+opt.seconds
                while True:
                    cnf,chosen=encode(m,opt.target,maj,cycles,opt.four)
                    formula=temp/"two.cnf";trace=temp/"two.lrat"
                    trace.unlink(missing_ok=True);h=cnf.save(formula)
                    row=dict(target=opt.target,majority_if_even=maj,cycles=cycles,cnf=h,clauses=len(cnf.clauses))
                    if opt.four:row["four_cube_caps"]=True
                    try:
                        run=subprocess.run([str(geometry.SOLVER),"-q","--seed=1","--lrat","--no-binary",str(formula),str(trace)],capture_output=True,timeout=max(.01,stop-monotonic()))
                    except subprocess.TimeoutExpired:
                        row["status"]="open";break
                    if run.returncode==20:
                        assert b"s UNSATISFIABLE" in run.stdout
                        proof=HERE/"whole-proofs"/(h+".lrat.gz");proof.parent.mkdir(exist_ok=True)
                        row.update(status="excluded",proof=proof.relative_to(HERE).as_posix(),
                            raw=rebuild.masks.p.joins.archive(trace,proof),compressed=rebuild.masks.digest(proof),
                            replay=rebuild.masks.p.check_proof(formula,proof,tools[0]))
                        break
                    assert run.returncode==10 and b"s SATISFIABLE" in run.stdout
                    true={int(x) for l in run.stdout.splitlines() if l.startswith(b"v ") for x in l.split()[1:]}
                    sites={v for v,x in chosen.items() if x in true}
                    assert len(sites)+len(m)==opt.target+1
                    path,more=build_answer(m,sites)
                    if more:
                        cycles=cycles+more;continue
                    independent_check(path)
                    assert any(path[i:i+len(m)]==[256+v for v in s] for s in (m,m[::-1]) for i in range(len(path)-len(m)+1))
                    row.update(status="witness",path=path)
                    if opt.target>=192:write("candidate-192.json",row)
                    break
                job["targets"][tag]=row;write("whole-middle.json",records)
                print(mr["source"],len(m)-1,opt.target,maj,row["status"],len(cycles),flush=True)
                if row["status"]=="witness" and opt.target>=192:return

if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("--top",type=int,default=3);ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--target",type=int,default=192);ap.add_argument("--four",action="store_true");main(ap.parse_args())

