"""Prove or disprove the existence of a 95-edge rooted path avoiding a set of sites."""
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import subprocess
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"260-donor-intersections"))
from census import load,save,digest,bank
sys.path.insert(0,str(MS/"254-distant-arm-partners"))
import fixed
from fixed import p

def compilers(tmp):
    checker,tmptrim=tmp/"verify.exe",tmp/"trim.exe"
    for src,exe in [(p.joins.CHECKER,checker),(fixed.R252/"TrimLrat.cs",tmptrim)]:
        subprocess.run([str(p.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(src)],
                       check=True,capture_output=True)
    return checker,tmptrim

def groups():
    catalog=load(MS/"260-donor-intersections/catalogue.json")
    by_root={}
    for k,arm in catalog["parents"].items():
        for end,root in enumerate((arm[0],arm[-1])):
            by_root.setdefault(root,{})[k+":"+str(end)]={v^root for v in arm if v!=root}
    return by_root

def formula(blocked,cycles=(),alternatives=None,prefix=(0,)):
    model,chosen=p.joins.partner.encode([0]+sorted(blocked),prefix,cycles)
    if alternatives is not None:
        # Select at least one possible full parent. Each of its additional blocked sites must be absent.
        selectors=[]
        for extra in alternatives:
            select=model.variable()
            selectors.append(select)
            for v in extra: model.clauses.append([-select,-chosen[v]])
        model.clauses.append(selectors)
    return model,chosen

def decode(chosen,truth,prefix):
    verts={v for v,x in chosen.items() if x in truth}
    assert len(verts)==96 and 0 in verts
    adj={v:set(p.joins.partner.NEIGHBOURS[v])&verts for v in verts}
    ends={v for v in verts if len(adj[v])==1}
    if len(ends)!=2 or 0 not in ends or any(len(adj[v])!=2 for v in verts-ends):
        raise ValueError("Incorrect selected degrees")
    path=[0]
    while True:
        nxt=adj[path[-1]]-set(path)
        if not nxt: break
        u,=nxt
        path.append(u)
    if path[:len(prefix)]!=list(prefix): raise ValueError("Rooted prefix")
    left=verts-set(path)
    cycles=[]
    while left:
        queue=[min(left)]
        left.remove(queue[0])
        for v in queue:
            fresh=adj[v]&left
            left-=fresh
            queue.extend(sorted(fresh))
        cycles.append(sorted(queue))
    return path,cycles

def query(folder,tmp,compiler,blocked,seconds,alternatives=None,prefix=(0,),previous=None,builder=formula):
    cycles=[] if previous is None else list(previous["cycles"])
    fixed.HERE=folder
    cnf,chosen=builder(blocked,cycles,alternatives,prefix)
    raw,formula_path=tmp/"proof.lrat",tmp/"partner.cnf"
    until=monotonic()+seconds
    while True:
        fingerprint=cnf.save(formula_path)
        result=dict(blocked=sorted(blocked),cycles=cycles,prefix=list(prefix),alternatives=alternatives,
                    cnf=fingerprint,clauses=len(cnf.clauses))
        try:
            raw.unlink(missing_ok=True)
            proc=subprocess.run([str(p.joins.partner.SOLVER),"-q","--seed=1","--lrat","--no-binary",
                str(formula_path),str(raw)],capture_output=True,timeout=max(.01,until-monotonic()))
        except subprocess.TimeoutExpired: return dict(status="open",**result)
        if proc.returncode==20 and b"s UNSATISFIABLE" in proc.stdout:
            dest=folder/"proofs"/(fingerprint+".lrat.gz")
            dest.parent.mkdir(exist_ok=True)
            result.update(status="excluded",proof=dest.relative_to(folder).as_posix(),
                          raw=p.joins.archive(raw,dest),compressed=digest(dest))
            result["replay"]=p.check_proof(formula_path,dest,compiler[0])
            fixed.compact(tmp,*compiler,result)
            return result
        if proc.returncode!=10 or b"s SATISFIABLE" not in proc.stdout: raise ValueError(proc.stderr[-300:])
        truth={int(v) for l in proc.stdout.splitlines() if l.startswith(b"v ") for v in l.split()[1:] if int(v)>0}
        path,components=decode(chosen,truth,prefix)
        if not components:
            if len(path)!=96 or set(path)&blocked or (alternatives is not None and
                    not any(not set(path).intersection(extra) for extra in alternatives)):
                raise ValueError("Incorrect witness")
            return dict(status="witness",path=path,all_pairs=bank.check_path(path,8),**result)
        cycles.extend(components)
        cnf,chosen=builder(blocked,cycles,alternatives,prefix)

def replay(folder,tmp,checker,row,builder=formula):
    cnf,_=builder(set(row["blocked"]),row["cycles"],row["alternatives"],row["prefix"])
    file=tmp/"replay.cnf"
    if cnf.save(file)!=row["cnf"]: raise ValueError("Formula differs")
    if row["status"]=="excluded":
        proof=folder/row["proof"]
        if digest(proof)!=row["compressed"] or p.check_proof(file,proof,checker)!=row["replay"]:
            raise ValueError("Proof replay differs")
    if row["status"]=="witness":
        path=row["path"]
        if (bank.check_path(path,8)!=4560 or path[:len(row["prefix"])]!=row["prefix"] or
                set(path)&set(row["blocked"]) or (row["alternatives"] is not None and
                not any(not set(path)&set(extra) for extra in row["alternatives"]))): raise ValueError("Path differs")

if __name__=="__main__":
    dest=HERE/"groups.json"
    rows=load(dest) if dest.exists() else {}
    with TemporaryDirectory() as d:
        tmp=Path(d)
        compiler=compilers(tmp)
        for root,targets in sorted(groups().items(),key=lambda item:len(item[1])):
            tag=str(root)
            blocked=set.intersection(*targets.values())
            if tag not in rows or rows[tag]["status"]=="open":
                rows[tag]=query(HERE,tmp,compiler,blocked,float(sys.argv[1]),previous=rows.get(tag))
                rows[tag]["members"]=sorted(targets)
                save(dest,rows)
            replay(HERE,tmp,compiler[0],rows[tag])
            print(root,len(targets),len(blocked),rows[tag]["status"],flush=True)
