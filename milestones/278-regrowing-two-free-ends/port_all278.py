"""Split open 192-edge two-crossing queries, then audit all 22 archived middle shapes."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import subprocess
from archive import HERE,input_paths,code,lift,read,write
from whole_middle import encode,geometry,rebuild,build_answer
from port278 import check_cycle,short_cycles,sites_checked
from middle_witnesses import two_cuts,key as middle_key,validate_chart
from middle_clauses import reconstruct

TARGET=192
SELECTED={"190-375","190-377","190-373","190-1041"}

def table():
    jobs=read("whole-middle.json");counts=Counter();records=Counter();found=set()
    for name,path in input_paths():
        for ax,origin,raw,m in two_cuts(path):
            k=middle_key(m);counts[k]+=1;records[k]+=len(path)==192
            r=jobs[k]
            if name==r["source"] and ax==r["axis"]:
                assert origin==r["origin"] and m==r["m"] and sites_checked(m,8)
                found.add(k)
    assert len(jobs)==22 and found==set(jobs)==set(counts)
    assert all(counts[k]==r["occurrences"] and records[k]==r["records"] for k,r in jobs.items())
    return jobs

def file_for(r,maj):
    if (r["source"],r["axis"],maj)==("190-418",8,1):return "port-190-418-192-1.json"
    return "port-%s-axis%d-192-%d.json"%(r["source"],r["axis"],maj)


def plan(m,maj):
    ports=(m[0],m[-1]);inner=set(m[1:-1]);both={}
    for p in ports:
        raw=sorted(p^(1<<j) for j in range(8) if p^(1<<j) not in inner)
        other=next(q for q in ports if q!=p)
        eligible=[v for v in raw if (v^other).bit_count()!=1]
        both[p]=(eligible,raw)
    port=min(ports,key=lambda p:(len(both[p][0])+int(p.bit_count()%2==maj),p))
    eligible,raw=both[port]
    return dict(port=port,other=next(p for p in ports if p!=port),neighbours=raw,geometric_cycles=sorted(set(raw)-set(eligible)),
                empty_allowed=port.bit_count()%2==maj,branches=([None] if port.bit_count()%2==maj else [])+eligible)

def make_cnf(m,maj,part,chosen_neighbor,cycles):
    f,x=encode(m,TARGET,maj,cycles,True)
    for v in part["neighbours"]:
        f.clauses.append([x[v] if v==chosen_neighbor else -x[v]])
    return f,x

def check_path(m,axis,origin,port,neighbour,path,maj):
    pairs=sites_checked(path,9)
    assert len(path)==TARGET+1 and all(v.bit_count()%2==maj for v in (path[0],path[-1]))
    upper=[v for v in path if v>=256]
    assert len(upper)==len(m) and (upper==[v+256 for v in m] or upper==[v+256 for v in m[::-1]])
    assert sum((a^b)==256 for a,b in zip(path,path[1:]))==2
    actual=[v for v in path if v<256 and (v^port).bit_count()==1]
    assert actual==([] if neighbour is None else [neighbour])
    native=[lift(axis,origin,v) for v in path];assert sites_checked(native,9)==pairs
    return dict(path=path,literal_donor_coordinates=native,unordered_pairs=pairs)

def search_one(a,key,r,maj):
    m=r["m"];part=plan(m,maj);file=file_for(r,maj)
    initial=r["targets"][f"192-{maj}"]["cycles"]+short_cycles(m,part["geometric_cycles"])
    for c in short_cycles(m,part["geometric_cycles"]):check_cycle(c)
    label=dict(source=r["source"],source_axis=r["axis"],origin=r["origin"],middle_key=key,middle=m,target=TARGET,majority=maj,partition=part)
    ledger=read(file) if (HERE/file).exists() else dict(**label,rows={})
    assert all(ledger[k]==v for k,v in label.items())
    with TemporaryDirectory(prefix="q9-port278-") as d:
        tmp=Path(d);tools=rebuild.masks.compilers(tmp);rebuild.masks.fixed.HERE=HERE
        for v in part["branches"]:
            tag=str(v) if v is not None else "empty"
            if a.only and tag not in a.only:continue
            prior=ledger["rows"].get(tag,{})
            if prior.get("status") in ("excluded","witness"):continue
            cycles=prior.get("cycles",initial);stop=monotonic()+a.seconds
            while True:
                f,x=make_cnf(m,maj,part,v,cycles);cnf=tmp/"partner.cnf";trace=tmp/"proof.lrat";trace.unlink(missing_ok=True)
                digest=f.save(cnf)
                row=dict(neighbour=v,cycles=cycles,cnf=digest,clauses=len(f.clauses),four_cube_caps=True)
                try:
                    job=subprocess.run([str(geometry.SOLVER),"-q","--seed="+str(a.seed),"--lrat","--no-binary",str(cnf),str(trace)],
                        timeout=max(.03,stop-monotonic()),capture_output=True)
                except subprocess.TimeoutExpired:
                    row["status"]="open";break
                if job.returncode==20:
                    assert b"s UNSATISFIABLE" in job.stdout
                    proof=HERE/"whole-proofs"/(digest+".lrat.gz");proof.parent.mkdir(exist_ok=True)
                    row.update(status="excluded",proof=proof.relative_to(HERE).as_posix(),
                        raw=rebuild.masks.p.joins.archive(trace,proof),compressed=rebuild.masks.digest(proof),
                        replay=rebuild.masks.p.check_proof(cnf,proof,tools[0]))
                    rebuild.masks.fixed.compact(tmp,*tools,row);break
                assert job.returncode==10 and b"s SATISFIABLE" in job.stdout
                truth={int(t) for line in job.stdout.splitlines() if line.startswith(b"v ") for t in line.split()[1:]}
                sites={u for u,k in x.items() if k in truth}
                assert len(sites)+len(m)==TARGET+1
                path,more=build_answer(m,sites)
                if more:
                    cycles=cycles+more;continue
                row.update(status="witness",**check_path(m,r["axis"],r["origin"],part["port"],v,path,maj))
                write("candidate-192.json",dict(source=r["source"],majority=maj,port=part["port"],**row));break
            ledger["rows"][tag]=row;write(file,ledger)
            print(r["source"],r["axis"],maj,"port",part["port"],"neighbour",v,row["status"],flush=True)
            if row["status"]=="witness":return True


def solve(a):
    for key,r in table().items():
        if r["source"] not in (set(a.sources) if a.sources else SELECTED):continue
        for maj in (0,1):
            direct=r["targets"][f"192-{maj}"]
            if direct["status"]=="witness":return True
            if direct["status"]=="excluded":continue
            if search_one(a,key,r,maj):return True
    return False

def verify_proof(f,row,tmp,checker):
    cf=tmp/"audit.cnf"
    assert f.save(cf)==row["cnf"] and len(f.clauses)==row["clauses"]
    if row["status"]=="excluded":
        proof=HERE/row["proof"];assert sha256(proof.read_bytes()).hexdigest()==row["compressed"]
        assert rebuild.masks.p.check_proof(cf,proof,checker)==row["replay"]

def base(m,maj,row,tmp):
    four=row.get("four_cube_caps",False)
    receipt=reconstruct(m,TARGET,maj,row["cycles"],four=four)
    f,x=encode(m,TARGET,maj,row["cycles"],four)
    assert f.save(tmp/"base.cnf")==receipt["cnf"] and len(f.clauses)==receipt["clauses"]
    return f,x

def check_source(key,r,maj,tmp,checker):
    m=r["m"];ports={m[0],m[-1]};file=file_for(r,maj);direct=r["targets"][f"192-{maj}"]
    assert (direct["target"],direct["majority_if_even"])==(TARGET,maj)
    result=dict(direct=direct["status"],empty_permitted_by_parity={str(p):p.bit_count()%2==maj for p in sorted(ports)})
    if direct["status"] in ("witness","excluded"):
        f,_=base(m,maj,direct,tmp);verify_proof(f,direct,tmp,checker);del f
        if direct["status"]=="excluded":result["direct_proof"]=direct["proof"]
        else:
            path=direct["path"];sites_checked(path,9)
            assert len(path)==TARGET+1 and all(v.bit_count()%2==maj for v in (path[0],path[-1]))
            try:validate_chart(path,m)
            except AssertionError:validate_chart(path[::-1],m)
            native=[lift(r["axis"],r["origin"],v) for v in path];sites_checked(native,9)
            result["positive"]=dict(path=path,original_coordinates=native)
    if not (HERE/file).is_file():
        result["status"]=result["direct"]
        return result
    ledger=read(file);part=ledger["partition"]
    assert (ledger["source"],ledger["source_axis"],ledger["origin"],ledger["middle_key"],ledger["middle"],ledger["target"],ledger["majority"])==(r["source"],r["axis"],r["origin"],key,m,TARGET,maj)
    def literal(p):
        q,=ports-{p}
        raw={v for v in range(256) if (v^p).bit_count()==1 and v not in m[1:-1]}
        loops={v for v in raw if (v^q).bit_count()==1}
        branches=(raw-loops)|({None} if p.bit_count()%2==maj else set())
        return raw,loops,branches
    p=part["port"];q,=ports-{p};raw,loops,branches=literal(p)
    assert p==min(ports,key=lambda z:(len(literal(z)[2]),z)) and q==part["other"]
    assert set(part["neighbours"])==raw and set(part["geometric_cycles"])==loops
    assert (None in branches)==part["empty_allowed"] and set(part["branches"])==branches and len(part["branches"])==len(branches)
    assert plan(m,maj)==part
    for v in loops:
        cycle=[p]+[256+u for u in (m if m[0]==p else m[::-1])]+[q,v];check_cycle(cycle)
    keys={str(v) if v is not None else "empty":v for v in branches}
    assert set(ledger["rows"])<=keys.keys()
    statuses={};allowed=sorted(set(range(256))-set(m[1:-1]))
    for tag,v in sorted(keys.items()):
        row=ledger["rows"].get(tag)
        if row is None:statuses[tag]="pending";continue
        assert row["neighbour"]==v and row["four_cube_caps"]
        f,x=base(m,maj,row,tmp)
        for u in sorted(raw):
            variable=1+allowed.index(u);assert x[u]==variable
            f.clauses.append([variable if u==v else -variable])
        verify_proof(f,row,tmp,checker);del f
        assert row["status"] in ("witness","open","excluded")
        if row["status"]=="witness":
            w=check_path(m,r["axis"],r["origin"],p,v,row["path"],maj)
            assert all(row[k]==z for k,z in w.items());result["positive"]=w
        statuses[tag]=row["status"]
    outcome="witness" if "witness" in statuses.values() else ("excluded" if all(st=="excluded" for st in statuses.values()) else "open")
    assert {result["direct"],outcome}!={"witness","excluded"}
    result.update(status=result["direct"] if result["direct"] in ("witness","excluded") else outcome,
        port=p,immediate_cycles=sorted(loops),branches=statuses,partition_file=file,partition_sha256=sha256((HERE/file).read_bytes()).hexdigest())
    return result

def replay():
    jobs=table();out={};covered=Counter();total=Counter()
    with TemporaryDirectory(prefix="q9-allports-audit-") as d:
        tmp=Path(d);checker=rebuild.masks.compilers(tmp)[0]
        for k,r in sorted(jobs.items()):
            parities={str(maj):check_source(k,r,maj,tmp,checker) for maj in (0,1)}
            closed=all(z["status"]=="excluded" for z in parities.values());lower=191 if r["records"] else 190
            out[k]=dict(source=r["source"],axis=r["axis"],edges=len(r["m"])-1,occurrences=r["occurrences"],record_occurrences=r["records"],
                parity=parities,excluded_192=closed,archived_lower=lower,upper=191 if closed else None,
                exact_maximum=191 if closed and lower==191 else None)
            number=sum(s["status"]=="excluded" for s in parities.values())
            total.update(middles=1,charts=r["occurrences"],record_charts=r["records"],parities=2)
            covered.update(middles=int(closed),charts=closed*r["occurrences"],record_charts=closed*r["records"],parities=number)
            print(r["source"],"axis",r["axis"],"certified parities",number,flush=True)
    write("all-middle-port-coverage.json",dict(target=TARGET,whole_middle_sha256=sha256((HERE/"whole-middle.json").read_bytes()).hexdigest(),total=total,excluded=covered,rows=out))
    print("192-edge exclusions",dict(covered),"of",dict(total),flush=True)

if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("action",choices=("solve","replay","finish"));ap.add_argument("--sources",nargs="+",choices=sorted(SELECTED))
    ap.add_argument("--only",nargs="+");ap.add_argument("--seconds",type=float,default=10);ap.add_argument("--seed",type=int,default=1)
    a=ap.parse_args()
    if a.action in ("solve","finish"):solve(a)
    if a.action in ("replay","finish"):replay()

