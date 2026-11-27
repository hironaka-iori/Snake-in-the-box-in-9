"""Split the remaining 192-edge, odd-endpoint case of the 190-418 middle by a port neighbour."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import subprocess
from archive import HERE,input_paths,code,lift,read,write
from whole_middle import encode,geometry,rebuild,build_answer

SOURCE="190-418"
TARGET=192
MAJ=1
OUT="port-190-418-192-1.json"

def sites_checked(path,d):
    assert len(set(path))==len(path) and all(0<=v<1<<d for v in path)
    for i,v in enumerate(path):
        for j in range(i):
            assert ((path[j]^v).bit_count()==1)==(i==j+1)
    return len(path)*(len(path)-1)//2

def source():
    key,row=next((k,v) for k,v in read("whole-middle.json").items() if v["source"]==SOURCE)
    middle=row["m"];assert len(middle)==93 and code(middle).hex()==key and sites_checked(middle,8)
    path=next(p for name,p in input_paths() if name==SOURCE)
    axis=row["axis"];origin=row["origin"];bit=1<<axis
    indices=[i for i,(u,v) in enumerate(zip(path,path[1:])) if u^v==bit]
    first,last=indices;assert path[first]==origin
    projected=[(v^origin)&(bit-1)|(((v^origin)>>(axis+1))<<axis) for v in path[first+1:last+1]]
    assert middle==projected
    return key,row

def plan(m):
    ports=(m[0],m[-1]);inner=set(m[1:-1]);both={}
    for p in ports:
        raw=sorted(p^(1<<j) for j in range(8) if p^(1<<j) not in inner)
        other=next(q for q in ports if q!=p)
        eligible=[v for v in raw if (v^other).bit_count()!=1]
        both[p]=(eligible,raw)
    port=min(ports,key=lambda p:(len(both[p][0])+int(p.bit_count()%2==MAJ),p))
    eligible,raw=both[port]
    return dict(port=port,other=next(p for p in ports if p!=port),neighbours=raw,geometric_cycles=sorted(set(raw)-set(eligible)),
                empty_allowed=port.bit_count()%2==MAJ,branches=([None] if port.bit_count()%2==MAJ else [])+eligible)

def short_cycles(m,common):
    return [[m[0]]+[256+v for v in m]+[m[-1],v] for v in common]

def check_cycle(cycle):
    s=set(cycle);assert len(s)==len(cycle)>=4
    for i,u in enumerate(cycle):
        assert {v for v in s if (u^v).bit_count()==1}=={cycle[i-1],cycle[(i+1)%len(cycle)]}

def make_cnf(m,part,chosen_neighbor,cycles):
    f,x=encode(m,TARGET,MAJ,cycles,True)
    for v in part["neighbours"]:
        f.clauses.append([x[v] if v==chosen_neighbor else -x[v]])
    return f,x

def check_path(m,axis,origin,port,neighbour,path):
    pairs=sites_checked(path,9)
    assert len(path)==TARGET+1 and all(v.bit_count()%2==MAJ for v in (path[0],path[-1]))
    upper=[v for v in path if v>=256]
    assert len(upper)==len(m) and (upper==[v+256 for v in m] or upper==[v+256 for v in m[::-1]])
    assert sum((a^b)==256 for a,b in zip(path,path[1:]))==2
    actual=[v for v in path if v<256 and (v^port).bit_count()==1]
    assert actual==([] if neighbour is None else [neighbour])
    native=[lift(axis,origin,v) for v in path];assert sites_checked(native,9)==pairs
    return dict(path=path,literal_donor_coordinates=native,unordered_pairs=pairs)

def solve(a):
    key,r=source();m=r["m"];part=plan(m)
    initial=r["targets"]["192-1"]["cycles"]+short_cycles(m,part["geometric_cycles"])
    for c in short_cycles(m,part["geometric_cycles"]):check_cycle(c)
    label=dict(source=SOURCE,source_axis=r["axis"],origin=r["origin"],middle_key=key,middle=m,target=TARGET,majority=MAJ,partition=part)
    ledger=read(OUT) if (HERE/OUT).exists() else dict(**label,rows={})
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
                f,x=make_cnf(m,part,v,cycles);cnf=tmp/"partner.cnf";trace=tmp/"proof.lrat";trace.unlink(missing_ok=True)
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
                row.update(status="witness",**check_path(m,r["axis"],r["origin"],part["port"],v,path))
                write("candidate-192.json",dict(source=SOURCE,majority=MAJ,port=part["port"],**row));break
            ledger["rows"][tag]=row;write(OUT,ledger)
            print(SOURCE,"port",part["port"],"neighbour",v,row["status"],flush=True)
            if row["status"]=="witness":return

def replay():
    key,r=source();m=r["m"];ledger=read(OUT);part=ledger["partition"];ports={m[0],m[-1]}
    assert ledger["middle"]==m and ledger["source_axis"]==r["axis"] and ledger["origin"]==r["origin"] and ledger["middle_key"]==key
    assert ledger["target"]==TARGET and ledger["majority"]==MAJ and ledger["source"]==SOURCE
    def literal(p):
        q,=ports-{p}
        raw={v for v in range(256) if (v^p).bit_count()==1 and v not in m[1:-1]}
        loops={v for v in raw if (v^q).bit_count()==1}
        branches=(raw-loops)|({None} if p.bit_count()%2==MAJ else set())
        return raw,loops,branches
    p=part["port"];q,=ports-{p};raw,loops,branches=literal(p)
    assert p==min(ports,key=lambda s:(len(literal(s)[2]),s)) and q==part["other"] and len(raw)==len(part["neighbours"])
    assert raw==set(part["neighbours"]) and loops==set(part["geometric_cycles"]) and branches==set(part["branches"])
    assert (None in branches)==part["empty_allowed"] and len(branches)==len(part["branches"])
    for v in loops:
        loop=[p]+[256+u for u in (m if p==m[0] else m[::-1])]+[q,v];check_cycle(loop)
    keys={str(v) if v is not None else "empty":v for v in branches};assert set(ledger["rows"])<=keys.keys()
    statuses={};witnesses={}
    with TemporaryDirectory(prefix="q9-review278-") as d:
        tmp=Path(d);checker=rebuild.masks.compilers(tmp)[0]
        def verify(f,row):
            cnf=tmp/"review.cnf";assert f.save(cnf)==row["cnf"] and len(f.clauses)==row["clauses"]
            if row["status"]=="excluded":
                proof=HERE/row["proof"];assert sha256(proof.read_bytes()).hexdigest()==row["compressed"]
                assert rebuild.masks.p.check_proof(cnf,proof,checker)==row["replay"]
        for tag,v in sorted(keys.items()):
            if tag not in ledger["rows"]:statuses[tag]="pending";continue
            row=ledger["rows"][tag];assert row["neighbour"]==v and row["four_cube_caps"]
            f,x=encode(m,TARGET,MAJ,row["cycles"],True)
            for u in sorted(raw):f.clauses.append([x[u]] if u==v else [-x[u]])
            verify(f,row)
            if row["status"]=="witness":
                matched=check_path(m,r["axis"],r["origin"],p,v,row["path"])
                assert all(row[k]==s for k,s in matched.items());witnesses[tag]=matched
            assert row["status"] in ("excluded","open","witness");statuses[tag]=row["status"]
        opposite=r["targets"]["192-0"];assert opposite["status"]=="excluded"
        f,_=encode(m,TARGET,0,opposite["cycles"],opposite.get("four_cube_caps",False));verify(f,opposite)
    closed=all(v=="excluded" for v in statuses.values())
    out=dict(source=SOURCE,middle_key=key,middle_edges=len(m)-1,occurrences=r["occurrences"],target=TARGET,
        even_endpoint_parity_proof=opposite["proof"],odd_endpoint_parity=dict(port=p,empty_allowed=None in branches,
            first_neighbours=sorted(raw),immediate_cycles=sorted(loops),branches=statuses),
        excluded_both_parities=closed,positive_paths=witnesses,ledger_sha256=sha256((HERE/OUT).read_bytes()).hexdigest())
    write("port-190-418-replay.json",out);print("Port split",statuses,"both parities excluded",closed,flush=True)

if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("action",choices=("solve","replay"));ap.add_argument("--only",nargs="+")
    ap.add_argument("--seconds",type=float,default=10);ap.add_argument("--seed",type=int,default=1);a=ap.parse_args()
    if a.action=="solve":solve(a)
    else:replay()
