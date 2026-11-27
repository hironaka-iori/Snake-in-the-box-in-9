"""Check archive incidence, degree bounds, numerical scope and all retained constructive witnesses."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json
from archive import HERE, read, write, code, input_paths, cases as source_cases
from whole_middle import encode,inputs,rebuild

def audit_path(path,d):
    assert len(set(path))==len(path) and all(0<=v<1<<d for v in path)
    for i,u in enumerate(path):
        for j in range(i+1,len(path)):
            assert ((u^path[j]).bit_count()==1)==(i+1==j)
    return len(path)*(len(path)-1)//2

def capacity(d):
    best=0
    for mask in range(1<<(1<<d)):
        sites={v for v in range(1<<d) if mask>>v&1}
        if len(sites)<=best: continue
        g={v:{v^(1<<j) for j in range(d)}&sites for v in sites}
        if any(len(a)>2 for a in g.values()):continue
        rest=set(sites)
        while rest:
            u=next(iter(rest));seen={u};queue=[u]
            for x in queue:
                for y in g[x]-seen:seen.add(y);queue.append(y)
            if all(len(g[y])==2 for y in seen):break
            rest-=seen
        else:best=len(sites)
    return best

def independently_count():
    lengths=Counter();shapes=Counter();by_size=Counter();names=set()
    for key,p in input_paths():
        for j in range(9):
            side=[(v>>j)&1 for v in p]
            cuts=[i for i in range(1,len(p)) if side[i]!=side[i-1]]
            if len(cuts)!=2:continue
            lo,hi=cuts
            m=p[lo:hi]
            assert len(set(side[lo:hi]))==1
            lengths[len(p)-1]+=1; by_size[len(m)-1]+=1;names.add(key)
            shapes[code(m).hex()]+=1
    return dict(charts=dict(lengths),paths=dict(Counter(x.split("-")[0] for x in names)),
        middle_edges=dict(sorted(by_size.items())),distinct_middles=len(shapes),middle_occurrences=shapes)

def main():
    cap={str(d):capacity(d) for d in (2,3)};assert cap=={"2":3,"3":5}
    census=independently_count();mid=inputs()
    assert census["middle_occurrences"]==Counter({k:r["occurrences"] for k,r in mid.items()})
    rows={};claims={};best=0
    for f in sorted(HERE.glob("summary-*.json")):
        src=json.loads(f.read_bytes());tag=f.stem[8:]
        if "-" not in tag or not tag[0].isdigit():continue
        replay_file=HERE/("replay-"+tag+".json")
        if not replay_file.exists():continue
        replay=json.loads(replay_file.read_bytes());cases=read("cases-"+tag+".json")
        small=set(k for k,r in cases.items() if r["closed"] and replay["results"][k]["complete"])
        for k in small: assert replay["results"][k]["histogram"]==cases[k]["histogram"]
        counts=Counter(v["maximum_seen"] for k,v in cases.items() if k in small)
        max_known=max(v["maximum_seen"] for v in cases.values());best=max(best,max_known)
        refs=read("paths-"+tag+".json")
        archive_counts=Counter(r["edges"] for r in refs.values() if r["archive"] is not None)
        new_counts=Counter(r["edges"] for r in refs.values() if r["archive"] is None)
        rows[tag]=dict(charts=src["chart_occurrences"],distinct=len(cases),twice_complete=len(small),
            occurrences_complete=sum(cases[k]["occurrences"] for k in small),maxima=dict(counts),
            all_attained_max=max_known,archive_matches=dict(archive_counts),outside_archive=dict(new_counts),
            retained_all_high_paths=src["capture_complete"])
    qfile=HERE/"whole-middle.json"
    if qfile.exists():
        with TemporaryDirectory(prefix="q9-verify-") as d:
            temp=Path(d);checker=None
            for key,job in read(qfile.name).items():
                assert job["m"]==mid[key]["m"]
                for r in job["targets"].values():
                    n=r["target"];maj=r["majority_if_even"]
                    cnf,_=encode(job["m"],n,maj,r["cycles"],r.get("four_cube_caps",False));target=temp/"audit.cnf"
                    assert cnf.save(target)==r["cnf"] and len(cnf.clauses)==r["clauses"]
                    if r["status"]=="witness":assert len(r["path"])==n+1 and audit_path(r["path"],9)
                    elif r["status"]=="excluded":
                        if checker is None:checker=rebuild.masks.compilers(temp)[0]
                        proof=HERE/r["proof"]
                        assert sha256(proof.read_bytes()).hexdigest()==r["compressed"]
                        assert rebuild.masks.p.check_proof(target,proof,checker)==r["replay"]
                    else:assert r["status"]=="open"
                claims[key]=dict(source=job["source"],edges=len(job["m"])-1,occurrences=job["occurrences"],targets={k:r["status"] for k,r in job["targets"].items()})
    files=HERE/"lift-placements.json";lifts={}
    if files.exists():
        for k,r in read(files.name)["results"].items():
            m=r["middle"];assert k==code(m).hex() and audit_path(m,8)
            p=r["path"];a,b=r["arm_lengths"]
            assert p[a+1:a+1+len(m)]==[256+v for v in m] and len(p)-1==r["edges"]==a+b+len(m)+1
            assert sum((v^w)==256 for v,w in zip(p,p[1:]))==2
            lifts[k]=dict(middle_edges=len(m)-1,lower_edges=[a,b],joined_edges=r["edges"],pairs=audit_path(p,9))
    target_reports={}
    for f in sorted(HERE.glob("target-*.json")):
        _,minimum,width,target=f.stem.split("-")
        minimum,width,target=map(int,(minimum,width,target))
        evidence=read(f.name); inputs_,_,_=source_cases(width,minimum,True)
        seeds={sha256(k).hexdigest():v for k,v in inputs_.items()}
        assert seeds.keys()==evidence.keys()
        closed=Counter(); outcomes=Counter();same=0;same_orig=0;per_engine=Counter()
        for k,r in evidence.items():
            x=seeds[k];assert r["source"]==x["source"] and r["occurrences"]==x["occurrences"]
            for name,v in r["records"].items():
                source="Target.cs" if name=="degree-and-leaves" else "TargetReplay.cs"
                assert v["source_sha256"]==sha256((HERE/source).read_bytes()).hexdigest()
                per_engine[(name,v["status"])]+=1
                if v["status"]=="witness":assert len(v["path"])==target+1 and audit_path(v["path"],9)
            result=tuple(sorted(v["status"] for v in r["records"].values()))
            outcomes["+".join(result)]+=1
            if result==("excluded","excluded"):
                same+=1;same_orig+=r["occurrences"];closed[r["retained_edges"]]+=1
        target_reports[f.stem]=dict(target=target,width=width,minimum_donor_edges=minimum,cases=len(evidence),
            sources=sum(r["occurrences"] for r in evidence.values()),twice_closed=same,twice_closed_sources=same_orig,
            retained_lengths=dict(closed),outcomes=outcomes,by_worker={k+" "+v:n for (k,v),n in per_engine.items()})
    overlap=read("consecutive-overlap.json")
    overlap_numbers={k:v for k,v in overlap.items() if k!="paths"}
    assert overlap["archive_counts"]=={"190":1042,"191":131}
    for n,limit in overlap["maximum_shared_edges"].items():
        assert max(r["bound"] for r in overlap["paths"].values() if r["edges"]==int(n))==limit
    write("conclusions.json",dict(consecutive_overlap=overlap_numbers,target_specific=target_reports,archive=census,face_forest_capacities=cap,regrowth=rows,
        middle_only=claims,donor_lifts=lifts,best_regrown=best))
    print("Independent archive",census["charts"],"middle shapes",census["distinct_middles"])
    print("Complete case counts",[(k,v["twice_complete"],v["distinct"],v["all_attained_max"]) for k,v in rows.items()])
    print("Independent two-crossing lifts",Counter((v["middle_edges"],v["joined_edges"]) for v in lifts.values()))
if __name__=="__main__":main()



