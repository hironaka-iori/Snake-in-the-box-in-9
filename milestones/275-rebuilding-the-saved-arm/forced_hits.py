"""Use the exact endpoint bounds to make each known pair of differing sites a required hit."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from shared_sites import data
from rebuild_saved import HERE,MS,face,read,save

def main():
    ap=ArgumentParser();ap.add_argument("--pair",default="93",choices=["93","94"])
    ap.add_argument("--length",type=int,default=96);ap.add_argument("--seconds",type=float,default=9)
    ap.add_argument("--audit",action="store_true");opt=ap.parse_args()
    x=data()[opt.pair];n=opt.length;folder=HERE/"shared";folder.mkdir(exist_ok=True)
    h=face.dependencies(MS);caps=read(HERE/"opposite/summary.json")["roots"]
    groups=[];roots=[]
    for k,p,diff in zip(x["roots"],x["relative_parents"],x["omitted"]):
        if caps[k]["maximum"]>=len(p)+n:continue
        assert set(p[1:])==set(x["common"])|set(diff) and set(x["common"]).isdisjoint(diff)
        roots.append(k);groups.append(diff)
    assert groups
    file=folder/f"forced-{opt.pair}-{n}.json";blocked=set(x["common"])
    with TemporaryDirectory(prefix="q9-r275-forced-") as td:
        tmp=Path(td);tools=h.rebuild.masks.compilers(tmp)
        if not opt.audit:
            def formula(forbid,length,seed,cycles,seen):
                f,variables=h.deficit.model(forbid,length,seed,cycles,seen)
                f.clauses.extend([variables[v] for v in sorted(required)] for required in groups)
                return f,variables
            h.rebuild.model=formula
            old=read(file)["result"] if file.exists() else {}
            if old.get("status") in ("excluded","witness"):return
            result=h.rebuild.solve(folder,tmp,tools,blocked,n,[0],old.get("cycles",[]),[],opt.seconds)
            save(file,dict(pair=opt.pair,length=n,required_hits=groups,source_roots=roots,result=result))
        obj=read(file);r=obj["result"]
        assert obj["source_roots"]==roots and obj["required_hits"]==groups
        f,chosen=h.deficit.model(blocked,n,[0],r["cycles"],[])
        for k in roots:
            p=x["relative_parents"][x["roots"].index(k)]
            f.clauses.append([chosen[v] for v in range(256) if v!=0 and v in p and v not in blocked])
        name=tmp/"verify.cnf";assert f.save(name)==r["cnf"] and len(f.clauses)==r["clauses"]
        if r["status"]=="excluded":
            proof=folder/r["proof"]
            assert sha256(proof.read_bytes()).hexdigest()==r["compressed"] and h.rebuild.masks.p.check_proof(name,proof,tools[0])==r["replay"]
        if r["status"]=="witness":
            b=r["path"];assert b[0]==0 and h.original_audit.path_edges(b,8)==n and not blocked&set(b)
            assert all(set(b)&set(g) for g in groups)
        report=dict(status=r["status"],rooted_upper=[caps[k]["maximum"] for k in roots],
               source_roots=roots,required_hits=groups,formula=r["cnf"],replay=r.get("replay"))
        save(folder/f"forced-replay-{opt.pair}-{n}.json",report)
        print(opt.pair,n,groups,r["status"],flush=True)

if __name__=="__main__":main()
