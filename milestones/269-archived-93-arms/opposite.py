"""Find a target-length rooted partner of any selected 93-edge parent."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0,str(MS/"268-archived-94-arms"))
import search as original
from deficit import model as deficit_model
from search import aligned, bank, pack, rebuild, read, write, family_model

def roots():
    return {k:r for k,r in read(MS/"266-rebuilding-one-arm/parents.json")["parents"].items()
            if r["retain_edges"]==93}

def legal_next(prefix):
    last=prefix[-1]
    return [last^(1<<j) for j in range(8) if last^(1<<j) not in prefix and
            all(((last^(1<<j))^v).bit_count()!=1 for v in prefix[:-1])]

def translate_domains(parents,prefix):
    tip=prefix[-1]
    foreign=set(prefix[:-1])
    for u in prefix[:-1]:
        foreign.update(u^(1<<j) for j in range(8))
    foreign.discard(tip)
    return {k:{v^tip for v in set(p[1:])|foreign}
            for k,p in parents.items() if not set(prefix[1:]).intersection(p)}

def search():
    ap=ArgumentParser()
    ap.add_argument("--deficit",action="store_true")
    ap.add_argument("--plan",action="store_true")
    ap.add_argument("--length",type=int,choices=(96,97,98),default=98)
    ap.add_argument("--seconds",type=float,default=4)
    ap.add_argument("--depth",type=int,choices=(0,1,2,3),default=0)
    ap.add_argument("--only",type=int,nargs="+")
    ap.add_argument("--individual",action="store_true")
    ap.add_argument("--published",action="store_true")
    a=ap.parse_args()
    if a.deficit:original.base_model=deficit_model
    source=roots()
    images=list(bank.permutation_images())
    group_path=HERE/"groups.json"
    if a.plan:
        groups=pack({k:r["parent"] for k,r in source.items()},images,87)
        write(group_path,groups)
        print("Groups",[(len(g["ranks"]),len(g["blocked"])) for g in groups])
        return
    jobs=read(HERE/f"queries-{a.length}.json") if (HERE/f"queries-{a.length}.json").exists() else {}
    dest=HERE/f"queries-{a.length}.json"
    with TemporaryDirectory() as td:
        tmp=Path(td)
        tools=rebuild.masks.compilers(tmp)
        for i,g in enumerate(read(group_path)):
            if a.only and i not in a.only:
                continue
            complete=aligned(g,source,images)
            subset=[k for k in complete if not a.published or source[k]["partners"]]
            if not subset:
                continue
            families=[[k] for k in subset] if a.individual else [subset]
            for keep in families:
                parents={k:complete[k] for k in keep}
                tag=",".join(keep)
                job=jobs.setdefault(tag,dict(group=i,keys=keep,rows={}))
                assert job["group"]==i and job["keys"]==keep
                rows=job["rows"]
                def visit(prefix):
                    address=",".join(map(str,prefix))
                    domains=translate_domains(parents,prefix)
                    if not domains:
                        return
                    for ancestor in jobs.values():
                        if ancestor["group"]==i and set(domains)<=set(ancestor["keys"]):
                            for length in range(1,len(prefix)+1):
                                old=ancestor["rows"].get(",".join(map(str,prefix[:length])),{})
                                if old.get("status")=="excluded":
                                    return
                    if len(prefix)<=a.depth:
                        for u in legal_next(prefix):
                            visit(prefix+[u])
                        return
                    old=rows.get(address,{})
                    if old.get("status")=="witness":return
                    sites=list(domains.values())
                    common=set.intersection(*sites)
                    rebuild.model=family_model(sites)
                    rec=rebuild.solve(HERE,tmp,tools,common,a.length-len(prefix)+1,[0],old.get("cycles",[]),[],a.seconds)
                    if a.deficit:rec["encoding"]="parity-deficit"
                    if rec["status"]=="witness":
                        partner=prefix[:-1]+[u^prefix[-1] for u in rec["path"]]
                        rec["joined"]={}
                        for k,p in parents.items():
                            if set(p).intersection(partner)=={0}:
                                path=p[::-1]+[256+v for v in partner]
                                rebuild.geometry.verify(path,9)
                                rec["joined"][k]=path
                        assert rec["joined"]
                        if a.length==98:
                            write(HERE/"candidate-192.json",rec["joined"])
                    rows[address]=rec
                    write(dest,jobs)
                    print(i,len(keep),a.length,prefix,rec["status"],flush=True)
                visit([0])
                if (HERE/"candidate-192.json").exists():return
    write(dest,jobs)
if __name__=="__main__":
    search()
