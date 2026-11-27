"""Query only the four R277 donors without an existing 192 exclusion and assemble the eleven-shape table."""
from argparse import ArgumentParser
from collections import defaultdict
from hashlib import sha256
from lift_single278 import HERE,MS,R277,face,read,save,bank,checked,word

FOLDER=HERE/"remaining-one-crossing"
SOURCE=R277/"q8-arms.json"
FOUR={"dfb1dd50","26ef09aa","d3c8dbd5","0d1d1415"}
def filehash(p):return sha256(p.read_bytes()).hexdigest()
def shapekey(s):return sha256(bytes.fromhex(s)).hexdigest()
def inherited():
    d=MS/"252-shorter-reference-segments";c=d/"census-68.json";pr=d/"replay-68-192.json"
    census=read(c);receipt=read(pr)
    assert receipt["census_sha256"]==filehash(c) and receipt["all_excluded"] and receipt["target"]==192
    assert receipt["all_new_endpoints_reviewed"]
    return set(census["all_ids"])

def prepare():
    rows=read(SOURCE);new=read(R277/"q8-new.json");ar=inherited()
    old=set(rows)-new.keys()
    missing={k for k in old if shapekey(k) not in ar}
    assert len(rows)==11 and len(new)==3 and len(old)==8 and {shapekey(k)[:8] for k in missing}==FOUR
    roots={};ends={};families=defaultdict(list)
    for s in sorted(missing):
        p=rows[s]["joined_q8"];assert word(p).hex()==s and len(p)==97 and bank.check_path(p,8)
        ends[s]=[]
        for direction,order in enumerate((p,p[::-1])):
            k,n,_=face.rooted(order);port=order[0]
            roots[k]=dict(parent=[v^port for v in order],normalized=n,raw_endpoint=port,minimum_omissions=0,
                          shape=s,direction=direction)
            ends[s].append(dict(root=k,raw_endpoint=port,direction=direction));families[port].append(k)
    assert len(roots)==8 and sorted(map(len,families.values()))==[4,4]
    groups=[dict(id="port-"+str(port),rank=0,raw_endpoint=port,parent_edges=96,minimum_omissions=0,keys=sorted(keys))
            for port,keys in sorted(families.items())]
    FOLDER.mkdir(exist_ok=True)
    data=dict(roots=roots,endpoints=ends,groups=groups,input_sha256=filehash(SOURCE))
    save(FOLDER/"plan.json",data)
    lower=FOLDER/"old-placements.json"
    if not lower.exists():
        data267=read(MS/"267-fixed-arm-extensions/placements.json")["roots"];archive={}
        for k,r in roots.items():
            A=r["normalized"];blocked=set(A[1:]);best=[0];ref=None
            for old,record in data267.items():
                witness=record["expanded_placement"]
                for name in ("parent","partner"):
                    p=witness[name]
                    for backwards,q in enumerate((p,p[::-1])):
                        shifted=[u^q[0] for u in q];stop=next((i for i,u in enumerate(shifted) if u in blocked),len(q))
                        if stop>len(best):
                            best=shifted[:stop];ref=dict(source_root=old,side=name,reverse=backwards,through=stop-1)
            archive[k]=dict(parent=A,best=checked(A,best),source=ref)
        save(lower,dict(roots=archive,source_sha256=filehash(MS/"267-fixed-arm-extensions/placements.json")))
    return data

def combine():
    c=read(SOURCE);prior=inherited();new=read(R277/"q8-new.json")
    fresh=read(HERE/"one-crossing/summary.json")["roots"];remaining=read(FOLDER/"summary.json")["roots"]
    assert set(read(R277/"nearby-direct-single-scans.json"))==set(read(R277/"nearby-direct-double-scans.json"))==set(c)
    assert read(R277/"nearby-direct-single-parents.json")==read(R277/"nearby-direct-double-parents.json")=={}
    allrows={}
    for s,r in sorted(c.items()):
        h=shapekey(s);p=r["joined_q8"];records=[]
        for direction,q in enumerate((p,p[::-1])):
            root,normalized,_=face.rooted(q)
            if h in prior:
                cap=191;source="252-shorter-reference-segments/replay-68-192.json"
                reference=read(MS/"253-repeated-segment-growth/closure.json")["paths"][h]
                assert word(reference).hex()==s and any(face.rooted(z)[1]==normalized for z in (reference,reference[::-1]))
            else:
                src=fresh if s in new else remaining
                assert src[root]["shape"]==s and src[root]["parent_edges"]==96
                cap=src[root]["maximum"]
                source=("one-crossing" if s in new else "remaining-one-crossing")+"/summary.json"
            records.append(dict(direction=direction,root=root,maximum=cap,source=source))
        allrows[s]=dict(shape_id=h,ends=records,interval_ceiling=max(x["maximum"] for x in records))
    pins={str(p.relative_to(MS)):filehash(p) for p in [SOURCE,R277/"nearby-direct-single-scans.json",
          R277/"nearby-direct-double-scans.json",HERE/"one-crossing/summary.json",FOLDER/"summary.json",
          MS/"252-shorter-reference-segments/replay-68-192.json",MS/"252-shorter-reference-segments/census-68.json",
          MS/"253-repeated-segment-growth/closure.json"]}
    save(FOLDER/"interval-coverage.json",dict(covered=sum(x["interval_ceiling"]<192 for x in allrows.values()),shapes=allrows,sources=pins))
    print("Interval ceilings",[(r["shape_id"][:8],r["interval_ceiling"]) for r in allrows.values()],flush=True)

def main():
    cli=ArgumentParser();cli.add_argument("action",choices=["search","audit"])
    cli.add_argument("--target",type=int,default=192);cli.add_argument("--seconds",type=float,default=5)
    cli.add_argument("--depth",type=int,default=0);cli.add_argument("--only",type=int,nargs="+")
    a=cli.parse_args();data=prepare();h=face.dependencies(MS)
    if a.action=="search":
        a.standard=False;a.refined_only=False;a.through=0;a.parents=None
        face.search(FOLDER,data,a,h,{})
        cand=FOLDER/("candidate-"+str(a.target)+".json")
        if a.target>=192 and cand.exists():
            rows=read(cand)
            for p in rows.values():assert bank.check_path(p,9) and len(p)-1==a.target
            save(HERE/("candidate-"+str(a.target)+"-remaining.json"),rows)
    else:
        face.audit(FOLDER,data,FOLDER,"old",h,dict(roots={}))
        combine()

if __name__=="__main__":main()
