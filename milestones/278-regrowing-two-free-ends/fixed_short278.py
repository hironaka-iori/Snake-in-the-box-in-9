"""Retain the full short arm and middle at a twice-crossed coordinate and rebuild the other arm."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json,sys
from archive import HERE,MS,charts,input_paths

FOLDER=HERE/"fixed-short"
def read(file):return json.loads(file.read_bytes())
def write(file,obj):
    stage=file.with_suffix(".pending")
    stage.write_bytes((json.dumps(obj,separators=(",",":"))+"\n").encode());stage.replace(file)

def dependencies():
    sys.path.insert(0,str(next(MS.glob("274-*"))))
    from face274 import dependencies
    return dependencies(MS)

def normalized(m,c,b):
    dims=list(dict.fromkeys((u^v).bit_length()-1 for p in (m,c) for u,v in zip(p,p[1:])))
    dims+=sorted(set(range(8))-set(dims))
    axes=[dims.index(a) for a in range(8)]
    tab=bytes(sum(1<<axes[i] for i in range(8) if v&1<<i) for v in range(256))
    shift=m[0];move=lambda p:list(bytes(v^shift for v in p).translate(tab))
    return move(m),move(c),move(b),axes,shift

def plan():
    cases={};counts=Counter();pinh=sha256()
    for name,path in input_paths():
        pinh.update(name.encode()+b"\0")
        for v in path:pinh.update(v.to_bytes(2,"little"))
        for axis,origin,left,m,right in charts(path):
            for side,c,b,mid in (("left",left,right,m[::-1]),("right",right,left,m)):
                if len(c)>4:continue
                M,C,B,axes,shift=normalized(mid,c,b)
                assert M[0]==B[0]==0 and C[0]==M[-1]
                key=sha256(bytes([len(M),*M,len(C),*C])).hexdigest()
                forbidden=set(M[1:-1])|set(C)|{v^(1<<j) for v in C for j in range(8)}
                assert not forbidden.intersection(B)
                r=cases.setdefault(key,dict(M=M,C=C,forbidden=sorted(forbidden),sources=[],maximum_starting_length=0))
                assert r["M"]==M and r["C"]==C and set(r["forbidden"])==forbidden
                r["sources"].append(dict(source=name,edges=len(path)-1,axis=axis,origin=origin,
                      short_side=side,free_port=shift,axes=axes,free_donor=B))
                r["maximum_starting_length"]=max(r["maximum_starting_length"],len(path)-1)
                counts[f"{len(path)-1}/{len(C)-1}"]+=1
    FOLDER.mkdir(exist_ok=True)
    out=dict(input_archive_sha256=pinh.hexdigest(),short_arm_maximum=3,charts=counts,cases=cases)
    write(FOLDER/"plan.json",out)
    print("Fixed-short charts",dict(counts),"distinct fixed charts",len(cases),flush=True)
    return out

def lift_free(row,record,b):
    M,C=row["M"],row["C"]
    oriented=b[::-1]+[256+u for u in M]+C
    axis,origin=record["axis"],record["origin"]
    dims=record["axes"];s=record["free_port"]
    ret=[]
    for v in oriented:
        p=s^sum(1<<i for i,a in enumerate(dims) if (v&255)&1<<a)
        ret.append(origin^(p&((1<<axis)-1))^((p>>axis)<<(axis+1))^(((v>>8)&1)<<axis))
    return ret[::-1] if record["short_side"]=="left" else ret

def choose(rows,opt):
    any_length=set(opt.source_edges)
    keys=[k for k,r in rows.items() if any(s["edges"] in any_length for s in r["sources"]) and
          len(r["C"])-1<=opt.max_short and (not opt.keys or any(k.startswith(prefix) for prefix in opt.keys))]
    return sorted(keys,key=lambda k:(-rows[k]["maximum_starting_length"],len(rows[k]["C"]),k))

def main():
    ap=ArgumentParser();ap.add_argument("action",choices=["plan","search"])
    ap.add_argument("--source-edges",type=int,nargs="+",default=[191]);ap.add_argument("--max-short",type=int,default=3)
    ap.add_argument("--target",type=int,default=192);ap.add_argument("--keys",nargs="+")
    ap.add_argument("--first",type=int,default=0);ap.add_argument("--count",type=int)
    ap.add_argument("--depth",type=int,default=0);ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--standard",action="store_true");opt=ap.parse_args()
    if opt.action=="plan":plan();return
    if (HERE/"candidate-192.json").exists():print("Existing 192 candidate; stopping.");return
    rows=read(FOLDER/"plan.json")["cases"];selected=choose(rows,opt)[opt.first:]
    if opt.count is not None:selected=selected[:opt.count]
    proofs=FOLDER/"proofs";proofs.mkdir(exist_ok=True)
    h=dependencies();h.search.base_model=h.search.base_model if opt.standard else h.deficit.model
    with TemporaryDirectory(prefix="q9-free-port278-") as td:
        tmp=Path(td);tools=None
        for k in selected:
            r=rows[k];m=len(r["M"])-1;t=len(r["C"])-1;n=opt.target-2-m-t
            if n>98:print(k[:10],"Q8 length ceiling",n,flush=True);continue
            if opt.target<=r["maximum_starting_length"]:continue
            dest=FOLDER/f"queries-{opt.target}";dest.mkdir(exist_ok=True);file=dest/(k+".json")
            ledger=read(file) if file.exists() else {}
            F=set(r["forbidden"]);stop=False
            def visit(prefix):
                nonlocal tools,stop
                if stop or set(prefix)&F:return
                tag=",".join(map(str,prefix));old=ledger.get(tag,{})
                if old.get("status") in ("witness","excluded"):return
                if len(prefix)<=opt.depth:
                    for v in h.legal_next(prefix):visit(prefix+[v])
                    return
                domains=h.translate_domains({k:[0,*sorted(F)]},prefix)
                if k not in domains:return
                forbidden=domains[k];h.rebuild.model=h.family_model([forbidden])
                if tools is None:tools=h.rebuild.masks.compilers(tmp)
                result=h.rebuild.solve(FOLDER,tmp,tools,forbidden,n-len(prefix)+1,[0],old.get("cycles",[]),[],opt.seconds)
                if not opt.standard:result["encoding"]="parity-deficit"
                if result["status"]=="witness":
                    b=prefix[:-1]+[v^prefix[-1] for v in result["path"]]
                    assert h.original_audit.path_edges(b,8)==n and not F&set(b)
                    result["free_arm"]=b
                    paths={}
                    for s in r["sources"]:
                        q=lift_free(r,s,b);assert h.original_audit.path_edges(q,9)==opt.target
                        paths[f"{s['source']}:{s['axis']}:{s['short_side']}"]=q
                    result["literal_joins"]=paths
                    if opt.target>=192:write(HERE/"candidate-192.json",dict(source="fixed-short",case=k,joins=paths))
                    stop=True
                ledger[tag]=result;write(file,ledger)
                print(k[:10],m,t,opt.target,n,tag,result["status"],flush=True)
            visit([0])
            if (HERE/"candidate-192.json").exists():return

if __name__=="__main__":main()
