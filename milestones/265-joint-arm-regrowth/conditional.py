"""Independent conditional traversal and canonical classification of constructed long snakes."""
from argparse import ArgumentParser
from hashlib import sha256
from tempfile import TemporaryDirectory
from pathlib import Path
import subprocess
from tails import HERE,MS,CSC,BANK,load,save,digest,checked,groups

def code(path):
    def directed(seq):
        order=[]
        out=[]
        for a,b in zip(seq,seq[1:]):
            dim=a^b
            if dim not in order:order.append(dim)
            out.append(order.index(dim))
        return bytes(out)
    return min(directed(path),directed(path[::-1]))

def main():
    parser=ArgumentParser()
    parser.add_argument("widths",nargs="+",type=int)
    parser.add_argument("--nodes",type=int,default=12000000)
    parser.add_argument("--min",dest="minimum",type=int,default=191)
    cfg=parser.parse_args()
    src=HERE/"ConditionalPairs.cs"; dest=HERE/("conditional-"+str(cfg.minimum)+".json")
    data=load(dest) if dest.exists() else dict(source_sha256=digest(src),bank_sha256=digest(BANK),widths={},shapes={})
    if data["source_sha256"]!=digest(src) or data["bank_sha256"]!=digest(BANK):raise ValueError("Changed inputs")
    catalogue=load(BANK)
    known={code(row["vertex_sequence"]):i for i,row in enumerate(catalogue)}
    known_segments={}
    for i,row in enumerate(catalogue):
        p=row["vertex_sequence"]
        for n in (190,191):
            for j in range(len(p)-n):known_segments.setdefault(code(p[j:j+n+1]),i)
    old=load(HERE/"tail-pairs.json")
    with TemporaryDirectory() as d:
        exe=Path(d)/"Conditional.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(src)],check=True,capture_output=True)
        for width in cfg.widths:
            area=data["widths"].setdefault(str(width),{})
            for key,base in groups(width).items():
                prior=area.get(key)
                if prior and (prior["status"]!="open" or prior["node_limit"]>=cfg.nodes):continue
                probes=old["widths"].get(str(width),{}).get(key,{}).get("trees",[])
                flip=bool(probes and probes[1]["nodes"]<probes[0]["nodes"])
                A,B=base["A"],base["B"]
                starts=(B,A) if flip else (A,B)
                raw=subprocess.run([str(exe),str(cfg.minimum),str(cfg.nodes)],text=True,capture_output=True,check=True,
                    input="".join(",".join(map(str,p))+"\n" for p in starts),timeout=210).stdout.splitlines()
                _,status,first,second,arms,cuts=raw[-1].split()
                witnesses=[]
                for line in raw[:-1]:
                    marker,u,v=line.split()
                    if marker!="P":raise ValueError("Unexpected native output")
                    x,y=(list(map(int,w.split(","))) for w in (u,v))
                    if flip:x,y=y,x
                    w=checked(x,y)
                    if w["edges"]<cfg.minimum or x[:width+1]!=A or y[:width+1]!=B:raise ValueError("Wrong completion")
                    word=code(w["joined"]);shape=sha256(word).hexdigest()
                    data["shapes"].setdefault(shape,dict(**w,bank_entry=known.get(word),bank_segment=known_segments.get(word)))
                    witnesses.append(dict(shape=shape,tail_A=x[width+1:],tail_B=y[width+1:]))
                if len({(tuple(w["tail_A"]),tuple(w["tail_B"])) for w in witnesses})!=len(witnesses):
                    raise ValueError("Duplicate labelled join")
                area[key]=dict(**base,status=status,flipped=flip,first_nodes=int(first),second_nodes=int(second),
                    qualifying_first_arms=int(arms),component_prunes=int(cuts),node_limit=cfg.nodes,witnesses=witnesses)
                save(dest,data)
                if status=="witness":print("192-edge witness",width,key,flush=True);return
            print(width,[(r["status"],len(r["witnesses"])) for r in area.values()],flush=True)

if __name__=="__main__":main()
