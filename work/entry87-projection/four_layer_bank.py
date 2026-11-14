"""Exact four-layer compatibility search on Q7 path shapes extracted from verified sources."""
import argparse,json,subprocess
from collections import Counter
from itertools import combinations
from pathlib import Path
from projection_seeds190 import seeds
from punctured_lift import project
from solve import BANK,BANK_HASH,defects,save,sha256


def words(paths,minimum):
    bank={}
    for i,q in enumerate(paths):
        for a,b in combinations(range(9),2):
            parts=[];last=-1
            for v in q:
                layer=(v>>a&1)|((v>>b&1)<<1)
                if layer!=last:parts.append([]);last=layer
                parts[-1].append(v)
            for j,seg in enumerate(parts):
                if len(seg)<minimum:continue
                seq=[(v^w).bit_length()-1 for v,w in zip(seg,seg[1:])]
                def canon(s):
                    names={};return bytes(48+names.setdefault(c,len(names)) for c in s)
                word=min(canon(seq),canon(seq[::-1]))
                bank.setdefault(word,(i,a,b,j))
    return bank


def menus(bank,size):
    result={}
    for raw,origin in bank.items():
        if len(raw)+1<size:continue
        for j in range(len(raw)-size+2):
            sub=raw[j:j+size-1]
            for rev,s in enumerate((sub,sub[::-1])):
                labels={};key=bytes(48+labels.setdefault(b,len(labels)) for b in s)
                result.setdefault(key,(origin,j,rev))
    return result


def test(pathmenus,exe,maxnodes):
    stream=[]
    for menu in pathmenus:
        stream.extend([str(len(menu)).encode(),*menu.keys()])
    result=subprocess.run([str(exe),str(maxnodes)],input=b"\n".join(stream),capture_output=True,check=True).stdout.split()
    reached=int(result[1]);nodes=int(result[2])
    r=dict(status=result[0].decode(),placements=reached,nodes=nodes)
    if result[0]==b"FOUND":
        q=list(map(int,result[3:]))
        assert len(q)==sum(len(next(iter(menu)))+1 for menu in pathmenus) and not defects(q)
        r["vertices"]=q
    return r


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("sizes",nargs=4,type=int)
    p.add_argument("--extended",action="store_true");p.add_argument("--stats",action="store_true")
    p.add_argument("--nodes",type=int,default=250000000);p.add_argument("--exe",type=Path,default=Path("four-layer-bank.exe"))
    a=p.parse_args();raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    paths=[r["vertex_sequence"] for r in json.loads(raw)]
    if a.extended:paths+=list(seeds())
    bank=words(paths,min(a.sizes));menus4=[menus(bank,n) for n in a.sizes]
    report=dict(sources=len(paths),sizes=a.sizes,classes=[len(m) for m in menus4],
                longest=max(map(len,bank))+1,segments=len(bank))
    print(report,flush=True)
    if not a.stats and all(menus4):
        # At low sizes the independently decoded path tests the whole search.
        a0={b"01":None,b"10":None}
        r=test([a0]*4,a.exe.resolve(),1000000)
        assert r["status"]=="FOUND" and not defects(r["vertices"])
        report.update(test(menus4,a.exe.resolve(),a.nodes))
    save(Path(f"four-layer-bank-{len(paths)}-{'-'.join(map(str,a.sizes))}-{a.nodes}.json"),report)
