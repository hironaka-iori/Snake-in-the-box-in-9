"""Finish the independent first-segment traversal for the Casella matched-axis bound."""
from balanced import HERE,R270,ADJ,read,write,Path,TemporaryDirectory,subprocess,CSC,remove_axis,walk
from collections import defaultdict
def main():
    stem="balanced-Casella-A1-189"
    first=read(HERE/(stem+".json"));second=read(HERE/(stem+"-replay.json"))
    p=first["parent"];bit=1<<first["matched_axis"];goal=first["threshold"];cutoff=first["split"]
    assert p==second["parent"] and goal==91 and cutoff==45 and first["complete"]
    cut,=[i for i,(v,w) in enumerate(zip(p,p[1:])) if v^w==bit]
    f0={remove_axis(v,bit) for v in p[:cut+1]};f1={remove_axis(v,bit) for v in p[cut+1:]}
    ports=set(range(128))-f0-f1
    for port in ports:
        name="second/"+str(port)
        assert first["branches"][name]==second["branches"][name] and second["branches"][name][-1]
    receipt=HERE/"balanced-first-replay.json"
    result=read(receipt) if receipt.exists() else {"shards":{}}
    remaining=sorted((1<<i) for i in range(7) if 1<<i not in f0)
    with TemporaryDirectory() as folder:
        tmp=Path(folder);exe=tmp/"enumerate.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(R270/"PrimerPartners.cs")],capture_output=True,check=True)
        for x in remaining:
            if result["shards"].get(str(x),{}).get("closed"):continue
            dest=tmp/"paths.csv"
            data=",".join(map(str,[0,*sorted(f0-{0})]))+"\n0,"+str(x)+"\n"
            job=subprocess.run([str(exe),"array",str(cutoff),"900000000","75",str(dest)],input=data,text=True,capture_output=True,check=True)
            status,nodes,count,_,_=job.stdout.split()
            paths=[list(map(int,s.split(","))) for s in dest.read_text().splitlines()]
            assert len(paths)==int(count)
            for path in paths:
                assert path[:2]==[0,x] and len(path)>cutoff and set(path)&f0=={0}
                for i,u in enumerate(path):
                    assert {u^(1<<d) for d in range(7)}&set(path)==set(path[max(0,i-1):i]+path[i+1:i+2])
            result["shards"][str(x)]=dict(closed=status=="complete",nodes=int(nodes),paths=paths)
            write(receipt,result);print("First step",x,status,count,flush=True)
        if not all(result["shards"][str(x)]["closed"] for x in remaining):return
        pool=[p for r in result["shards"].values() for p in r["paths"]]
        assert len(pool)==first["segments"]["long_first"]
        grouped=defaultdict(list)
        for path in pool:
            if path[-1] in ports:grouped[path[-1]].append(path)
        names=set()
        for port,paths in grouped.items():
            common=set(paths[0][:-1])
            for path in paths[1:]:common.intersection_update(path[:-1])
            threshold=goal-1-max(len(x)-1 for x in paths)
            ok,right,_=walk(exe,tmp,f1|common,port,threshold,75,"array")
            name="first/"+str(port)
            assert ok and [len(paths),len(right),True]==first["branches"][name]
            for left in paths:
                assert not any(len(left)+len(r)-1>=goal and set(left[:-1]).isdisjoint(r) for r in right)
            names.add(name)
        assert names=={k for k in first["branches"] if k.startswith("first/")}
        assert first["histogram"]==second["histogram"]=={}
        result.update(complete=True,verified_target=189,first_segment_paths=len(pool),first_ports=len(grouped),
                      second_ports=len(ports),attained=read(HERE/"casella-rebuilt-188.json")["edges"])
        assert result["attained"]==188
        write(receipt,result)
    statement="At Casella's archived crossing, requiring the rebuilt arm to cross the same internal coordinate once gives an exact maximum of 188 edges. Two exhaustive traversals exclude 189 and all longer joins under that restriction."
    write(HERE/"balanced-conclusion.json",dict(paper=statement,short=statement,records=[stem+".json",stem+"-replay.json",receipt.name]))
    print(statement,flush=True)
if __name__=="__main__":main()
