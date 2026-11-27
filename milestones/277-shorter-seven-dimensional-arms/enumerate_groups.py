"""Enumerate all compatible Q7 partners of length at least 47 for the R272 short-arm groups."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import os
import subprocess
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
R272=MS/"272-forty-nine-edge-parents"
R270=MS/"270-optimal-seven-dimensional-arms"
sys.path.insert(0,str(R270))
from all_primers import read,points,wordof,ordered,unrooted,paircheck
from primer_census import CSC,write

MINIMUM=47

def groups():
    data=read(R272/"short-arm-groups.json")
    src={w for w in read(R272/"q7-single-crossings.json")["q7_shapes"] if len(w)==96}
    replay=read(R272/"q7-single-crossings-replay.json")
    assert src=={w for w in replay["q7_shapes"] if len(w)==96} and len(src)==570
    directed={ordered(bytes.fromhex(w)[::direction]).hex() for w in src for direction in (1,-1)}
    members=[w for g in data for w in g["members"]]
    assert len(data)==382 and len(members)==len(directed)==1140 and set(members)==directed
    for g in data:
        blocked=set.intersection(*(set(points(bytes.fromhex(w))[1:]) for w in g["members"]))
        assert blocked==set(g["common"]) and len(blocked)>=45
    return data

def finish(engine,i,g,partners,nodes,cuts,rows):
    file=HERE/(engine+"-groups.json")
    partners.sort()
    assert len(partners)==len(set(partners))
    parents=[(k,points(bytes.fromhex(k))) for k in g["members"]]
    actual=[]
    for code in partners:
        q=list(bytes.fromhex(code));qset=set(q[1:])
        paircheck(q,7)
        assert q[0]==0 and len(q)>MINIMUM and not qset.intersection(g["common"])
        for k,p in parents:
            if not qset.intersection(p):
                joined=p[::-1]+[128+x for x in q]
                paircheck(joined,8)
                actual.append(dict(root=k,partner=code,shape=unrooted(joined)))
    row=dict(nodes=nodes,cuts=cuts,relaxed_lengths=dict(Counter(len(s)//2-1 for s in partners)),
             paths_sha256=sha256(("\n".join(partners)+"\n").encode()).hexdigest(),compatible=actual)
    if engine=="mask":row["partners"]=partners
    else:
        primary=read(HERE/"mask-groups.json")[str(i)]
        assert partners==primary["partners"] and actual==primary["compatible"] and row["paths_sha256"]==primary["paths_sha256"]
    rows[str(i)]=row
    if len(rows)%10==0:
        write(file,rows)
        print(engine,len(rows),"groups",dict(Counter(len(r["shape"])//2 for v in rows.values() for r in v["compatible"])),flush=True)

def primary(tmp,targets,gs,rows):
    exe=tmp/"Prime.exe";out=tmp/"paths.csv"
    subprocess.run([str(CSC),"/nologo","/optimize+","/platform:x64","/out:"+str(exe),str(R270/"PrimerPartners.cs")],capture_output=True,check=True)
    baseline=read(R272/"short-arm-mask.json")
    for i in targets:
        g=gs[i]
        run=subprocess.run([str(exe),"mask",str(MINIMUM),"900000000","75",str(out)],
            input=",".join(map(str,[0]+g["common"]))+"\n0\n",text=True,capture_output=True,check=True)
        length,visits,n,parity,component=run.stdout.split()
        if length!="complete":raise RuntimeError("Incomplete group "+str(i))
        partners=[bytes(map(int,line.split(","))).hex() for line in out.read_text().splitlines()]
        assert len(partners)==int(n)
        if str(i) in baseline:
            assert sorted(x for x in partners if len(x)//2>=50)==baseline[str(i)]["partners"]
        finish("mask",i,g,partners,int(visits),dict(parity=int(parity),component=int(component)),rows)

def contact(tmp,targets,gs,rows):
    source=HERE/"ContactReplay.cpp"
    vcvars=Path(os.environ["ProgramFiles"])/"Microsoft Visual Studio/2022/Community/VC/Auxiliary/Build/vcvars64.bat"
    cmd=tmp/"build.cmd"
    cmd.write_text('@echo off\ncall "'+str(vcvars)+'" >nul\nif errorlevel 1 exit /b 1\ncl /nologo /O2 /EHsc /std:c++17 /Fe:Replay.exe "'+str(source)+'"\n',encoding="ascii")
    run=subprocess.run([os.environ["COMSPEC"],"/D","/C",str(cmd)],cwd=tmp,text=True,capture_output=True)
    if run.returncode:raise RuntimeError(run.stdout+run.stderr)
    req=tmp/"groups.in";req.write_text("".join(" ".join(map(str,[i,MINIMUM,len(gs[i]["common"]),*gs[i]["common"]]))+"\n" for i in targets),encoding="ascii")
    with req.open() as stream:
        with subprocess.Popen([str(tmp/"Replay.exe"),str(tmp/"capacities.bin")],cwd=tmp,stdin=stream,stdout=subprocess.PIPE,text=True) as process:
            paths=[];done=0
            for line in process.stdout:
                parts=line.split()
                if parts[0]=="P":paths.append(bytes(map(int,parts[1:])).hex())
                else:
                    assert parts[0]=="G"
                    i,n,hits,local,reach=map(int,parts[1:])
                    assert len(paths)==hits and i==targets[done]
                    finish("contacts",i,gs[i],paths,n,dict(local=local,reachable=reach),rows)
                    paths=[];done+=1
            assert process.wait()==0 and done==len(targets) and not paths
    from capacity import validate
    validate((tmp/"capacities.bin").read_bytes(),HERE/"q4-capacities.json")

def main():
    ap=ArgumentParser();ap.add_argument("engine",choices=["mask","contacts"]);ap.add_argument("--count",type=int,default=382)
    opt=ap.parse_args();gs=groups();file=HERE/(opt.engine+"-groups.json")
    rows=read(file) if file.exists() else {}
    targets=[i for i in range(len(gs)) if str(i) not in rows][:opt.count]
    if not targets:return
    with TemporaryDirectory(prefix="snake-r277-") as d:
        if opt.engine=="mask":primary(Path(d),targets,gs,rows)
        else:contact(Path(d),targets,gs,rows)
    write(file,rows)
    print("Completed",opt.engine,len(rows),flush=True)

if __name__=="__main__":main()
