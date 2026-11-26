"""Look for 98-edge Q8 snakes with a single-crossing, 48-edge Q7 arm."""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from parents import HERE,R270,read,write,points,ordered,unrooted,paircheck
from primer_census import CSC

def group_cases():
    words=read(HERE/"q7-single-crossings.json")["q7_shapes"]
    remaining={}
    for w in words:
        if len(w)!=96:continue
        for s in (bytes.fromhex(w),bytes.fromhex(w)[::-1]):
            key=ordered(s).hex()
            p=points(bytes.fromhex(key))
            remaining[key]=sum(1<<x for x in p[1:])
    groups=[]
    while remaining:
        first=min(remaining)
        common=remaining.pop(first);members=[first]
        while remaining:
            m=max(remaining,key=lambda k:(remaining[k]&common).bit_count())
            intersection=common&remaining[m]
            if intersection.bit_count()<45:break
            members.append(m);remaining.pop(m);common=intersection
        groups.append(dict(common=[v for v in range(1,128) if (common>>v)&1],members=sorted(members)))
    return groups

def main():
    ap=ArgumentParser()
    ap.add_argument("mode",choices=["groups","mask","array"])
    ap.add_argument("--count",type=int,default=10000)
    a=ap.parse_args()
    filename=HERE/"short-arm-groups.json"
    if a.mode=="groups":
        groups=group_cases();write(filename,groups)
        print("Groups",len(groups),"rooted",sum(len(g["members"]) for g in groups));return
    groups=read(filename);file=HERE/("short-arm-"+a.mode+".json")
    rows=read(file) if file.exists() else {}
    targets=[i for i,g in enumerate(groups) if str(i) not in rows][:a.count]
    with TemporaryDirectory() as tmp:
        tmp=Path(tmp);exe=tmp/"Prime.exe";out=tmp/"paths.csv"
        subprocess.run([str(CSC),"/nologo","/optimize+","/platform:x64","/out:"+str(exe),str(R270/"PrimerPartners.cs")],capture_output=True,check=True)
        for i in targets:
            g=groups[i];common=set(g["common"]);members=g["members"]
            cmd=[str(exe),a.mode,"49","900000000","60",str(out)]
            run=subprocess.run(cmd,input=",".join(map(str,[0]+sorted(common)))+"\n0\n",text=True,capture_output=True,check=True)
            status,nodes,n,_,_=run.stdout.split()
            if status!="complete":raise RuntimeError("Open group "+str(i))
            relaxed=sorted(bytes(map(int,line.split(","))).hex() for line in out.read_text().splitlines())
            assert len(relaxed)==len(set(relaxed))==int(n)
            actual=[]
            for v in relaxed:
                q=list(bytes.fromhex(v));s=set(q[1:])
                assert q[0]==0 and not s&common
                paircheck(q,7)
                for m in members:
                    p=points(bytes.fromhex(m))
                    if not s.intersection(p):
                        j=p[::-1]+[128+x for x in q]
                        paircheck(j,8);actual.append(dict(root=m,partner=v,q8=unrooted(j)))
            row=dict(nodes=int(nodes),relaxed=len(relaxed),sha256=sha256(("\n".join(relaxed)+"\n").encode()).hexdigest(),actual=actual)
            if a.mode=="array":
                base=read(HERE/"short-arm-mask.json")[str(i)]
                assert relaxed==base["partners"] and actual==base["actual"]
            else:row["partners"]=relaxed
            rows[str(i)]=row
            if len(rows)%10==0 or actual or i==targets[-1]:
                write(file,rows);print(a.mode,len(rows),"/",len(groups),"shapes",len({r["q8"] for row in rows.values() for r in row["actual"]}),flush=True)
if __name__=="__main__":main()
