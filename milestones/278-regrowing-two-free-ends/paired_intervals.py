"""Find pairs of mutually compatible tails for the remaining off-centre archive intervals."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from archive import HERE,input_paths,read,write
from overlap import evidence,occurrences,reduced,shape,transitions
from grow import independent_check

def main(opt):
    paths=dict(input_paths())
    tag="paired-%d-%d-192"%(opt.minimum,opt.length)
    plan="plan-"+tag+".json";out=tag+".json"
    if not (HERE/plan).exists():
        known=evidence(paths,out);scope={};counts=Counter()
        for label,p in paths.items():
            if len(p)-1<opt.minimum:continue
            word=transitions(p);hits=reduced(occurrences(word,known))
            for i in range(len(p)-opt.length):
                j=i+opt.length;counts["total"]+=1
                if any(i<=lo and hi<=j for lo,hi,*_ in hits):
                    counts["already_excluded"]+=1;continue
                canon=shape(word[i:j])
                key=sha256(canon).hexdigest()
                row=scope.setdefault(key,dict(source=label,offset=i,occurrences=0));row["occurrences"]+=1
        write(plan,dict(counts=counts,scope=scope))
    scope=read(plan)["scope"];old=read(out) if (HERE/out).exists() else {}
    # Prioritise the interval shared by most still-uncovered archive occurrences.
    tasks=sorted(scope,key=lambda k:(-scope[k]["occurrences"],k))
    tasks=[k for k in tasks if old.get(k,{}).get("status") not in {"excluded","witness"}]
    if opt.first:tasks=tasks[opt.first:]
    if opt.count is not None:tasks=tasks[:opt.count]
    if not tasks:print("All covered intervals already decided or no uncovered windows in scope",len(scope));return
    source=HERE/("TwoTailIndexed.cs" if opt.indexed else "TwoTailJoin.cs");h=sha256(source.read_bytes()).hexdigest()
    with TemporaryDirectory(prefix="q9-arm-pair-") as d:
        temp=Path(d);exe=temp/"pairs.exe"
        subprocess.run(["C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe","/nologo","/optimize+","/platform:x64","/out:"+str(exe),str(source)],check=True)
        for first in range(0,len(tasks),100):
            batch=tasks[first:first+100];cores={};lines=[]
            for k in batch:
                r=scope[k];i=r["offset"];core=paths[r["source"]][i:i+opt.length+1]
                independent_check(core)
                assert k==sha256(shape(transitions(core))).hexdigest()
                cores[k]=core;lines.append(k+"\t"+",".join(map(str,core)))
            job=subprocess.run([str(exe),"192",str(opt.nodes),str(opt.store),str(opt.pairs),str(opt.milliseconds)],
                input="\n".join(lines)+"\n",text=True,capture_output=True,check=True)
            output=set()
            for line in job.stdout.splitlines():
                k,status,l,r,le,re,mask,contact,ls,rs,np,reason,lh,rh,path=line.split("\t")[:15]
                result=dict(**scope[k],status=status.lower(),left_max=int(l),right_max=int(r),left_exact=le=="1",right_exact=re=="1",
                    mask_nodes=int(mask),contact_nodes=int(contact),left_stored=int(ls),right_stored=int(rs),
                    pairs=int(np),reason=reason,left_histogram=lh,right_histogram=rh,source_sha256=h,source_file=source.name,
                    limits=dict(nodes=opt.nodes,tails=opt.store,pairs=opt.pairs,milliseconds=opt.milliseconds))
                if opt.indexed:
                    result["index_work"],result["trie_work"]=map(int,line.split("\t")[15:])
                assert k in cores and k not in output and result["status"] in {"open","excluded","witness"}
                output.add(k);old[k]=result
                if status=="EXCLUDED":assert result["left_exact"] and result["right_exact"]
                if status=="WITNESS":
                    witness=list(map(int,path.split(",")))
                    independent_check(witness);assert len(witness)==193
                    assert any(witness[i:i+len(cores[k])] in (cores[k],cores[k][::-1]) for i in range(len(witness)-len(cores[k])+1))
                    result["path"]=witness;write(out,old);write("candidate-192.json",result);return
            assert output==set(batch),(len(output),len(batch),job.stderr[-500:])
            write(out,old)
            if first%200==0:print(first+len(batch),"/",len(tasks),Counter(x["status"] for x in old.values()),flush=True)
    print("Summary",len(old),"/",len(scope),Counter(x["status"] for x in old.values()),flush=True)
if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("length",type=int);ap.add_argument("--minimum",type=int,default=191)
    ap.add_argument("--nodes",type=int,default=180000);ap.add_argument("--store",type=int,default=5000)
    ap.add_argument("--pairs",type=int,default=1000000);ap.add_argument("--milliseconds",type=int,default=1200)
    ap.add_argument("--indexed",action="store_true");ap.add_argument("--first",type=int,default=0);ap.add_argument("--count",type=int)
    main(ap.parse_args())

