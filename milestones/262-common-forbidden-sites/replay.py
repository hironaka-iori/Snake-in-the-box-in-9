"""Independently replay mask transfer by branching on axis images and comparing projected counts."""
from itertools import permutations
from pathlib import Path
from tempfile import TemporaryDirectory
from masks import HERE,load,save,digest,groups,compilers,replay

def ranks(source,target,index):
    def project(vertices,axes):
        row=[0]*(9<<len(axes))
        for v in vertices:
            mask=sum(1<<i for i,a in enumerate(axes) if v&(1<<a))
            row[(v.bit_count()<<len(axes))|mask]+=1
        return row
    fixed=[project(source,tuple(range(i))) for i in range(9)]
    found=[]
    def extend(axes,left):
        # Permuting the assigned axes might reorder a projection; count each fibre separately.
        if any(a>b for a,b in zip(fixed[len(axes)],project(target,axes))): return
        if not left:
            found.append(index[axes])
            return
        for v in left: extend(axes+(v,),left-{v})
    extend((),set(range(8)))
    return sorted(found)

if __name__=="__main__":
    q=load(HERE/"transfer.json")
    g=load(HERE/"groups.json")
    if q["source_sha256"]!=digest(HERE/"groups.json"): raise ValueError("Group archive changed")
    index={order:i for i,order in enumerate(permutations(range(8)))}
    transferred={}
    with TemporaryDirectory() as d:
        tmp=Path(d)
        checker=compilers(tmp)[0]
        for key,row in g.items():
            replay(HERE,tmp,checker,row)
            if row["status"]!="excluded": continue
            F=set(row["blocked"])
            if F!=set.intersection(*groups()[int(key)].values()): raise ValueError("Incorrect common sites")
            for shape,p in q["reference_paths"].items():
                for e,root in enumerate((p[0],p[-1])):
                    P={v^root for v in p if v!=root}
                    if any(sum(x.bit_count()==w for x in F)>sum(x.bit_count()==w for x in P) for w in range(9)):
                        continue
                    valid=ranks(F,P,index)
                    if valid: transferred.setdefault(shape+":"+str(e),{})[key]=valid
    if transferred!=q["covered"]: raise ValueError("Independent permutation search disagrees")
    save(HERE/"replay.json",dict(transferred=len(transferred),rooted_cases=q["complete_roots"],
        inputs={f.name:digest(f) for f in [Path(__file__),HERE/"masks.py",HERE/"transfer.json",HERE/"groups.json"]}))
