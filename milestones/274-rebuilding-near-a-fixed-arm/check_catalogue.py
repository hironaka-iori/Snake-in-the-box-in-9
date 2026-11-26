"""Compare full labelled Q8 output with a separate occupancy-set enumeration."""
from collections import Counter
from hashlib import sha256
from near import HERE,read,write,valid,shape,ArgumentParser
from replay_near import iter_buckets
if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("--source",default="common92");a=ap.parse_args()
    data=read(HERE/(a.source+"-paths.json"));seed=data["seed"]
    results={}; count=Counter();levels=data["levels"]; known_shapes={}
    for r in levels:
        results[r]={"digest":sha256(),"counts":Counter(),"buckets":0}
    for omitted,allpaths in iter_buckets(seed,max(map(int,levels)),data["minimum"],data["maximum"]):
        level=results[str(len(omitted))];level["buckets"]+=1
        tag=",".join(map(str,omitted))
        assert levels[str(len(omitted))]["nonempty"].get(tag,0)==len(allpaths)
        for p in sorted(map(bytes,allpaths)):
            valid(p,8)
            level["counts"][str(len(p)-1)]+=1
            s=shape(p)
            known_shapes[s]=min(known_shapes.get(s,len(omitted)),len(omitted))
            count[s]+=1
            level["digest"].update(bytes([len(omitted)])+bytes(omitted)+bytes([len(p)])+p)
    for r,isolate in results.items():
        isolate["digest"]=isolate["digest"].hexdigest()
        assert levels[r]["digest"]==isolate["digest"] and levels[r]["histogram"]==dict(isolate["counts"])
    assert set(known_shapes)==set(data["shapes"]) and all(known_shapes[s]==v["minimum_omissions"] and count[s]==v["placements"] for s,v in data["shapes"].items())
    write(HERE/(a.source+"-catalogue-replay.json"),dict(levels=results,shapes=len(count),checked_labelled=sum(count.values())))
    print(a.source,len(count),sum(count.values()),"verified",flush=True)
