"""Combine bounds only for identical normalized rooted arms across reconstructed seed families."""
from collections import Counter,defaultdict
from hashlib import sha256
from near import HERE,read,write,valid

def main():
    joint={}; families={}; per_seed={}; shapes={}; refnames={}; omit_levels={}
    for f in sorted((HERE/"face274").glob("*/summary.json")):
        seed=f.parent.name; report=read(f);plan=read(f.parent/"plan.json")
        data=read(HERE/(seed+"-paths.json")); reference=read(HERE/(seed+"-structure.json"))
        assert report["source_sha256"]==sha256((HERE/(seed+"-paths.json")).read_bytes()).hexdigest()
        roots_for=set()
        for k,r in report["roots"].items():
            p=plan["roots"][k]["normalized"];valid(p,8)
            assert sha256(bytes(p)).hexdigest()==k
            entry=joint.setdefault(k,dict(normalized=p,shape=r["shape"],minimum=0,maximum=197,evidence={}))
            assert entry["normalized"]==p and entry["shape"]==r["shape"]
            entry["minimum"]=max(entry["minimum"],r["minimum"])
            entry["maximum"]=min(entry["maximum"],r["maximum"])
            entry["evidence"][seed]=dict(lower=r["minimum"],upper=r["maximum"])
            assert entry["minimum"]<=entry["maximum"]
            roots_for.add(k)
        per_seed[seed]=roots_for;shapes[seed]=set(data["shapes"]);refnames[seed]=reference["source_join_edges"]
        omit_levels[seed]={k:r["minimum_omissions"] for k,r in report["roots"].items()}
        families[seed]=dict(seed_edges=reference["seed_edges"],original_join=reference["source_join_edges"],
            omission_levels=len(data["levels"]),shapes=len(data["shapes"]),roots=len(roots_for),
            labelled={r:l["histogram"] for r,l in data["levels"].items()},
            outside_earlier_q8_intervals=reference["outside_prior_intervals"])
    def stat(seeds):
        keys=set().union(*(per_seed[s] for s in seeds))
        return dict(seeds=sorted(seeds),shapes=len(set().union(*(shapes[s] for s in seeds))),
                    distinct_roots=len(keys),excluded_at_192=sum(joint[k]["maximum"]<192 for k in keys),
                    lower=max((joint[k]["minimum"] for k in keys),default=None),
                    upper=max((joint[k]["maximum"] for k in keys),default=None),
                    unrestricted_arm_lower=max([refnames[s] for s in seeds]+[joint[k]["minimum"] for k in keys]),
                    unrestricted_arm_upper=max([191]+[joint[k]["maximum"] for k in keys]),
                    open_roots=sorted(k for k in keys if joint[k]["maximum"]>=192 and joint[k]["minimum"]<192))
    for s in families:families[s]["rooted_bounds"]=stat([s])
    groups={label:stat(seedset) for label,seedset in dict(all=set(families),record={s for s in families if s.startswith("record")}).items() if seedset}
    budgets={}
    for label,g in groups.items():
        budgets[label]={}
        for level in range(3):
            keys={k for s in g["seeds"] for k,r in omit_levels[s].items() if r<=level}
            budgets[label][str(level)]=dict(shapes=len({joint[k]["shape"] for k in keys}),roots=len(keys),
                    excluded_192=sum(joint[k]["maximum"]<192 for k in keys),
                    attained_191=sum(joint[k]["minimum"]>=191 for k in keys),
                    lower=max([refnames[s] for s in g["seeds"]]+[joint[k]["minimum"] for k in keys]),
                    upper=max([191]+[joint[k]["maximum"] for k in keys]))
    result=dict(families=families,groups=groups,budgets=budgets,roots=joint)
    write(HERE/"results.json",result)
    for label,g in groups.items():print(label,{k:v for k,v in g.items() if k!="open_roots"},flush=True)
if __name__=="__main__":main()
