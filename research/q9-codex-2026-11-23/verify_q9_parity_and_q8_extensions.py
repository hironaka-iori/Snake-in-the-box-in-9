"""Audit distinct parent/cut combinations, retries, path witnesses and placement counts."""
import gzip,json,math
from collections import Counter
from pathlib import Path
from verify_q9_center_avoidance import forms,verify

def rows(name):
    with open(name) as stream:return list(map(json.loads,stream))

def audit_cut(bank,weight,files):
    keys={(i,m,s) for i in range(len(bank)) for m in range(1,512) if m.bit_count()==weight for s in (0,1)}
    expected=keys;cases={}
    for name in files:
        seen=set()
        for i,m,s,st,w in rows(name):
            key=(i,m,s)
            assert key in expected and key not in seen and st in ("FOUND","UNKNOWN","UNSAT")
            seen.add(key)
            assert (w is not None)==(st=="FOUND")
            if w:
                verify(w);assert len(w)>=193
                assert {v for v in w if (v&m).bit_count()%2==s}=={v for v in bank[i] if (v&m).bit_count()%2==s}
            cases[key]=st
        assert seen==expected
        expected={k for k,v in cases.items() if v=="UNKNOWN"}
    return dict(cases=len(keys),outcomes=Counter(cases.values()),logs=files)

def main():
    bank={}
    for l in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,l.split()))
        if len(p)==192:
            verify(p);bank.setdefault(forms(p,191)[0],p)
    assert len(bank)==131
    bank=list(bank.values())
    cuts={}
    groups={9:["q9_cut_fullparity_atleast192.jsonl"],8:["q9_cut_edges_atleast192.jsonl"],
            7:["q9_cut_squares_atleast192.jsonl","q9_cut_squares_atleast_vertex.jsonl"],
            6:["q9_cut_eight_all_atleast192.jsonl","q9_cut_eight_all_deep_atleast192.jsonl"],
            5:["q9_cut_weight5_atleast192.jsonl","q9_cut_weight5_deep_atleast192.jsonl","q9_cut_weight5_last_atleast192.jsonl"],4:["q9_cut_weight4_atleast192.jsonl"],
            3:["q9_cut_weight3_atleast192.jsonl"],2:["q9_cut_weight2_atleast192.jsonl"],1:["q9_cut_weight1_atleast192.jsonl"]}
    for weight,files in groups.items():
        if not Path(files[0]).exists() or len(rows(files[0]))!=len(bank)*2*math.comb(9,weight):continue
        # Only merge a completed retry file.
        active=[files[0]]
        for name in files[1:]:
            n=sum(r[3]=="UNKNOWN" for r in rows(active[-1]))
            if not Path(name).exists() or len(rows(name))!=n:break
            active.append(name)
        cuts[weight]=audit_cut(bank,weight,active)
    sizes=Counter()
    known=set()
    for line in open("q8_joint_even_arms.txt"):
        p=[0]
        for d in line.strip():p.append(p[-1]^(1<<int(d)))
        verify(p);assert max(p)<256
        k=forms(p,len(p)-1)[0]
        if k not in known:sizes[len(k)]+=1;known.add(k)
    native=[]
    for r,label in [(2,"two"),(3,"three")]:
        for target,floor,suffix in [(192,96,"192_long"),(195,93,"195"),(196,93,"196")]:
            name=f"q8_{label}_external_{suffix}.log"
            path=Path(name)
            if not path.exists() or not path.stat().st_size:continue
            fields=path.read_text().split();assert fields[0]=="NO_JOIN"
            record={k:int(v) for k,v in zip(fields[1::2],fields[2::2])}
            pairs=sum(x*y if a<b else x*(x+1)//2 for a,x in sizes.items() for b,y in sizes.items()
                      if floor<=a<=b and a+b+1+r>=target)
            assert pairs==record["pairs"] and pairs*math.factorial(8)*256==record["placements"]
            native.append(dict(target=target,min_parent=floor,external=r,file=name,**record))
    control=json.load(open("q9_cut_cube_atleast_crosscheck.json"))
    counts=control["results"];assert sum(counts.values())==120
    assert counts["FOUND/FOUND"] and counts["UNSAT/UNSAT"]
    return dict(q9_parent_classes=len(bank),minimum_Q9_edges=192,parity_weights=cuts,
                Q8_classes=len(known),Q8_placements=native,independent_models=counts,
                above_threshold_controls=sum(1 for row in control["cases"] if row[4] and row[4]>row[3]),
                extra_vertex_controls={n:json.load(open(f"q8_{n}_external_controls.json"))
                                       for n in ("two","three")})

if __name__=="__main__":print(json.dumps(main(),indent=2))
