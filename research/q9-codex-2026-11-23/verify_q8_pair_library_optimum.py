"""Audit the scoped optimum for the paired Q8 path library."""
import collections
import json
import math
from pathlib import Path
from verify_q9_center_avoidance import forms,verify

def load():
    bank={}
    for seq in open("q8_joint_even_arms.txt"):
        p=[0]
        for step in seq.strip():p.append(p[-1]^(1<<int(step)))
        assert max(p)<256;verify(p);bank.setdefault(forms(p,len(p)-1)[0],p)
    sizes=collections.Counter(len(p)-1 for p in bank.values())
    assert sum(sizes.values())==1863
    results={}
    for target,floor in [(192,93),(195,96),(196,93)]:
        fields=Path(f"q8_multicross_bank{target}.log").read_text().split()
        assert fields[0]=="NO_JOIN"
        row={key:int(v) for key,v in zip(fields[1::2],fields[2::2])}
        need=sum(na*nb if a<b else na*(na+1)//2 for a,na in sizes.items() for b,nb in sizes.items()
                 if a<=b and a+b+1>=target)
        assert row["bank"]==sum(n for a,n in sizes.items() if a>=floor)
        assert row["pairs"]==need and row["placements"]==need*math.factorial(8)*256
        results[target]=row
    ctrl=json.load(open("q8_multicross_controls.json"))
    # The returned path uses one layer change. Verify that both projected arms
    # belong to this bank, independently of the measured runtime or solver logs.
    p=ctrl["q9_control_vertices"];verify(p);assert len(p)==192
    crosses=[i for i in range(191) if p[i]^p[i+1]==256]
    assert len(crosses)==1
    j=crosses[0]
    for factor in [p[:j+1],p[j+1:]]:
        assert forms(factor,len(factor)-1)[0] in bank
    found=Path("q8_multicross_bank191.log").read_text().split()
    assert found[0]=="FOUND";direct=list(map(int,found[3:]));verify(direct);assert len(direct)==192
    extra={}
    for target,floor,name in [(195,93,"extra195"),(196,93,"extra196"),(192,96,"extra192_long")]:
        fields=Path("q8_multicross_"+name+".log").read_text().split();assert fields[0]=="NO_JOIN"
        d={k:int(v) for k,v in zip(fields[1::2],fields[2::2])}
        need=sum(na*nb if a<b else na*(na+1)//2 for a,na in sizes.items() for b,nb in sizes.items()
                 if floor<=a<=b and a+b+2>=target)
        assert need==d["pairs"] and need*256*math.factorial(8)==d["placements"]
        extra[target]=dict(min_parent_edges=floor,**d)
    return dict(library_by_edges=sizes,shape_count=len(bank),search=results,
                independent_bank_witness=direct,bank_witness_crossings=sum(a^b==256 for a,b in zip(direct,direct[1:])),
                with_one_external_vertex=extra,extra_control=json.load(open("q8_extra_vertex_control.json")),
                attained_edges=len(p)-1,factor_lengths=[j,190-j],
                lower_witness=p,small_domain_checks=ctrl["independent_decisions"])
if __name__=="__main__":print(json.dumps(load(),indent=2))
