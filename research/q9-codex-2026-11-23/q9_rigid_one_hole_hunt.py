"""Open one hole in a record-producing Q8 donor before free Q9 occupancy repair."""
from q9_intact_bank_search import word_path,verify,search
from pathlib import Path
from itertools import chain
import random,sys,json

def trials(idx,p,arm):
    assert set(arm)<=set(p) and verify(p)
    occupied=set(p);donor=set(arm);n=0
    for tip in [p[0],p[-1]]:
        for d in range(9):
            extra=tip^1<<d
            if extra in occupied:continue
            chords={extra^1<<j for j in range(9)}&occupied-{tip}
            blocked=chords&donor
            if len(blocked)>1:continue
            pool=list(blocked) or sorted(donor,key=lambda v:(min((v^u).bit_count() for u in chords),v))[:7]
            for hole in pool:
                if tip==hole:continue
                kept=donor-{hole}
                if any((v^extra).bit_count()==1 and sum(v^1<<j in kept for j in range(9))==2 for v in kept):continue
                n+=1;yield hole,extra,chords,tip

def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    paths=json.loads(Path("q9_rigid_five_witnesses.json").read_text())
    pin_count,budget=map(int,sys.argv[1:3])
    tasks=[]
    for k,rec in paths.items():
        idx=int(k);p=rec["vertices"];a=word_path(bank[idx])
        for hole,extra,chords,tip in trials(idx,p,a):
            tasks.append((idx,p,a,hole,extra,chords,tip))
    random.Random(4822).shuffle(tasks)
    for ix,(i,p,a,hole,extra,chords,tip) in enumerate(tasks):
        banned=chords|{hole};old=set(p);hint=old-banned|{extra}
        solid=sorted(v for v in old-set(a) if v not in banned and all((v^b).bit_count()>2 for b in banned|{extra}))
        rng=random.Random(983+ix)
        pins=sorted({tip,extra}|set(rng.sample(solid,min(pin_count,len(solid)))))
        result=search(a,192,budget,hint,pins,False,omit=[hole])
        print(json.dumps(dict(i=i,hole=hole,extra=extra,tip=tip,extra_pins=len(pins),results=result)),flush=True)
        if any(z["status"]=="FOUND" for z in result):return
if __name__=="__main__":main()
