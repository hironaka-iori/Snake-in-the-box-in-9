"""Fix only shared minority points, freeing all majority points and the visit order."""
from pathlib import Path
import json,random,sys
from itertools import chain
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R))
from q9_intact_bank_search import search,verify
def read(f):
    for i,l in enumerate(f.open()):
        vs=list(map(int,l.split()));n=len(vs)//2;yield i,vs[:n],vs[n:]
def main():
    outside,cap,trials=map(int,sys.argv[1:4]); rng=random.Random(17680)
    bank=list(read(Path(sys.argv[4]) if len(sys.argv)>4 else R/'q9_fresh189_multirewire_20261121/poses.dat'));rng.shuffle(bank)
    for idx,a,b in read(D/'controls.dat'):
        common=set(a)&set(b)
        result=search(a,191,cap,(),omit=set(a)-common,forbid=set(range(512))-(set(a)|set(b)))
        assert any(r['status']=='FOUND' and verify(r['vertices']) for r in result)
        print(json.dumps(dict(control=idx,results=result)),flush=True)
    jobs=0
    for idx,a,b in bank:
        for c in (0,1):
            first={v for v in a if v.bit_count()%2==c};second={v for v in b if v.bit_count()%2==c}
            shared=first&second;onlyA=sorted(first-second);onlyB=sorted(second-first)
            if not 63<=len(shared)<=85:continue
            other={v for v in range(512) if v.bit_count()%2!=c}
            pool=other|first|second
            # Splice material from each parent even if the rest is entirely rebuilt.
            pins=rng.sample(onlyA,3)+rng.sample(onlyB,3)
            forbidden=set() if outside else set(range(512))-pool
            result=search(a,192,cap,(),pins,False,1-c,set(a)-shared,forbidden,(pool,outside))
            print(json.dumps(dict(pose=idx,colour=c,shared=len(shared),pins=pins,results=result),separators=(',',':')),flush=True)
            jobs+=1
            if any(r['status']=='FOUND' for r in result) or jobs>=trials:return
if __name__=='__main__':main()
