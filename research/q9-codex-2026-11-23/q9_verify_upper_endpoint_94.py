"""Independent enumeration by contracting the entire compulsory lower path to a marked edge."""
from itertools import combinations,accumulate
from operator import xor
from pathlib import Path
from collections import Counter
import json
from q9_classify_record_donor_windows import canonical
from verify_q9_intact98_all_crossings import integer_bound
def main():
    D=Path("q9_upper_endpoint_94");saved=json.loads((D/"audit.json").read_text());poss=set();nc=Counter()
    source=Path("q8_single_cross_complete_arms.txt").read_text().split()+Path("q8_catalogue_96_98.words").read_text().split()
    for length in (94,95):
        words={canonical(w[j:j+length]) for w in source for j in range(len(w)-length+1)}
        assert len(words)==saved["source_counts"][str(length)]
        for w in words:
            a=list(accumulate([1<<int(d) for d in w],xor,initial=0));F=set(a)
            forbidden={v^1<<d for v in a[1:-1] for d in range(8)}
            extra=sorted(set(range(256))-F-forbidden);tips=[a[0],a[-1]]
            U=tips+extra;adj=[sum(1<<j for j,y in enumerate(U) if (x^y).bit_count()==1) for x in U]
            # The two distinguished vertices are joined by the contracted compulsory path.
            adj[0]|=2;adj[1]|=1
            for mask in range(1<<len(extra)):
                S=(mask<<2)|3
                degs=[(ns&S).bit_count() for ns in adj]
                if any(degs[j] not in (1,2) for j in range(len(U)) if S>>j&1):continue
                remain=S;parts=0;ok=True
                while remain:
                    bit=remain&-remain;forced=bit;front=bit
                    while front:
                        b=front&-front;front^=b
                        new=adj[b.bit_length()-1]&S&~forced;forced|=new;front|=new
                    remain^=forced;parts+=1
                    true_size=forced.bit_count()+((length-1) if forced&1 else 0)
                    if true_size<3 or sum(degs[j]==1 for j in range(len(U)) if forced>>j&1)!=2:ok=False;break
                if ok and parts>=2:
                    e=tuple(x for j,x in enumerate(extra) if mask>>j&1)
                    ports=tuple(sorted(U[j] for j in range(len(U)) if S>>j&1 and degs[j]==1))
                    poss.add((w,e,ports));nc[length,parts]+=1
    cells=saved["cells"];assert len(cells)==3*len(poss)
    expected={(w,e,p,k) for w,e,p in poss for k in (0,1,2)};bounds=[]
    for row in cells:
        w=row["word"];e=tuple(row["extra"]);p=tuple(row["ports"]);ends=row["ends"];expected.remove((w,e,p,ends[0]))
        low=set(accumulate([1<<int(d) for d in w],xor,initial=0))|set(e)
        delta=sum((-1)**x.bit_count() for x in low)-(ends[0]-ends[1])//2
        r=json.loads(Path(row["certificate"]).read_text());c=r["cert"]
        n=integer_bound(c,low,set(p),ends,delta)+len(low)*c["scale"];assert n==r["total_scaled"]
        limit=n//c["scale"]-1;limit-=(limit-ends[0])%2
        assert limit==row["upper_edges"];bounds.append(limit)
    assert not expected
    print(json.dumps(dict(source_counts=saved["source_counts"],valid_multi_component_counts={str(k):v for k,v in nc.items()},verified=len(cells),max_edges=max(bounds),histogram=dict(Counter(bounds)))))
if __name__=="__main__":main()
