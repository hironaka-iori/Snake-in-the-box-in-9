"""Check every way to leave a saturated Q8 donor inside a 192-edge Q9 path."""
from pathlib import Path
from itertools import combinations
import json, sys, random
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound

def word_path(word):
    a=[0]
    for c in word:a.append(a[-1]^1<<int(c))
    return a

def branches(a):
    assert len(set(a))==len(a) and all(((v^w).bit_count()==1)==(j+1==i) for i,v in enumerate(a) for j,w in enumerate(a[:i]))
    assert not any(v not in a and all((v^w).bit_count()!=1 for w in a[1:-1]) for v in range(256))
    tips={a[0],a[-1]}; assert a[0]==0
    for k in (1,2):
        for crossing in combinations(sorted(tips),k):
            low_ends=tips-set(crossing)
            for majority in (0,1):
                if any(v.bit_count()%2!=majority for v in low_ends):continue
                ends=[(2-len(low_ends))*int(c==majority) for c in (0,1)]
                delta=sum(1-2*(v.bit_count()%2) for v in a)-(1-2*majority)
                yield crossing,majority,ends,delta

def run():
    bank=Path("q8_catalogue_96_98.words").read_text().split();n=int(sys.argv[1])
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes);axes=axes[:n]
    for i in map(int,sys.argv[2:]):
        a=word_path(bank[i])
        for ports,majority,ends,delta in branches(a):
            const,scale,tables,cert=build(a,ports,a,ends,delta,axes)
            val=const+sum(table[0][2] for _,table in tables)
            assert val==integer_bound(cert,set(a),set(ports),ends,delta)
            print(json.dumps(dict(i=i,word=bank[i],ports=ports,majority=majority,upper_endpoint_counts=ends,upper_delta=delta,total_scaled=len(a)*scale+val,cert=cert),separators=(",",":")),flush=True)
if __name__=="__main__":run()
