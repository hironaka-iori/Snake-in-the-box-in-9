"""Independent bitset disjointness check and classification of four-cube layer orders."""
from collections import defaultdict, Counter
from itertools import permutations, product
from pathlib import Path
import json,sys

def points(w):
    p=[0]
    for d in w:p.append(p[-1]^(1<<int(d)))
    return p
def check(p):
    assert len(set(p))==len(p)
    for j,y in enumerate(p):
        assert all(((x^y).bit_count()==1)==(i+1==j) for i,x in enumerate(p[:j]))
def square(p):
    return len({x^p[0] for x in p})==4 and len({x^y for x in p for y in p})==4
def half(p):
    return square(p[:4]) and square(p[4:]) and {x^p[0] for x in p[:4]}=={x^p[4] for x in p[4:]}
def shape(p):
    w=[x^y for x,y in zip(p,p[1:])]
    def norm(w):
        table={}
        return tuple(table.setdefault(x,len(table)) for x in w)
    return min(norm(w),norm(reversed(w)))
def orders():
    all_shapes=set();cut=set();singles=set();single_count=0;counter=Counter()
    def grow(p):
        nonlocal single_count
        if len(p)==16:
            sig=shape(p);all_shapes.add(sig)
            if min(Counter(sig).values())==1:singles.add(sig);single_count+=1
            nice=half(p[:8]) and half(p[8:])
            counter[nice]+=1
            if nice:cut.add(sig)
            return
        for d in range(4):
            y=p[-1]^(1<<d)
            if y not in p:grow(p+[y])
    grow([0])
    return [sum(counter.values()),counter[True],len(all_shapes),len(cut),single_count,len(singles)]
def main():
    full='--include46' in sys.argv
    a=Path('q7_four_q5_46plus.words' if full else 'q7_q5_direct_47plus.words').read_text().split()
    b=Path('q7_q5_block_46plus.words' if full else 'q7_four_q5_47plus.words').read_text().split()
    assert len(a)==len(b)==len(set(a)) and set(a)==set(b)
    groups=defaultdict(list)
    for w in a:
        p=points(w);check(p);assert ''.join(t for t in w if t in '56')=='565'
        groups[len(p)].append(p)
    # A bit at position i means the i-th labelled arm avoids this column.
    allow={}
    for size,seq in groups.items():
        index=[bytearray((len(seq)+7)//8) for _ in range(128)]
        for i,p in enumerate(seq):
            for x in p[1:]:index[x][i//8]|=1<<(i%8)
        allow[size]=[~int.from_bytes(v,'little') for v in index]
    checks=Counter();compatible=Counter();lower=None
    for perm in permutations(range(5)):
        for u,v in [(5,6),(6,5)]:
            axes=perm+(u,v)
            image=[sum(((x>>k)&1)<<d for k,d in enumerate(axes)) for x in range(128)]
            for n,A in groups.items():
                for m,B in groups.items():
                    if n<m or n+m<(96 if full else 97):continue
                    ban=allow[m];full=(1<<len(B))-1
                    for p in A:
                        candidates=full
                        for x in p[1:]:
                            candidates &= ban[image[x]]
                            if not candidates:break
                        compatible[n+m]+=candidates.bit_count()
                    checks[n+m]+=len(A)*len(B)
    assert not sum(compatible.values())
    cpp={}
    for l in Path('q8_two_square_97plus.log').read_text().splitlines():
        t=l.split()
        if t[0]=='DONE':cpp[int(t[1])]=int(t[3])
    if full:
        cpp[96]=sum(int(l.split()[3]) for name in ('q8_two_square_witness96.log','q8_two_square_46_50.log') for l in Path(name).read_text().splitlines() if l.startswith('DONE 96 '))
        extra=json.loads(Path('q8_q5_last_gray_20261121/audit.json').read_text())
        witness=extra['witnesses']['high95.log']['path']
        check(witness);assert len(witness)==95
    assert cpp==dict(checks)
    print(json.dumps({'rooted_q7_counts':{k:len(v) for k,v in groups.items()},'relative_tests':dict(checks),
          'compatible':dict(compatible),'Q4_directed_total_square_cut_and_class_counts_then_single_axis_cut_directed_and_classes':orders()},indent=2))
if __name__=='__main__':main()
