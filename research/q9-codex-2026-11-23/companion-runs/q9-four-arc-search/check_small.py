from itertools import product
from pathlib import Path
import json
import subprocess
import tempfile
from collections import defaultdict
root=Path(__file__).resolve().parent
cycle=(0,1,3,7,15,14,12,8)
def valid(p):
    return len(p)==len(set(p)) and all(((v^u).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j,u in enumerate(p) if j>i)
def arcs(cycle):
    return {tuple(cycle[(i+k*d)%8] for k in range(n)) for i,d,n in product(range(8),[-1,1],range(1,8))}
def lengths(left,right):
    halves=defaultdict(set)
    for a,b in product(left,right):
        if (a[-1]^b[0]).bit_count()==1 and len(a)+len(b)<8 and valid(a+b):
            halves[len(a)+len(b)].add(a+b)
    answers=set()
    for h in range(2,8):
        for r in range(2,8):
            if any((x[-1]^y[0]).bit_count()==1 and valid(x+y) for x in halves[h] for y in halves[r]):
                answers.add((h,r))
    return answers
with tempfile.TemporaryDirectory() as tmp:
    exe=Path(tmp)/'tiny'
    source=(root/'search.cpp').read_text().replace('constexpr int N = 192;', 'constexpr int N = 8;')
    assert 'constexpr int N = 8;' in source
    subprocess.run(['clang++','-std=c++20','-O3','-x','c++','-','-o',exe],input=source,text=True,check=True)
    pos=neg=0
    for shift in [0,1,3,7,11,15,16,17,31]:
        expected=lengths(arcs(cycle),arcs(tuple(v^shift for v in cycle)))
        for h,r in product(range(2,8),repeat=2):
            out=subprocess.run([exe,str(h+r-1),str(h),'1','specific',str(shift),'1'],input=' '.join(map(str,cycle))+'\n',text=True,capture_output=True,check=True).stdout
            observed=out.startswith('FOUND')
            assert observed==((h,r) in expected),(shift,h,r,out)
            if observed: pos+=1
            else: neg+=1
    print(json.dumps(dict(cases=pos+neg,positive=pos,negative=neg)))
