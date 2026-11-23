from pathlib import Path
from collections import Counter
import importlib.util
D=Path(__file__).resolve().parent;R=D.parent
spec=importlib.util.spec_from_file_location('block_model_under_test',R/'q9_shuffle_blocks/search.py')
solver=importlib.util.module_from_spec(spec);spec.loader.exec_module(solver)
def vertices(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<c)
    return p
def induced(p,d):
    return all(0<=v<1<<d for v in p) and len(set(p))==len(p) and all(((v^p[i]).bit_count()==1)==(j==i+1) for j,v in enumerate(p) for i in range(j))
def word(p):return [(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
def signature(w,groups,lens):
    m={a:i for i,g in enumerate(groups) for a in g};res=[];j=0
    for n in lens:
        res.append(tuple(sorted(m[x] for x in w[j:j+n])));j+=n
    assert j==len(w);return tuple(res)
def check(w,pairs,single,lengths,p):
    assert len(p)==len(w)+1 and p[0]==0 and induced(p,2*len(pairs)+1);g=[*pairs,(single,)]
    assert signature(w,g,lengths)==signature(word(p),g,lengths)
