"""Cover every inserted-step type for selected source/four-axis pairs."""
import sys,json,itertools
from search import encode,jobs,clean,path
L,count,salt=map(int,sys.argv[1:])
words,draws=jobs(L,salt,count);S=192-L
for i,(row,axes,_) in enumerate(draws):
    assert clean(path(words[row]));modes=[-1]+[d for d in range(9) if d not in axes]
    for extras in itertools.product(modes,repeat=S):
        st,c,w,loc=encode(words[row],axes,extras,10000)
        if st=='UNKNOWN':st,c,w,loc=encode(words[row],axes,extras,90000)
        print(json.dumps([i,row,axes,extras,st,c,loc,w],separators=(',',':')),flush=True)
        if w:sys.exit()
