from itertools import groupby
from pathlib import Path
import sys
D=Path(__file__).resolve().parent
def rows(file):
    return [list(map(int,s.split())) for s in (D/file).read_text().splitlines()]
def put(name,ls):
    (D/name).write_text(' '.join(map(str,sorted(ls))))
mode=sys.argv[1]
if mode=='banks':
    (D/'both.words').write_bytes((D.parent/'q8_single_cross_complete_arms.txt').read_bytes()+(D.parent/'q8_catalogue_96_98.words').read_bytes())
elif mode=='high':
    w=rows('wide.paths'); longest=sorted((p[1],p[0]) for p in w if sum((x^y)==256 for x,y in zip(p[2:],p[3:]))==3)
    put('high.ids',set(range(8))|set(range(1249,1253))|{r for _,r in longest[-22:]})
    put('all.ids',range(len((D/'cases.dat').read_text().splitlines())))
elif mode=='deeper':
    w=rows('beam.paths');put('deeper.ids',set(range(2))|set(range(1249,1253))|{i for _,i in sorted((a[1],a[0]) for a in w)[-7:]})
elif mode=='upper':
    q=set()
    for name in ('wide','beam','beam_all','beam_deep','regrow'):
        for r in rows(name+'.paths'):
            p=r[2:];parts=[list(a) for _,a in groupby(p,key=lambda x:x>>8)]
            if len(parts)!=4:continue
            tail=parts[-1];w=''.join(str((a^b).bit_length()-1) for a,b in zip(tail,tail[1:]))
            if len(w)>=55:q.add(w)
    (D/'regrown_upper.words').write_text(''.join(w+'\n' for w in sorted(q)))
