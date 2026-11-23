from pathlib import Path
from collections import Counter
import sys,json
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from verify_q8_catalogue_lifts import fit,decode,check
bank=Path('q8_catalogue_96_98.words').read_text().split()
seeds=[]
for row,w in enumerate(Path('q9_three_axis_191.in').read_text().split()):
    for c,n in Counter(w).items():
        if n!=1:continue
        a=int(c);t=w.index(c);p=decode(w)
        col=lambda x:(x>>(a+1)<<a)|(x&((1<<a)-1))
        low=[col(x) for x in p[:t+1]];high=[col(x) for x in p[t+1:]]
        coords=[fit(low,bank),fit(high,bank)]
        if not all(coords):continue
        path=low+[x+256 for x in high];check(path,9)
        host=coords[0]['placed_vertices']+[x+256 for x in coords[1]['placed_vertices']]
        assert set(path)<=set(host) and len(path)==192 and len(host)==194
        seeds.append(dict(row=row,path=path,host=host,layers=coords))
assert [s['row'] for s in seeds]==[27,32,57,96,129]
(D/'seeds.json').write_text(json.dumps(seeds))
(D/'seeds.in').write_text(''.join(' '.join(map(str,s['host']))+'\n' for s in seeds))

