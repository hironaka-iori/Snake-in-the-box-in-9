import json
from pathlib import Path
root=Path(__file__).resolve().parent
def inspect(line):
    head,w,c,n,*raw=line.split()
    assert head=='STATE'
    raw=list(map(int,raw));masks=raw[:-1:2];ports=raw[1:-1:2]+[raw[-1]]
    z=0;g=[0]
    for d in w:z^=1<<int(d);g.append(z)
    assert len(set(g))==16
    p=[]
    for i,m in enumerate(masks):
        x=ports[i]
        while True:
            assert m>>x&1
            p.append(32*g[i]+x);m^=1<<x
            if not m:break
            ns=[x^(1<<d) for d in range(5) if m>>(x^(1<<d))&1]
            assert len(ns)==1
            x=ns[0]
        assert x==ports[i+1]
    assert len(set(p))==len(p)==int(n)
    assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    chords=sum((x^y).bit_count()==1 for i,x in enumerate(p) for y in p[i+2:])
    assert chords==int(c)
    return chords,len(p),w,p
out={}
for fn in ('nearbank.log','pairports.log'):
    rows=[inspect(l) for l in (root/fn).read_text().splitlines() if l.startswith('STATE ')]
    c,n,w,p=min(rows)
    out[fn]=dict(states=len(rows),min_chords=c,vertices=n,outer_word=w,closest_path=p)
out['searched_fixed_port_runs']={f:(root/f).read_text().splitlines()[-1] for f in ('ports193.log','tree193.log','true185.log','true187.log','true189.log','true193.log')}
(root/'near_summary.json').write_text(json.dumps(out,indent=2)+'\n')
