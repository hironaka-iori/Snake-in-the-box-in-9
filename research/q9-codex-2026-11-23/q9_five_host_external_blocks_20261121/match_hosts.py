from pathlib import Path
import json
D=Path(__file__).resolve().parent
def order(s):
    adj={v:[v^1<<k for k in range(8) if v^1<<k in s] for v in s}
    ends=[v for v in s if len(adj[v])==1];assert len(ends)==2
    path=[min(ends)];rem=s-set(path)
    while rem:
        v,=rem.intersection(adj[path[-1]]);rem.remove(v);path.append(v)
    return path
def mapping(source,target):
    ss=set(source);tt=set(target)
    lower=order({v for v in ss if v<256})
    for layer in (0,1):
        upper=order({v&255 for v in tt if v>>8==layer})
        for arm in (upper,upper[::-1]):
            ax={};ok=True
            for a,b,c,d in zip(lower,lower[1:],arm,arm[1:]):
                i=a^b;j=c^d
                if ax.setdefault(i,j)!=j:ok=False;break
            if not ok or len(ax)!=8 or len(set(ax.values()))!=8:continue
            lut=[0]
            for k in range(8):lut += [v^ax[1<<k] for v in lut]
            sh=lut[lower[0]]^arm[0]^(layer<<8)
            if {lut[v&255]^(v&256)^sh for v in ss}==tt:
                return {'perm':[ax[1<<k].bit_length()-1 for k in range(8)]+[8],'shift':sh}
    return None
def read(p):return [list(map(int,l.split())) for l in Path(p).read_text().splitlines()]
five=read(D/'seeds.in');nine=read('q8_all_191_positive.hosts')
for i,p in enumerate(five):print(i,[(j,iso) for j,q in enumerate(nine) if (iso:=mapping(p,q))])
print("raw autoiso rows",[[j for j,q in enumerate(nine[:i]) if mapping(p,q)] for i,p in enumerate(nine)])

