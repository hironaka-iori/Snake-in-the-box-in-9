import json,random
from collections import Counter
from prepare import D,R,bank,unpack,bits
rng=random.Random(413978)
for label in ('single','double'):
    originals=[json.loads(l) for l in (D/f'{label}.jsonl').read_text().splitlines()][::3]
    chosen=sorted(originals,key=lambda c:(c['conflicts'],rng.random()))[:120]
    out=[]
    for idx,c in enumerate(chosen):
        base=unpack(int(c['fixed'],16));don=unpack(int(c['protected'],16));host=bank[c['row']]
        source={i for i,v in enumerate(host) if v in base-don}
        for goal in (100,125):
            keep=set();order=list(source);rng.shuffle(order)
            for st in order:
                if len(keep)>=goal-len(don):break
                for j in range(st,st+rng.randrange(3,10)):
                    if j in source and len(keep)<goal-len(don):keep.add(j)
            if len(keep)<24:continue
            new_fixed=don|{host[i] for i in keep};assert new_fixed<=base and len(new_fixed)<=goal
            out.append({**c,'holes':len(source-keep),'fixed':hex(bits(new_fixed)),'remote':[]})
    (D/f'{label}wide.jsonl').write_text(''.join(json.dumps(c,separators=(',',':'))+'\n' for c in out))
