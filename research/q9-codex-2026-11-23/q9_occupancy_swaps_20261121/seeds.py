from collections import Counter
from pathlib import Path
import json,random,sys
D=Path(__file__).resolve().parent;R=D.parent
sys.path.insert(0,str(R/'q9_internal_xor_20261121'))
from verify import vertices,quadratic,chords
rng=random.Random(47721)
N=[{v^1<<j for j in range(9)} for v in range(512)]
def topo(s):
    deg={v:len(N[v]&s) for v in s};rest=set(s);sizes=[]
    while rest:
        todo=[rest.pop()]
        for v in todo:
            for w in N[v]&rest:rest.remove(w);todo.append(w)
        sizes.append(len(todo))
    return len(sizes),sum(deg.values())//2-len(s)+len(sizes),max(deg.values())
refs=(R/'q9_reordered_segments_20261120/reference191.words').read_text().split()
controls=[]; extra=[]; standard=[]
for word in refs:
    p=vertices(word);s=set(p);assert len(p)==192 and not quadratic(p)
    # nearest admissible exterior, without supplying the search with the removed vertex.
    ext=sorted(set(range(512))-s,key=lambda v:(len(N[v]&s),v))
    candidates=[v for v in ext if len(N[v]&s)==0]
    if candidates:extra.append(s|{rng.choice(candidates)})
    else:extra.append(s|{rng.choice(ext[:5])})
    for pos in rng.sample(range(1,len(p)-1),12):
        v=p[pos];alts=[x for x in ext if (x^v).bit_count()==2 and len(N[x]&(s-{v}))<=2]
        if alts:
            modified=(s-{v})|{rng.choice(alts)}
            if topo(modified)!=(1,0,2):controls.append(modified);break
for f,limit,e in [(R/'q9_internal_xor_20261121/near192_chords2_outside_plainfiles.words',250,2),(R/'q9_moving_chord_first.words',120,1)]:
    ws=f.read_text().split()
    for w in rng.sample(ws,min(limit,len(ws))):
        p=vertices(w);assert len(p)==193 and len(chords(p))==e
        standard.append(set(p))
def write(name,seq):
    rng.shuffle(seq)
    uniq=list(dict.fromkeys(tuple(sorted(s)) for s in seq))
    (D/(name+'.sets')).write_text(''.join(' '.join(map(str,s))+'\n' for s in uniq))
    return {'distinct':len(uniq),'topology':dict(Counter(str(topo(set(s))) for s in uniq))}
print(json.dumps(dict(control=write('control',controls),target=write('target',standard+extra),extra=write('extra',extra)),indent=2))
