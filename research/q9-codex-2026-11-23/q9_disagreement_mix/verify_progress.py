"""Check scope, counts and coordinates of the local colour experiments."""
from pathlib import Path
from math import comb
from collections import Counter
import json
from check import verify,canonical
D=Path(__file__).resolve().parent
def rows(name):
    return [list(map(int,l.split()[1:])) for l in (D/name).read_text().splitlines() if l.startswith('ROW')]
words=(D/'two_banks189.words').read_text().split()
assert len({canonical(w) for w in words})==len(words)==230
sides=set()
for w in words:
    p=verify(w)
    for c in (0,1):sides.add(tuple(sorted(v^c for v in p[c::2])))
got=[tuple(map(int,l.split()[2:])) for l in (D/'unique_sides.in').read_text().splitlines()]
assert len(got)==304 and set(got)==sides
out={}
for k,name in enumerate(['plus1.log','minus1_plus2.log','minus2_plus3.log','minus3_plus4.log']):
    data=rows(name)
    if k<=1:
        assert len(data)==460 and all(r[2]==comb(95,k)*comb(161,k+1) and r[-1]==0 for r in data)
        assert {(r[0],r[1]) for r in data}=={(i,c) for i in range(230) for c in (0,1)}
        full=sum(r[3] for r in data)
    else:
        assert len(data)==304 and [r[0] for r in data]==list(range(304))
        assert all(r[1]==comb(95,k) and r[-2:]==[0,0] for r in data)
        full=sum(r[-3] for r in data)
    out[k]=dict(rows=len(data),hamilton_tests=full,undecided=0,witnesses=0)
for inp,log,k in [('parity_control.in','parity_control.log',2),('three_control.in','three_control.log',3)]:
    tests=(D/inp).read_text().splitlines();records=(D/log).read_text().splitlines();assert len(tests)==10 and len(records)==20
    for i,line in enumerate(tests):
        s=set(map(int,line.split()[2:]));p=list(map(int,records[2*i].split()[1:]))
        assert records[2*i].startswith('FOUND ') and len(p)==191 and len(set(p))==191
        assert all(((v^u).bit_count()==1)==(i==j+1) for i,v in enumerate(p) for j,u in enumerate(p[:i]))
        assert len(s-set(p[1::2]))==k and len(set(p[1::2])-s)==k+1
        assert records[2*i+1].endswith(' 0 1')
for source,res in [('colour_union.log',0),('colour_plus4.log',4)]:
    data=[json.loads(l) for l in (D/source).read_text().splitlines()]
    ctr=Counter(r['status'] for l in data if 'pose' in l for r in l['results'])
    assert all(any(r['status']=='FOUND' for r in l['results']) for l in data if 'control' in l)
    out['outside_'+str(res)]=dict(ctr)
out['new_shapes']=len(words);out['distinct_sides']=len(sides)
out['minority_max_overlap']=91;out['positive_controls']=20
out['cadical_second_order']=json.loads((D/'sat_audit.json').read_text())
print(json.dumps(out,indent=2))
