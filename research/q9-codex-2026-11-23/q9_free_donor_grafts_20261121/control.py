from collections import defaultdict
import json,sys
from prepare import D,R,bank,words,check,unpack,bits,transform
from run import solve
lines=(D/'grafts.txt').read_text().splitlines()
def mapped(gid):
    _,r,z,a,b,s,e,m,c=lines[gid].split();r,z,a,b,s,e,c=map(int,(r,z,a,b,s,e,c));m=list(map(int,m));x=bank[r][a]^transform(bank[z][s],m)
    w=[x^transform(v,m) for v in bank[z]];assert w[s]==bank[r][a] and w[e]==bank[r][b];return w
def emit(label,forms):
    best=[]
    for c in forms:
        fixed=unpack(int(c['fixed'],16));don=unpack(int(c['protected'],16))
        for g in c['grafts']:
            W=mapped(g)
            if not don<=set(W):continue
            allowed=fixed&set(W);outside=(set(W)-set(bank[c['row']]))-don
            if len(outside)>=4 and len(allowed-don)>=20:
                best.append((len(allowed),-len(don),c,allowed,W))
    best.sort(key=lambda v:(-v[0],v[1]))
    for _,__,c,anchor,W in best[:20]:
        Dset=unpack(int(c['protected'],16));hint=set(bank[c['row']])|Dset
        for solver in ('cadical','minicard'):
            st,w=solve(anchor,hint,191,70000,solver)
            if w:
                check(w);assert anchor<=set(w) and len(w)>=192
                if set(w)-hint:
                    print(json.dumps(dict(label=label,ids=c['grafts'],row=c['row'],solver=solver,original_fixed=c['fixed'],fixed=hex(bits(anchor)),protected=c['protected'],fixed_count=len(anchor),exterior=len(anchor-Dset),outside_hint=len(set(w)-hint),witness=w),separators=(',',':')),flush=True);return
    print(json.dumps(dict(label=label,available=len(best),status='no_control')),flush=True)
for label in ('single','double'):
    emit(label,[json.loads(l) for l in (D/f'{label}.jsonl').read_text().splitlines()][::3])
