import json
from functools import lru_cache
from pathlib import Path
from prepare import D,R,bank,words,check,unpack,bits,transform,canon,hostshapes
from run import solve
lines=(D/'grafts.txt').read_text().splitlines()
@lru_cache(None)
def donors(length):
    out={}
    for r,w in enumerate(words):
        for j in range(192-length):
            key=canon(w[j:j+length]);bucket=out.setdefault(key,[])
            if len(bucket)<10 and all(a[0]!=r for a in bucket):bucket.append((r,j))
    return out
def match(target,donor):
    for permword in (donor,donor[::-1]):
        mp={};claimed={}
        for x,y in zip(permword,target):
            if (x in mp and mp[x]!=y) or (y in claimed and claimed[y]!=x):break
            mp[x]=y;claimed[y]=x
        else:
            spare=sorted(set(range(9))-set(mp.values()));mp.update(zip(sorted(set(range(9))-set(mp)),spare))
            return [mp[i] for i in range(9)],permword!=donor
    return None
singles=[json.loads(l) for l in (D/'single.jsonl').read_text().splitlines()][::3];singles.sort(key=lambda c:c['conflicts'])
for c in singles:
    gid=c['grafts'][0];_,r,z,a,b,s,e,m,cost=lines[gid].split();r,z,a,b,s,e=map(int,(r,z,a,b,s,e));m=list(map(int,m))
    h=bank[r];w=[h[a]^transform(v^bank[z][s],m) for v in bank[z]];pos={v:j for j,v in enumerate(w)}
    first=unpack(int(c['protected'],16));outside=unpack(int(c['fixed'],16))-first;W=set(w)
    if len(W&outside)<85:continue
    for i in range(1,176):
        if h[i] not in pos:continue
        for j in range(i+12,min(i+56,191)):
            if h[j] not in pos or not(j+7<a or b+7<i):continue
            x,y=pos[h[i]],pos[h[j]];n=abs(x-y);gain=n-(j-i)
            if gain not in (2,4,6,8) or not (max(x,y)+1<min(s,e) or max(s,e)+1<min(x,y)):continue
            second=w[x:y+1] if x<y else w[y:x+1][::-1]
            tableword=[(u^v).bit_length()-1 for u,v in zip(second,second[1:])];key=canon(''.join(map(str,tableword)))
            if key in hostshapes(r,n):continue
            for z2,j2 in donors(n).get(key,[]):
                if z2 in (r,z):continue
                mp,rev=match(tableword,list(map(int,words[z2][j2:j2+n])));start=j2+n if rev else j2;end=j2 if rev else j2+n
                new=first|set(second)
                exterior={h[t] for t in range(192) if not(a<=t<=b or i<=t<=j)}&W
                outside=exterior-new;anchor=outside|new
                hint=set(h)|new
                if len(outside)<35 or len(W-hint)<2:continue
                st,out=solve(anchor,hint,191,55000,'cadical')
                if not out or not set(out)-hint:continue
                check(out);assert set(out)>=anchor
                print(json.dumps(dict(row=r,primary=gid,secondary=[z2,i,j,start,end,mp],protected=hex(bits(new)),fixed=hex(bits(anchor)),exterior=len(outside),fixed_count=len(anchor),outside_hint=len(set(out)-hint),witness=out),separators=(',',':')))
                raise SystemExit
print(json.dumps({'status':'no_control'}))
