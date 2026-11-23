"""Independently verify arm banks, placements, residual connectivity, and witnesses."""
from pathlib import Path
from collections import deque
import json

root=Path(__file__).resolve().parent
bank=(root.parent/'q8_catalogue_96_98.words').read_text().split()
def canon(w):
    m={};return ''.join(m.setdefault(k,chr(65+len(m))) for k in w)
def shape(p):
    return canon([(a^b).bit_length()-1 for a,b in zip(p,p[1:])])
def valid(p,d=9):
    assert all(0<=x<1<<d for x in p) and len(set(p))==len(p)
    for j,x in enumerate(p):
        for i in range(j):assert ((p[i]^x).bit_count()==1)==(i+1==j)
def pts(w):
    p=[0]
    for c in w:p.append(p[-1]^(1<<(ord(c)-65)))
    return p
def words_at(n):
    return {canon(v) for w in bank for i in range(len(w)-n+1) for v in (w[i:i+n],w[i:i+n][::-1])}
sets={}
for n in [31,32,49,50,95,96,97,98]:
    sets[n]=words_at(n)
    assert sets[n]==set((root/f'q8_{n}.words').read_text().split())
first=[pts(w) for w in (root/'q8_98.words').read_text().split()]
for p in first:valid(p,8)
out={'source_count':len(bank),'oriented_arm_counts':{k:len(v) for k,v in sets.items()},'placements':{},'examples':{}}
for n,expected in [(49,34),(50,24)]:
    connected=0;count=0;seen=set()
    for line in (root/f'placements{n}.log').read_text().splitlines():
        s=line.split()
        if s[0]!='PLACE':continue
        row,*b=map(int,s[1:]);a=first[row];valid(b);assert shape(b) in sets[n]
        assert (row,tuple(b)) not in seen;seen.add((row,tuple(b)))
        assert all((x^y).bit_count()>1 for j,x in enumerate(a) for k,y in enumerate(b) if j or k)
        assert a[0]!=b[0]
        # Delete closed neighborhoods of all nontip arm vertices. Endpoints can always be used.
        forbidden={u for v in a[1:]+b[1:] for u in [v,*[v^(1<<k) for k in range(9)]]}
        allowed=set(range(512))-forbidden|{a[0],b[0]}
        q=deque([a[0]]);found={a[0]}
        while q:
            v=q.popleft()
            for k in range(9):
                u=v^(1<<k)
                if u in allowed and u not in found:found.add(u);q.append(u)
        connected+=b[0] in found;count+=1
    assert count==expected and (connected>0)==(n==49)
    out['placements'][n]=dict(enumerated=count,connectable=connected)
for n,method in [(31,'cross_arms'),(49,'floating')]:
    s=(root/f'q8_98_{method}_{n}.log').read_text().splitlines()[-1].split();assert s[0]=='FOUND'
    path=list(map(int,s[5:] if method=='cross_arms' else s[3:]));valid(path);assert len(path)-1==int(s[2])
    assert shape(path[:99]) in sets[98] and shape(path[-n-1:]) in sets[n]
    out['examples'][method]=dict(secondary_edges=n,total_edges=len(path)-1,connector_edges=len(path)-1-98-n,vertices=path)
for n,expect in [(31,5),(32,0)]:
    lines=(root/('yes31.log' if n==31 else 'no32.log')).read_text().splitlines()
    assert sum(int(line.split()[-1]) for line in lines)==expect
print(json.dumps(out,indent=2))
