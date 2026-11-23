import sys,json,collections,itertools
from functools import lru_cache
from pathlib import Path
from run import solve
D=Path(__file__).resolve().parent
def walk(word):
    p=[0]
    for d in map(int,word):p.append(p[-1]^(1<<d))
    return p
def valid(p):
    return len(set(p))==len(p) and all(0<=x<512 for x in p) and all(((a^b).bit_count()==1)==(i+1==j) for (i,a),(j,b) in itertools.combinations(enumerate(p),2))
def readmask(s):return {v for v in range(512) if int(s,16)>>v&1}
ref=(D.parent/'q9_gap_generations/prior191.words').read_text().splitlines()
rows=[walk(w) for w in ref]
def norm(s):
    def one(u):
        dic={};return bytes(dic.setdefault(x,len(dic)) for x in u)
    return min(one(s),one(s[::-1]))
@lru_cache(None)
def host_shapes(r,n):return {norm(ref[r][i:i+n]) for i in range(192-n)}
def reconstruct(r,z,a,b,s,e,m):
    assert z!=r and sorted(m)==list(range(9));P=rows[r];Q=rows[z];sign=1 if s<e else -1
    here=[P[a]]
    for j in range(s,e,sign):
        src=(Q[j]^Q[j+sign]).bit_length()-1;here.append(here[-1]^(1<<m[src]))
    assert here[-1]==P[b] and valid(here) and abs(s-e)-(b-a) in (2,4,6,8)
    assert norm(ref[z][min(s,e):max(s,e)]) not in host_shapes(r,abs(e-s))
    forbidden={v^d for v in here[1:-1] for d in [0]+[1<<k for k in range(9)]}
    return r,z,a,b,here,forbidden
lines=(D/'grafts.txt').read_text().splitlines()
@lru_cache(None)
def geo(i):
    _,r,z,a,b,s,e,m,c=lines[i].split();r,z,a,b,s,e,c=map(int,(r,z,a,b,s,e,c))
    ans=reconstruct(r,z,a,b,s,e,list(map(int,m)));P=rows[r]
    assert sum(v in ans[-1] for j,v in enumerate(P) if not a<=j<=b)==c
    return ans
def verify_witness(path,fixed,geoms):
    assert valid(path) and fixed<=set(path)
    for *_,route,forbid in geoms:
        i=path.index(route[0]);j=path.index(route[-1]);actual=path[min(i,j):max(i,j)+1]
        assert route==actual or route[::-1]==actual
def main():
    assert len(rows)==131 and all(valid(p) for p in rows)
    for i in range(len(lines)):geo(i)
    summary={};deep={(x[0],x[1]):x[2] for x in map(json.loads,(D/'retry.jsonl').read_text().splitlines())}
    for label,i,st,w,n in map(json.loads,(D/'final_case.jsonl').read_text().splitlines()):
        assert deep[label,i]=='UNKNOWN';deep[label,i]=st
    allfixed=set()
    for label in ('single','double','singlewide','doublewide'):
        cases=[json.loads(l) for l in (D/f'{label}.jsonl').read_text().splitlines()]
        statuses={};pair=collections.Counter();counts=collections.Counter();fixed_sizes=[];conf=[];hs=[]
        for backend in ('cadical','minicard'):
            fs=[f for f in ((D/f'{label}-{backend}.jsonl'),(D/f'{label}-{backend}-tail.jsonl')) if f.exists()]
            records={r[0]:r for f in fs for r in map(json.loads,f.read_text().splitlines())}
            assert len(records)==len(cases);statuses[backend]=records
        for i,c in enumerate(cases):
            r=c['row'];G=list(map(geo,c['grafts']));assert all(g[0]==r for g in G)
            protected=set.union(*(set(g[4]) for g in G));fixed=readmask(c['fixed']);assert protected==readmask(c['protected']) and protected<=fixed
            allfixed.add(c['fixed'])
            if len(G)==2:
                A,B=sorted(G,key=lambda x:x[2]);assert A[3]+7<B[2] and A[1]!=B[1]
                assert all((x^y).bit_count()>=2 for x in A[4] for y in B[4])
            outside={j:v for j,v in enumerate(rows[r]) if not any(g[2]<=j<=g[3] for g in G)}
            possible={j:v for j,v in outside.items() if all(v not in g[5] for g in G)}
            assert len(outside)-len(possible)==c['conflicts'] and fixed<=protected|set(possible.values())
            assert len(protected|set(possible.values()))-len(fixed)==c['holes']
            assert all(j in possible and possible[j] not in fixed for j in c['remote'])
            for name in statuses:
                _,n,st,w=statuses[name][i];assert n==len(fixed)
                if w:verify_witness(w,fixed,G);assert len(w)>=193
            x=statuses['cadical'][i][2];y=statuses['minicard'][i][2];pair[(x,y)]+=1
            s='FOUND' if 'FOUND' in (x,y) else 'UNSAT' if 'UNSAT' in (x,y) else deep.get((label,i),'UNKNOWN')
            counts[s]+=1;fixed_sizes.append(len(fixed));conf.append(c['conflicts']);hs.append(c['holes'])
        summary[label]=dict(cases=len(cases),outcomes=dict(counts),independent={','.join(k):v for k,v in pair.items()},fixed=[min(fixed_sizes),max(fixed_sizes)],conflicts=[min(conf),max(conf)],holes=[min(hs),max(hs)])
    controls=[json.loads((D/'control.jsonl').read_text().splitlines()[0]),json.loads((D/'double_control.json').read_text())]
    met=[]
    for c in controls:
        r=c['row'];G=[geo(c['ids'][0] if 'ids' in c else c['primary'])]
        if 'secondary' in c:
            z,a,b,s,e,m=c['secondary'];G.append(reconstruct(r,z,a,b,s,e,m));assert G[0][1]!=z
        don=set.union(*(set(g[4]) for g in G));fixed=readmask(c['fixed']);assert don==readmask(c['protected']) and don<=fixed
        w=c['witness'];verify_witness(w,fixed,G);assert len(w)==192
        hint=set(rows[r])|don;assert c['outside_hint']==len(set(w)-hint) and c['outside_hint']>0
        st,other=solve(fixed,hint,191,180000,'minicard');assert st=='FOUND';verify_witness(other,fixed,G)
        met.append(dict(donors=len(G),fixed=len(fixed),donor_vertices=len(don),exterior=len(fixed-don),outside_hint=len(set(w)-hint),second_length=len(other)-1))
    summary['distinct_anchor_sets']=len(allfixed);summary['controls']=met;summary['ranked_grafts_checked']=len(lines);print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
