"""Independent standard-library checks of donors, positive lifts, and filtering."""
import json,random
from collections import Counter,defaultdict
from pathlib import Path
from itertools import combinations
from functools import lru_cache
D=Path(__file__).resolve().parent
def pts(file):
    for line in file.open():
        d,*p=map(int,line.split());assert d==10;yield p
def check_geometry(p,d,pairs=False):
    assert all(0<=x<1<<d for x in p) and len(set(p))==len(p)
    if pairs:
        for i,j in combinations(range(len(p)),2):
            assert ((p[i]^p[j]).bit_count()==1)==(j==i+1)
    else:
        time={x:i for i,x in enumerate(p)}
        for i,x in enumerate(p):
            assert sorted(time[x^1<<b] for b in range(d) if x^1<<b in time)==[j for j in (i-1,i+1) if 0<=j<len(p)]
def moves(p):return [(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
def defects_for_fold(w,a,b):
    x=0;p=[0]
    for y in w:
        x^=1<<(a if y==b else y);p.append(x)
    return sum(p[i]==p[j] or (j-i>1 and (p[i]^p[j]).bit_count()==1) for i,j in combinations(range(len(p)),2))
def partitions(dims):
    if not dims:yield [];return
    x,*other=dims
    for y in other:
        for m in partitions([z for z in other if z!=y]):yield [(x,y)]+m
def allmaps():
    for pairs in partitions(list(range(10))):
        for single in range(5):
            g=0;m=[None]*10
            for k,(x,y) in enumerate(pairs):
                if k==single:m[x]=m[y]=8
                else:m[x]=2*g;m[y]=2*g+1;g+=1
            yield m
def geom_filter(w):
    if any(a==b==4 for a,b in zip(w,w[1:])) or any((a==c==4) or a==b==c for a,b,c in zip(w,w[1:],w[2:])):return False
    f=[0]
    for g in w:f.append(f[-1]^(1<<g))
    vertices=defaultdict(set)
    for t,v in enumerate(f):vertices[v].add(t)
    if max(map(len,vertices.values()))>16:return False
    for a in range(32):
        for b in range(a+1,32):
            if (a^b).bit_count()!=1:continue
            L,R=vertices[a],vertices[b]
            related=[(x,y) for x in L for y in (x-1,x+1) if y in R]
            if a^b==16:
                if len(L)+len(R)-len(related)>16:return False
            else:
                used={x for e in related for x in e};comp=0
                for t in sorted(used):
                    # A connected component of the chronological contact graph
                    # starts at a time with no preceding contact edge.
                    if (t-1,t) not in related and (t,t-1) not in related:comp+=1
                if comp+(len(L-used)+1)//2+(len(R-used)+1)//2>8:return False
    return True
def main():
    rng=random.Random(114435);archive=D.parent/'q9_three_seam_folds/q10_12.txt'
    donors={};full=[]
    for file in (archive,D.parent/'q9_two_sheet_chart_20261121/near_573291.pts',D.parent/'q9_two_sheet_chart_20261121/extend_573291.pts',D/'controls.pts'):
        paths=list(pts(file));donors[file.name]=dict(rows=len(paths),lengths=dict(Counter(len(p)-1 for p in paths)))
        for p in paths:check_geometry(p,10)
        if file==archive:full=list(map(moves,paths))
    controls=list(pts(D/'controls.pts'));models=defaultdict(list)
    for name in ('positive_solves','independent_controls'):
        for line in (D/(name+'.jsonl')).open():
            r=json.loads(line);assert r['status']=='FOUND';models[r['j']].append(r['path'])
    compare=[]
    for i,p in enumerate(controls):
        w=moves(p);assert set(w)==set(range(10))
        costs=[defects_for_fold(w,a,b) for a,b in combinations(range(10),2)]
        assert min(costs)>0
        expected=[min(8,x)//2 for x in w];assert geom_filter(expected)
        for path in models[i]:
            check_geometry(path,9,True);axis=moves(path);assert [x//2 for x in axis]==expected and len(axis)==191
            compare.append(sum(x!=min(y,8) for x,y in zip(axis,w)))
    maps=list(allmaps());assert len(set(map(tuple,maps)))==len(maps)==4725
    direct={}
    for g in (192,195,196):
        dates={};tests=[]
        for row in range(12):
            for ix in rng.sample(range(4725),40):
                for st in rng.sample(range(380-g),4):tests.append((row,ix,st))
        wanted={(row,ix) for row,ix,st in tests}
        for line in (D/f'all{g}.logtmp').open():
            row,ix,mp,w,r=line.split();i,j=int(row),int(ix)
            if (i,j) not in wanted:continue
            assert mp==''.join(map(str,maps[j])) and w==''.join(str(maps[j][c]) for c in full[i])
            good=set()
            for seg in r.strip(',').split(','):
                a,b=map(int,seg.split('-'));good.update(range(a,b+1))
            dates[(i,j)]=good
        passed=0
        for row,ix,st in tests:
            val=geom_filter([maps[ix][x]//2 for x in full[row][st:st+g]])
            assert val==(st in dates.get((row,ix),set()));passed+=val
        direct[g]=dict(tests=len(tests),pass_filter=passed)
    seven={}
    for g in (192,195,196):
        def get(name):return {r['j']:r for r in map(json.loads,(D/(name+'.jsonl')).read_text().splitlines())}
        rows=get('priority'+str(g));second=get('priority_retry'+str(g));assert set(second)=={j for j in rows if rows[j]['status']=='UNKNOWN'}
        rows.update(second);assert len(rows)==len((D/f'priority{g}.tsv').read_text().splitlines());seven[g]=dict(Counter(z['status'] for z in rows.values()))
    assert len(models)==len(controls) and all(len(x)==2 for x in models.values())
    print(json.dumps(dict(donors=donors,controls=len(controls),rigid_folds_failed=45*len(controls),full_pair_verified_paths=len(compare),pair_tests_each=192*191//2,edits_from_raw_range=[min(compare),max(compare)],direct_filter_vs_sliding=direct,seven_offsets_final=seven),indent=2))
if __name__=='__main__':main()
