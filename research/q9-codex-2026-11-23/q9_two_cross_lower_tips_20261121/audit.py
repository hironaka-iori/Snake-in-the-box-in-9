import gzip,itertools,json,random,sys
from fractions import Fraction
from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent
R=D.parent
sys.path.insert(0,str(R))
from verify_q9_intact98_all_crossings import integer_bound
def pairwise(p):
    dups=[];chords=[];gaps=[]
    for j,y in enumerate(p):
        for i,x in enumerate(p[:j]):
            d=(x^y).bit_count()
            if d==0:dups.append((i,j))
            if d==1 and i+1<j:chords.append((i,j))
            if i+1==j and d!=1:gaps.append((i,j))
    return dups,chords,gaps
def q9(a,b):return a[::-1]+[v+256 for v in b]+[b[-1]]
def split(l):
    n,m,*v=map(int,l.split());assert n+m==len(v)
    return v[:n],v[n:]
def walk(w):
    z=[0]
    for c in w:z.append(z[-1]^(1<<int(c)))
    return z
def check_bridge(a,b):
    z=q9(a,b);assert not any(pairwise(z))
    assert a[0]==b[0] and len(set(z))==len(z)
    assert len(set(a)&set(b))==1 and min((u^b[-1]).bit_count() for u in a)>1
    return z
def main():
    ws=(R/'q8_catalogue_96_98.words').read_text().split();rows={}
    for f in ['repriced','diffuse8']:
        for l in (D/(f+'.jsonl')).read_text().splitlines():
            r=json.loads(l);key=(r['i'],r['x'])
            if key not in rows or Fraction(r['bound'],r['scale'])<Fraction(rows[key]['bound'],rows[key]['scale']):rows[key]=r
    assert len(rows)==2992
    sample=set(random.Random(192298).sample(sorted(rows),100));tot=Counter();closed=Counter()
    with (D/'old_catalogue_manifest.jsonl').open('w') as out:
        for key,r in sorted(rows.items()):
            i,packed=key;arm=walk(ws[i]);x=packed%256;s=packed//256;t=arm[-1] if s else arm[0];u=arm[0] if s else arm[-1]
            threshold=193+((u^x).bit_count()%2);tot[threshold]+=1;closed[threshold]+=int(r['bound']<threshold*r['scale'])
            if key in sample:
                L=set(arm)|{x};sgn=lambda z:1-2*(z.bit_count()%2);delta=sum(map(sgn,L))-(sgn(u)+sgn(x))//2
                c=json.load(gzip.open(D/r['cert'],'rt'));assert r['bound']==len(L)*c['scale']+integer_bound(c,L,{t,x},(0,0),delta)
            print(json.dumps(dict(r,threshold=threshold),separators=(',',':')),file=out)
    seeds=[split(l) for l in (D/'short_seeds.txt').read_text().splitlines()];h=Counter();best=[]
    for a,b in seeds:
        z=check_bridge(a,b);h[len(z)-1]+=1
        if len(z)>len(best):best=z
    assert len(seeds)==124 and len(best)==191
    near=[]
    for l in (D/'soft.log').read_text().splitlines():
        k=l.split()
        if k[0]!='NEAR':continue
        a,b=split(' '.join(k[5:]));z=q9(a,b);d,c,g=pairwise(z)
        cyc=z[0]==z[-1] and all((i,j) in [(0,len(z)-2),(1,len(z)-1)] for i,j in c) and d==[(0,len(z)-1)] and not g
        near.append(dict(score=int(k[2]),duplicate_pairs=d,chords=c,non_edges=g,induced_cycle_after_dropping_closing_duplicate=cyc))
    for f in ['short_repair','soft']:
        for l in (D/(f+'.log')).read_text().splitlines():
            if l.startswith('BEST '):
                c=l.split();v=check_bridge(*split(' '.join(c[4:])));assert len(v)==int(c[1])+1
    orth=[]
    for i,l in enumerate(gzip.open(R/'q9_port_followup_public191.txt.gz','rt')):
        p=list(map(int,l.split()))
        for axis in range(9):
            cuts=[j for j in range(1,len(p)) if (p[j]^p[j-1])==1<<axis]
            if len(cuts)==2:
                a,b=cuts;v=[a,b-a,len(p)-b]
                if v==[2,96,94] or v==[94,96,2]:
                    z=p[1:] if v[0]==2 else p[:-1];assert len(z)==191 and not any(pairwise(z));orth.append([i,axis,v])
    s=dict(old_root_cases=tot,strict_integer_excluded=closed,python_replays=100,short_seed_counts=h,known191_trims=orth,near=near,best_edges=len(best)-1,best_vertex_pairs=len(best)*(len(best)-1)//2,best_path=best,full95_bank=json.loads((D/'finite_bank.log').read_text()),finite95=(D/'short95_catalogue.log').read_text().splitlines()[-1],hard=(D/'short_repair.log').read_text().splitlines()[-1],soft=(D/'soft.log').read_text().splitlines()[-1],joint_tail=(D/'tail_pair.log').read_text().splitlines()[-1])
    for key,f in [("four_tails","four_tails.log"),("four_tails_control","four_control.log"),("finite_bank_control","short95_control.log")]:
        if (D/f).exists():s[key]=(D/f).read_text().splitlines()[-1]
    if (D/"old_catalogue_native.jsonl").exists():
        native=[json.loads(l) for l in (D/"old_catalogue_native.jsonl").read_text().splitlines()]
        assert len(native)==2992 and all(rows[r["i"],r["x"]]["bound"]==r["bound"] for r in native)
        s["native_replays"]=len(native)
    (D/'short_verified.json').write_text(json.dumps(s,indent=2)+'\n')
    print(tot,closed,len(orth),near)
if __name__=='__main__':main()
