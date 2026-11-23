from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'seam_sat.py').read_text()
s=s.replace('def solve(a,b,sites','def solve(paths,sites').replace('ref=set(a+b)','ref=set(sum(paths,[]))').replace('enumerate([a,b])','enumerate(paths)').replace("if sorted(map(len,arms))!=sorted([len(a),len(b)]) or shape(arms) not in old:return 'F',arms","if shape(arms) not in old:return 'F',arms")
s=s[:s.index('def main():')]+'''def main():
    global old
    inp=Path(sys.argv[1]);target=int(sys.argv[2]);limit=int(sys.argv[3]);budget=int(sys.argv[4]);rng=random.Random(int(sys.argv[5]))
    pool=[parse(line) for line in inp.read_text().splitlines()]; old=set(map(lambda line:shape(parse(line)),(r/'ready.pts').read_text().splitlines())); counter=Counter()
    for rep in range(limit):
        paths=rng.choice(pool); ends=[(j,i,x) for j,p in enumerate(paths) for i,x in ((0,p[0]),(len(p)-1,p[-1]))]
        cand=sorted([((x^y).bit_count(),j,i,k,h,x,y) for j,i,x in ends for k,h,y in ends if j<k])
        dist,j,i,k,h,x,y=rng.choice(cand[:3]);sites=[(j,i),(k,h)]
        rad=rng.choice([4,5,6,7]);cross= (x^y)
        mids=[x^v for v in range(256) if not v&~cross and 0<(v.bit_count())<dist]
        hotspots=set(mids)|{x,y}
        for n,p in enumerate(paths):
            eligible=[(idx,z) for idx,z in enumerate(p) if min((z^m).bit_count() for m in hotspots)<=1]
            if n not in (j,k) and eligible:sites.append((n,rng.choice(eligible)[0]))
            if rep%3==0 and eligible:sites.append((n,rng.choice(eligible)[0]))
        if rep%2==0:
            l=rng.randrange(len(paths));sites.append((l,rng.choice((0,len(paths[l])-1))))
        st,p=solve(paths,sites,rad,target,(budget,18),[],rng);counter[st]+=1
        if p:old.add(shape(p));off=p[0][0];print(' '.join(' '.join(map(str,[len(a),*(z^off for z in a)])) for a in p),flush=True)
    print(dict(counter),file=sys.stderr)
if __name__=='__main__':main()
'''
(r/'triple_sat.py').write_text(s)

