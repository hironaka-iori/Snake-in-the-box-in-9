"""Align alternate intact Q8 middles to two projected tips of published Q9 paths."""
import itertools,random,sys
from pathlib import Path
from collections import defaultdict
def pts(word):
    p=[0]
    for d in word:p.append(p[-1]^(1<<int(d)))
    return p
def put(f,parts):print(*(x for s in parts for x in [len(s),*s]),file=f)
def collect():
    out=set()
    for src in ['/private/tmp/q9_191_published_bank20.pts','/private/tmp/q9_domain_all190_centers20.txt']:
        for line in open(src):
            p=list(map(int,line.split()))
            for a in range(9):
                cut=[i for i,(x,y) in enumerate(zip(p,p[1:])) if x^y==1<<a]
                if len(cut)!=2:continue
                i,j=cut;root=p[i+1]
                def strip(x):
                    t=x^root
                    return (t&((1<<a)-1))|((t>>(a+1))<<a)
                m=tuple(map(strip,p[i+1:j+1]));l=tuple(map(strip,p[:i][::-1]));r=tuple(map(strip,p[j+2:]))
                out.add((m,l,r))
    return sorted(out)
def main():
    rng=random.Random(2905);pool=collect();bucket=defaultdict(list)
    with open('q9_double_tip_known_seeds.pts','w') as f:
        for seed in pool:
            put(f,seed);bucket[seed[0][-1].bit_count()].append(seed)
    words=set()
    for f in ['q8_single_cross_complete_arms.txt','q8_four_q6_20261120/q6_fresha_20.words','q8_four_q6_20261120/q6_freshb_20.words','q8_four_q6_20261120/q6_freshc_20.words','/private/tmp/q9_q7out_new95a20.words']:
        words.update(w for w in Path(f).read_text().split() if 93<=len(w)<=96)
    words=sorted(words);rng.shuffle(words)
    with open('q9_double_tip_mapped_seeds.pts','w') as out:
        for n,w in enumerate(words[:int(sys.argv[1])]):
            m=pts(w);used=set(m);dest=[[a for a in range(8) if (m[-1]>>a&1)==b] for b in (0,1)]
            cand=bucket[m[-1].bit_count()]
            if not cand:continue
            best=None
            for j in range(160):
                s,l,r=rng.choice(cand);pa=[0]*8
                for b in (0,1):
                    rng.shuffle(dest[b]);src=[a for a in range(8) if (s[-1]>>a&1)==b]
                    for i,d in zip(src,dest[b]):pa[i]=1<<d
                images={0:0}
                def image(x):
                    old=images.get(x)
                    if old is not None:return old
                    z=pa[(x&-x).bit_length()-1]^image(x&(x-1));images[x]=z;return z
                arms=[]
                for t in [l,r]:
                    arm=[]
                    for x in t:
                        z=image(x)
                        if z in used:break
                        arm.append(z)
                    arms.append(arm)
                score=sum(map(len,arms))
                if best is None or score>best[0]:best=score,arms
            put(out,(m,*best[1]));out.flush()
    print('base',len(pool),'mapped',n+1)
if __name__=='__main__':main()

