"""Extract two freely shaped Q8 outer paths from a nine-dimensional control bank."""
from pathlib import Path
import argparse
import itertools
from two_free_tails_sat import valid

def canonical(outer1,outer2):
    labels={}
    for arm in (outer1,outer2):
        for x,y in zip(arm,arm[1:]):
            key=(x^y).bit_length()-1
            if key not in labels:labels[key]=len(labels)
    remain=set(range(8))-set(labels)
    for k in sorted(remain,key=lambda k:(-((outer1[0]^outer2[0])>>k&1),k)): labels[k]=len(labels)
    def convert(v):
        u=v^outer1[0]
        return sum((u>>h&1)<<j for h,j in labels.items())
    return tuple(map(convert,outer1)),tuple(map(convert,outer2))

def extract(paths):
    donors=set(); normalized=[]
    for path in paths:
        assert valid(path)
        n=len(path)-1
        motion=[(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
        for a in range(9):
            cut=[j for j,d in enumerate(motion) if d==a]
            if len(cut)!=2:continue
            p,q=cut
            if q-p-1 not in (94,95,96):continue
            start=path[p+1]
            def pr(v):
                u=v^start
                return (u&((1<<a)-1))|(u>>(a+1)<<a)
            def pr9(v):
                return pr(v)|((v^start)>>a&1)<<8
            arms=[tuple(map(pr,reversed(path[:p+1]))),tuple(map(pr,path[q+1:]))]
            assert arms[0][0]==0 and arms[1][0]==pr(path[q])
            for l,r in (arms,arms[::-1]):donors.add(canonical(l,r))
            mid=path[p+1:q+1];word=''.join(str((pr(x)^pr(y)).bit_length()-1) for x,y in zip(mid,mid[1:]))
            normalized.append((min(len(arms[0]),len(arms[1])),word,tuple(map(pr9,path))))
    return sorted(donors),max(normalized)

if __name__=='__main__':
    arg=argparse.ArgumentParser();arg.add_argument('--out',required=True);arg.add_argument('--positive',required=True);arg.add_argument('paths',nargs='+');opt=arg.parse_args()
    paths={tuple(map(int,line.split())) for f in opt.paths for line in Path(f).read_text().splitlines()}
    paths={p for p in paths if len(p)==192 and max(p)<512}
    donors,(score,word,full)=extract(paths)
    with open(opt.out,'w') as out:
        for l,r in donors:print(len(l),len(r),*l,*r,file=out)
    with open(opt.positive,'w') as out:print('FOUND',0,8,191,word,*full,file=out)
    print('input191',len(paths),'rooted_exteriors',len(donors),'control_shorter_outer_vertices',score)
