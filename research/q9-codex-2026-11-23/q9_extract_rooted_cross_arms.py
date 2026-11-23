from collections import Counter
from pathlib import Path
import json

def canonical(w):
    d={}
    return ''.join(str(d.setdefault(c,len(d))) for c in w)
def valid_arm(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return len(set(p))==len(p) and all((a^b).bit_count()!=1 for j,a in enumerate(p) for b in p[:max(0,j-1)])
def run():
    arms=set();splits=Counter()
    for file in ['q9_three_axis_191.in','q9_three_axis.in']:
        for w in Path(file).read_text().splitlines():
            for axis,count in Counter(w).items():
                if count!=1:continue
                i=w.index(axis);splits[len(w),min(i,len(w)-1-i),max(i,len(w)-1-i)]+=1
                for arm in [w[:i][::-1],w[i+1:]]:
                    while len(arm)>=90:
                        arm=canonical(arm)
                        if arm in arms:break
                        if valid_arm(arm):arms.add(arm)
                        arm=arm[:-1]
    Path('q9_rooted_cross_arms.words').write_text('\n'.join(sorted(arms,key=lambda s:(-len(s),s)))+'\n')
    print(json.dumps({'input_splits':{str(k):v for k,v in splits.items()},'valid_rooted_arm_classes_by_length':Counter(map(len,arms))}))
if __name__=='__main__':run()
