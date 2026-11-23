from collections import Counter
from pathlib import Path
import json
def canonical(w):
    def norm(w):
        axes={};return ''.join(axes.setdefault(c,str(len(axes))) for c in w)
    return min(norm(w),norm(w[::-1]))
def vertices(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def contacts(p):
    s=set(p);assert len(s)==len(p)
    return sum((x^1<<a) in s for x in s for a in range(9))//2-len(p)+1
seeds=Path("q9_gap_harvest_189.words").read_text().splitlines()
uniq={};count=Counter()
for w in seeds:
    p=vertices(w);assert contacts(p)==0
    load=Counter(y for x in p for y in (x^1<<a for a in range(9)));used=set(p)
    def visit(left,right,l,r,loss,phase):
        if len(l)+len(r)==3:
            word=canonical(l[::-1]+w+r);uniq[word]=loss;count[loss]+=1;return
        for rev in ([False] if phase else [True,False]):
            tip=left if rev else right
            for a in range(9):
                v=tip^1<<a;penalty=load[v]-1
                if v in used or loss+penalty>4:continue
                used.add(v)
                for b in range(9):load[v^1<<b]+=1
                if rev:visit(v,right,l+str(a),r,loss+penalty,False)
                else:visit(left,v,l,r+str(a),loss+penalty,True)
                for b in range(9):load[v^1<<b]-=1
                used.remove(v)
    visit(p[0],p[-1],"","",0,False)
half=[set(),set()];stats=Counter()
for word,loss in sorted(uniq.items(),key=lambda kv:(kv[1],kv[0])):
    p=vertices(word);assert len(p)==193 and contacts(p)==loss
    stats[loss]+=1
    for k in (0,1):half[k].add(tuple(sorted(p[k::2])))
for k,h in enumerate(half):
    with open(f"q9_new189_extended_side{97-k}.txt","w") as out:
        for s in sorted(h):print(*s,file=out)
with open("q9_new189_nearmisses.words","w") as out:
    for w,loss in sorted(uniq.items(),key=lambda kv:(kv[1],kv[0])):print(loss,w,file=out)
print(json.dumps(dict(distinct_near_paths=stats,raw_completions=count,parity_sets=list(map(len,half))),indent=2))
