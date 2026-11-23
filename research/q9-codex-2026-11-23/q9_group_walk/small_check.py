from colors import lift
from itertools import product
from collections import Counter
import random
def direct(word,path):
    if not word:return True
    for d in range(3*word[0],3*word[0]+3):
        v=path[-1]^(1<<d)
        if v not in path and all((u^v).bit_count()!=1 for u in path[:-1]):
            if direct(word[1:],path+[v]):return True
    return False
rng=random.Random(615913); gs=[list(range(i,i+3)) for i in (0,3,6)]
results=Counter(); patterns=[w for n in range(7) for w in product(range(3),repeat=n)]
patterns.extend(tuple(rng.randrange(3) for _ in range(n)) for n in range(7,19) for _ in range(15))
for w in patterns:
    p=[0]
    for x in w:p.append(p[-1]^(1<<(3*x)))
    goal=direct(w,[0]);s,it,n,q=lift(p,gs,100000,rng)
    assert (s=='FOUND' and goal) or (s=='UNSAT' and not goal),(w,s,goal)
    results[s]+=1
print(len(patterns),dict(results))
