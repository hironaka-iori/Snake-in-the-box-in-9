from bank import *
from itertools import permutations
from random import Random
import os,subprocess
rng=Random(3868);dim=4
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    return p
def valid(p):return len(set(p))==len(p) and all(((p[i]^p[j]).bit_count()==1)==(j==i+1) for j in range(len(p)) for i in range(j))
def c(w):return min(normalize(w),normalize(w[::-1]))
def shape(S):
    nb={x:[x^1<<k for k in range(dim) if x^1<<k in S] for x in S}
    e=[x for x in S if len(nb[x])==1]
    if len(e)!=2 or any(len(z)>2 for z in nb.values()):return
    p=[e[0]];prev=-1
    while True:
        nx=[v for v in nb[p[-1]] if v!=prev]
        if not nx:break
        prev=p[-1];p.append(nx[0])
    if len(p)==len(S):return c(''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:])))
def generate(w):
    yield w
    for i in range(dim):
        if valid(path(w+str(i))):yield from generate(w+str(i))
bank=sorted({c(w) for w in generate('') if len(w)>1})
images=[]
for w in bank:
    expected={x for u in range(1,16) for v in range(1,16) if (u&v).bit_count()%2==0 and (x:=shape({a^(u if (a&v).bit_count()%2 else 0) for a in path(w)}))}
    expected.add(w);res=subprocess.run([D/'transform','4'],input=w+'\n',text=True,capture_output=True,check=True)
    obs={z.split()[0] for z in res.stdout.splitlines()};assert obs==expected;images.append(len(obs))
for i in range(60):
    inp=rng.sample(bank,2);z=subprocess.run([D/'join_test','0','2','4'],input=''.join(w+' 0 0 0 1\n' for w in inp),env={**os.environ,'Q9_GL_MIN':'0'},capture_output=True,text=True,check=True)
    actual=int(z.stdout.splitlines()[-1].split()[-4]);best=0
    for a0 in inp:
     for a in (a0,a0[::-1]):
      A=path(a);A=[x^A[-1] for x in A]
      for b0 in inp:
       for b in (b0,b0[::-1]):
        for per in permutations(range(4)):
         B=path([per[int(c)] for c in b])
         for root in [0,1,2,4,8]:
          for j in range(1,len(B)):
           p=A+([root] if root else [])+[x^root for x in B[1:j+1]]
           if not valid(p):break
           best=max(best,len(p)-1)
    assert best==actual,(inp,actual,best)
print(json.dumps(dict(all_Q4_input_shapes=len(bank),image_counts=images,explicit_relative_placement_comparisons=60)))
