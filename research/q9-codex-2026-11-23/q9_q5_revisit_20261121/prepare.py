from pathlib import Path
import json,itertools,random,collections
D=Path(__file__).resolve().parent;R=D.parent
def path(w):
 p=[0]
 for a in w:p.append(p[-1]^(1<<int(a)))
 return p
def lay(v,A):return sum((v>>a&1)<<k for k,a in enumerate(A))
def seq(p,A):
 return [t for t,_ in itertools.groupby(lay(v,A) for v in p)]
def norm(s):return min(tuple(s),tuple(s[::-1]))
def ports(p,A):
 return {tuple(sorted((v,w))) for v,w in zip(p,p[1:]) if lay(v,A)!=lay(w,A)}
def main():
 W=(R/'q9_gap_generations/prior191.words').read_text().split();P=[path(w) for w in W];S=list(map(set,P))
 rng=random.Random(219022);cases=[];seen=set();controls=[];meta=[]
 for i,w in enumerate(W):
  axes=list(itertools.combinations(range(9),4));rng.shuffle(axes);axes.sort(key=lambda A:sum(w.count(str(a)) for a in A))
  eligible=[A for A in axes if 20<=1+sum(w.count(str(a)) for a in A)<=25]
  meta.append([i,1+sum(w.count(str(a)) for a in axes[0]),len(eligible)])
  for A in eligible[:3]:
   s=seq(P[i],A);visits=collections.Counter(s);cols={v:lay(v,A) for v in range(512)}
   for j in range(len(W)):
    if j==i:continue
    changed=S[i]^S[j];layers=frozenset(cols[v] for v in changed)
    if len(layers)>8 or not changed or norm(s)==norm(seq(P[j],A)):continue
    n=len(S[i]-S[j]);port=len(ports(P[i],A)^ports(P[j],A))
    if n>=3 and port>=2:
     controls.append(dict(r=i,t=j,a=A,f=sorted(layers),n=n,port=port,k=len(s),jvis=len(seq(P[j],A))))
   for k in (3,4,5,6,8):
    pool=[]
    for _ in range(55):
     first=rng.choice(s);B={first}
     while len(B)<k:
      cand=[v for v in range(16) if v not in B]
      wts=[1+sum((v^(1<<b)) in B for b in range(4))*3+visits[v]*2 for v in cand]
      B.add(rng.choices(cand,wts)[0])
     count=sum(v in B for v in s);span=sum(cols[v] in B for v in P[i]);contacts=sum((v in B)!=(z in B) for v,z in zip(s,s[1:]))
     if contacts>=4 and any(visits[v]>=2 for v in B):pool.append((count,contacts,span,rng.random(),tuple(sorted(B))))
    for _,_,_,_,B in sorted(pool,reverse=True)[:2]+rng.sample(pool,min(2,len(pool))):
     key=(i,A,B)
     if key not in seen:cases.append(dict(r=i,a=A,f=B,k=len(s)));seen.add(key)
 def put(name,obj):(D/name).write_text(''.join(json.dumps(x,separators=(',',':'))+'\n' for x in obj))
 put('cases.jsonl',cases);put('templates.jsonl',meta)
 controls.sort(key=lambda c:(c['k']==c['jvis'],-c['port'],-c['n']))
 chosen=[];source=set();dest=set()
 for c in controls:
  if c['r'] in source or c['t'] in dest:continue
  chosen.append(c);source.add(c['r']);dest.add(c['t'])
  if len(chosen)==12:break
 put('controls.jsonl',chosen)
 print(len(cases),len({c['r'] for c in cases}),len({(c['r'],tuple(c['a'])) for c in cases}),len(controls),chosen[:2],collections.Counter(c['k'] for c in cases))
if __name__=='__main__':main()
