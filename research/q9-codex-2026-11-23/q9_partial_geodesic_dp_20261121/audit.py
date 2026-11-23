from pathlib import Path
import json,collections,hashlib
D=Path(__file__).resolve().parent;R=D.parent
def txt(s):return (D/s).read_text().splitlines()
def nums(s):return [list(map(int,l.split())) for l in txt(s)]
def jsons(s):return list(map(json.loads,txt(s)))
def wc(p):return (p[0],*p[1:5],p[8])
def path(w):
 p=[0]
 for c in w:p.append(p[-1]^(1<<int(c)))
 return p
def valid(p):return len(p)==len(set(p)) and all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j,b in enumerate(p) if j>i)
bank=(R/'q9_gap_generations/prior191.words').read_text().split();P=list(map(path,bank));assert len(P)==131 and all(len(p)==192 and valid(p) for p in P)
def geometry(line,goal):
 row,d,t,a,j,L,R0,rem,size,*c=line;p=[x^t if x>>d&1 else x for x in P[row]]
 assert t and not(t>>d&1) and c==p[a:j+1] and all((x^y).bit_count()>1 for i,x in enumerate(c) for y in c[i+2:])
 assert L==(0 if not a else p[a]^p[a-1]) and R0==(0 if j+1==len(p) else p[j]^p[j+1])
 assert goal==rem+sum((x^y).bit_count() for x,y in zip(c,c[1:]))
 A=set(c)
 def tips(v,m):
  return [(x,(x^v).bit_count()) for x in range(512) if x==v or ((x^v)&~m==0 and x!=v^m and x not in A and all((x^z).bit_count()!=1 for z in A-{v}))]
 pairs=sum(1 for x,h in tips(c[0],L) for y,k in tips(c[-1],R0) if h+k==rem and (x^y).bit_count()>1)
 assert size==pairs>0
raw=nums('head.log')+nums('tail.log');assert raw==nums('replay.log') and raw==sorted(raw) and len(raw)==131
intr=nums('integral.log');assert intr==nums('intreplay.log') and len(intr)==131
orig=[list(map(int,l.split()[1:])) for l in (R/'q9_sheared_partial191.log').read_text().splitlines() if l.startswith('AT ')]
for n,m,w,t,*_ in orig:assert (m,w,t)==tuple(sum(z[k] for z in raw[:n]) for k in (1,2,3))
works={s:nums(s+'.work') for s in ('head','tail','integral')}
for ss,rr,logs in [(['head','tail'],'replay.work',raw),(['integral'],'intreplay.work',intr)]:
 recs=sum((works[s] for s in ss),[])
 assert sorted(map(wc,recs))==sorted(map(tuple,nums(rr)))
 for r in recs:geometry(r,192)
 for row,m,w,t,dp,hall,export,surv in logs:
  a=[r for r in recs if r[0]==row];assert m==9*255 and len(a)==export and sum(r[8] for r in a)==surv and t==dp+hall+surv
sc=[]
for s in works:
 k=jsons(s+'sat.log');assert len(k)==len(works[s]) and all(i==j and st=='UNSAT' and q is None for j,(i,st,c,q) in enumerate(k));sc.extend(k)
fixed=jsons('timeline.log')+jsons('inttimeline.log');assert {(s,i) for s,i,_,_ in fixed}=={(s,i) for s,l in works.items() for i,r in enumerate(l)}
counts=collections.Counter()
for s,i,st,q in fixed:
 row,d,t,a,j,L,R0,rem,n,*c=works[s][i];assert q is None
 k={l for l in range(max(0,L.bit_count()-1)+1) if 0<=rem-l<=max(0,R0.bit_count()-1)}
 assert set(map(int,st))==k
 counts.update(st.values())
assert set(counts)<=set(['UNSAT','PROP'])
proofs=jsons('proof.log');assert {(s,i) for s,i,*z in proofs}=={(s,i) for s,r in works.items() for i,_ in enumerate(r)}
proofset={q[2]:(q[3],q[4]) for q in proofs}
assert len(proofs)==len(sc) and all((D/'proofs'/(k+'.zz')).is_file() for k in proofset)
i,row,d,t,a,j,L,R0,rem,l,r,c,*wits=jsons('control.json')[0];expected=nums('control.work')[i];geometry(expected,31);assert expected[:8]==[row,d,t,a,j,L,R0,rem]
for w in wits:
 assert len(w)==32 and valid(w) and w[l]==c[0] and w[-1-r]==c[-1] and l*r>0
 indices=[w.index(x) for x in c];assert all(n-m==(u^v).bit_count() for m,n,u,v in zip(indices,indices[1:],c,c[1:]))
 assert (w[0]^c[0])&~L==0 and (w[-1]^c[-1])&~R0==0
def sums(rows):
 k=('maps','windows','trials','gap_dp','matching','sent_windows','sent_pairs')
 return dict(zip(k,[sum(col) for col in list(zip(*rows))[1:]]))
print(json.dumps(dict(words_sha256=hashlib.sha256((R/'q9_gap_generations/prior191.words').read_bytes()).hexdigest(),tail=sums(raw[100:]),partial=sums(raw),integral=sums(intr),position_results=counts,unsat_cnf_windows=len(proofs),distinct_cnf_sha256=len(proofset),checked_distinct_RUP_steps=sum(z[0] for z in proofset.values()),control=dict(vertices=32,partial_depths=[l,r],internal_stretches=sum((u^v).bit_count()>1 for u,v in zip(c,c[1:])))),indent=2))
