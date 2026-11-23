from prepare import *
cases=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()));w=(R/'q9_gap_generations/prior191.words').read_text().split();seen=set()
for r in cases:
 i=r['r'];A=tuple(r['a']);B=sorted(set(range(9))-set(A))
 if (i,A) in seen:continue
 seen.add((i,A));p=path(w[i]);q=[32*lay(v,A)+lay(v,B) for v in p]
 print(i,len(q),*q)
