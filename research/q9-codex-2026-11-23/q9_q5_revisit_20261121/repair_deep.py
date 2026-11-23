from repair import *
un={v[0] for v in rows('repair.log') if v[3]=='UNKNOWN'}
for i,(r,q,f) in enumerate(constraints()):
 if i not in un:continue
 fi={v for v in q if v//32 not in f};al=fi|{v for v in range(512) if v//32 in f}
 st,p=second(fi,set(q),192,75000,allowed=al)
 print(json.dumps([i,r,sorted(f),st,p],separators=(',',':')),flush=True)
 if p:break
