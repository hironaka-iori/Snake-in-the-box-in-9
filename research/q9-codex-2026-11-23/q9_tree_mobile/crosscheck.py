import collections,gzip,itertools,json,random,subprocess
from search import D,R,match,shade,M,solve,validate
paths=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')]
rng=random.Random(997112);rows=[]
for i in range(24):
 p=shade(paths[rng.randrange(len(paths))]);s=set(p[::2]);m=rng.choice(M);pl=match(s,m);rng.shuffle(pl);d=2+i%3
 for a,b in pl[:d]:s.remove(a);s.add(b)
 if i%2:
  x=rng.choice([v for v in range(512) if v.bit_count()%2==0 and v not in s and all(v not in q for q in pl[:10])]);s.add(x)
 pairs=[(b,a) for a,b in pl[:d]]+pl[d:8]
 sub=[s-{a for a,b in q}|{b for a,b in q} for j in range(d,len(pairs)+1) for q in itertools.combinations(pairs,j)]
 text=''.join(str(len(z))+' '+' '.join(map(str,sorted(z)))+'\n' for z in sub)
 res=subprocess.run([str(D/'graph_solver'),'--majority-sets'],input=text,text=True,capture_output=True,check=True)
 ans=res.stdout.splitlines();assert len(ans)==len(sub);stats=collections.Counter(z.split()[0] for z in ans)
 assert stats['UNKNOWN']==0
 for z in ans:
  if z.startswith('FOUND'):assert validate(list(map(int,z.split()[1:])))
 sat=solve(s,m,pairs,d,50000,0,0,None,150);assert (stats['FOUND']>0)==(sat['status']=='FOUND') and sat['status'] in ('FOUND','UNSAT')
 rows.append(dict(i=i,cardinality=len(s),enum=len(ans),native=dict(stats),sat=sat['status']))
(D/'crosscheck.json').write_text(json.dumps(rows,indent=2)+'\n')
print(len(rows),sum(r['enum'] for r in rows),collections.Counter(r['sat'] for r in rows))
