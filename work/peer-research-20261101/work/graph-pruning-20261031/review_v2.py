from pathlib import Path
import sys,json,itertools,random,time,hashlib
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
import graph_solver as G
from review_implementation import exact

def check(adj,R,h):
 ex=len(exact(adj,R,[h]));bound,groups=G.claw_bound(adj,R,h,True);assert ex<=bound,(adj,R,h,ex,bound,groups)
 used=set();loss=0;claws=stars=0
 for group in groups:
  vs=set(group['vertices']);assert not used&vs;assert all(R>>v&1 for v in vs);used|=vs;loss+=group['loss']
  if group['kind']=='endpoint_star':
   assert vs=={h}|set(G.bits(adj[h]&R));assert group['loss']==max(0,len(vs)-2);stars+=1
  else:
   v=group['center'];assert v in vs and len(vs)==4 and all(adj[v]>>w&1 for w in vs-{v});assert group['loss']==1;claws+=1
 assert bound==R.bit_count()-loss
 return claws,stars,ex,bound

def main():
 start=time.perf_counter();arbitrary=cubecases=searches=claws=stars=strict=0;rng=random.Random(31020262)
 for n,masks in [(5,range(1024)),(6,[rng.randrange(1<<15) for _ in range(3000)])]:
  pairs=list(itertools.combinations(range(n),2))
  for mask in masks:
   adj=[0]*n
   for i,(u,v) in enumerate(pairs):
    if mask>>i&1:adj[u]|=1<<v;adj[v]|=1<<u
   for h in range(n):
    R=G.component(adj,(1<<n)-1,h);a,b,ex,bd=check(adj,R,h);arbitrary+=1;claws+=a;stars+=b;strict+=bd<R.bit_count()
 adj=G.cube(4)
 for domain in range(1,65536):
  h=(domain&-domain).bit_length()-1;R=G.component(adj,domain,h);a,b,ex,bd=check(adj,R,h);cubecases+=1;claws+=a;stars+=b;strict+=bd<R.bit_count()
 memo_hits=pruned=0
 for j in range(1500):
  n=3 if j<500 else 4;adj=G.cube(n);domain=rng.randrange(1,1<<(1<<n));p=[rng.choice(list(G.bits(domain)))]
  for _ in range(rng.randrange(5)):
   opts=[v for v in G.bits(domain) if v not in p and adj[p[-1]]>>v&1 and all(not adj[v]>>u&1 for u in p[:-1])]
   if not opts:break
   p.append(rng.choice(opts))
  ex=len(exact(adj,domain,p))
  for mode in ['claw','hybrid']:
   for memo in [False,True]:
    for target in [ex-1,ex]:
     r=G.Search(n,target,prefix=p,domain=domain,mode=mode,memo=memo,node_limit=10000000,seconds=60).run();expected='SAT' if target==ex-1 else 'UNSAT_EXHAUSTIVE_PYTHON';assert r['status']==expected,(n,domain,p,ex,target,mode,r)
     if r['witness']:
      w=r['witness'];assert w[:len(p)]==p and len(w)>=target+1 and len(w)==len(set(w)) and all(domain>>v&1 for v in w);assert all(bool(adj[a]>>b&1)==(jj==i+1) for i,a in enumerate(w) for jj,b in enumerate(w) if jj>i)
     searches+=1;memo_hits+=r['stats']['memo_hits'];pruned+=r['stats']['pruned_claw']
 out={'status':'PASS','source_sha256':hashlib.sha256((H/'graph_solver.py').read_bytes()).hexdigest(),'arbitrary_graph_root_cases':arbitrary,'Q4_all_domain_canonical_root_cases':cubecases,'packed_claws_checked':claws,'endpoint_stars_checked':stars,'strict_below_reach_cases':strict,'Search_control_runs':searches,'Search_memo_hits':memo_hits,'Search_claw_prunes':pruned,'seconds':time.perf_counter()-start,'scope':'independent direct recursion oracle; no Q9 numerical conclusion'}
 (H/'review_v2.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
