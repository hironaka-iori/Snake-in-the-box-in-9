from pathlib import Path
import sys,json,itertools,random,time,hashlib
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
import graph_solver as G

def exact(adj,domain,path):
 best=path[:]
 def go(p):
  nonlocal best
  if len(p)>len(best):best=p[:]
  for w in range(len(adj)):
   if w in p or not domain>>w&1 or not adj[p[-1]]>>w&1:continue
   if any(adj[w]>>v&1 for v in p[:-1]):continue
   go(p+[w])
 go(path);return best

def main():
 start=time.perf_counter();pairs=list(itertools.combinations(range(5),2));raw=0;leaf=0;search=0;cycles=0
 for mask in range(1<<len(pairs)):
  adj=[0]*5
  for i,(u,v) in enumerate(pairs):
   if mask>>i&1:adj[u]|=1<<v;adj[v]|=1<<u
  for h in range(5):
   R=G.component(adj,31,h);ex=len(exact(adj,R,[h]));bound,detail=G.block_bound(adj,R,h,with_parity=False,cycle_cap=True,details=True)
   assert ex<=bound,(mask,h,ex,bound,detail)
   assert ex<=G.leaf_bound(adj,R,h);raw+=1;leaf+=1;cycles+=any(x['cycle_blocks'] for x in detail['chains'])
 rng=random.Random(3102026)
 cases=[]
 for domain in range(1,256):
  for h in range(8):
   if domain>>h&1:cases.append((3,domain,[h]))
 for _ in range(250):
  domain=rng.randrange(1,1<<16);h=rng.choice(list(G.bits(domain)));p=[h];adj=G.cube(4)
  for j in range(rng.randrange(5)):
   opts=[v for v in range(16) if domain>>v&1 and v not in p and adj[p[-1]]>>v&1 and all(not adj[v]>>u&1 for u in p[:-1])]
   if not opts:break
   p.append(rng.choice(opts))
  cases.append((4,domain,p))
 for n,domain,p in cases:
  adj=G.cube(n);ex=len(exact(adj,domain,p));old=p[:-1];allowed={v for v in G.bits(domain) if v==p[-1] or (v not in p and all(not adj[v]>>u&1 for u in old))};R=sum(1<<v for v in allowed);R=G.component(adj,R,p[-1]);suffix=ex-len(p)+1
  assert G.block_bound(adj,R,p[-1])>=suffix
  assert G.leaf_bound(adj,R,p[-1])>=suffix
  for mode in ['reach','parity','leaf','block','separator']:
   for memo in [False,True]:
    for target in [ex-1,ex]:
     r=G.Search(n,target,prefix=p,domain=domain,mode=mode,memo=memo,node_limit=10000000,seconds=60).run()
     expected='SAT' if target==ex-1 else 'UNSAT_EXHAUSTIVE_PYTHON'
     assert r['status']==expected,(n,domain,p,mode,memo,target,ex,r)
     if r['witness']:
      w=r['witness'];assert w[:len(p)]==p and len(w)>=target+1 and all(domain>>v&1 for v in w)
      assert len(set(w))==len(w) and all(bool(adj[a]>>b&1)==(j==i+1) for i,a in enumerate(w) for j,b in enumerate(w) if j>i)
     search+=1
 out={'status':'PASS','source_sha256':hashlib.sha256((H/'graph_solver.py').read_bytes()).hexdigest(),'all_five_vertex_graph_root_cases':raw,'cycle_penalty_exercised_cases':cycles,'leaf_arbitrary_graph_cases':leaf,'cube_domain_prefix_cases':len(cases),'search_controls':search,'modes':5,'memo_both':True,'seconds':time.perf_counter()-start,'scope':'small exhaustive/random controls; general soundness rests on proofs; no Q9 bound'}
 (H/'implementation_independent_review.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
