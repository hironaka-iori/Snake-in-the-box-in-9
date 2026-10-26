"""Find a candidate cycle, then verify a lower bound by integer inequalities on every edge."""
from pathlib import Path
from fractions import Fraction
import ast,gzip,hashlib,json,subprocess,time
from model import ROOT,np
HERE=Path(__file__).resolve().parents[1]/'share-model'

def algorithms():
 ref='41797e3863e17be730f06e3a9c5df09bbc0d404d';path='milestones/10-window-aggregate/scripts/refine.py'
 raw=subprocess.check_output(['git','show',ref+':'+path],cwd=ROOT).decode().replace('\r\n','\n')
 tree=ast.parse(raw);nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['prune','howard']]
 code=ast.unparse(ast.Module(body=nodes,type_ignores=[]))
 code=code.replace('for _ in range(iters):','for iteration in range(iters):\n        if iteration % 5 == 0: print("Policy iteration",iteration,flush=True)')
 ns={'np':np};exec(compile(code,path,'exec'),ns)
 return ns,hashlib.sha256(raw.encode()).hexdigest()
def decode(n,k):
 out=[]
 for _ in range(k):out.append(n%6+1);n//=6
 return out[::-1]
def main():
 start=time.monotonic();meta=json.loads((HERE/'data/model.json').read_text());a=np.load(HERE/'build/graph.npz')
 ids=np.flatnonzero(~a['excluded']);U=a['U'][ids];V=a['V'][ids]
 W=336*a['count'][ids].astype(np.int64)+48*a['demand'][ids]+42*a['share'][ids]+a['share_lower'][ids]
 ns,sha=algorithms();keep=ns['prune'](meta['states'],U,V);pool=np.flatnonzero(keep)
 active=np.unique(np.concatenate([U[pool],V[pool]]));index=np.full(meta['states'],-1,dtype=np.int32);index[active]=np.arange(len(active))
 print('Cyclic graph:',len(active),'states;',len(pool),'edges',flush=True)
 mu,cycle=ns['howard'](len(active),index[U[pool]],index[V[pool]],W[pool],iters=300)
 ci=pool[np.array(cycle)];mean=Fraction(int(W[ci].sum()),len(ci));print('Candidate mean',mean,'scaled:',mean/336,'period',len(ci),flush=True)
 assert all(int(V[e])==int(U[ci[(j+1)%len(ci)]] ) for j,e in enumerate(ci))
 p,q=mean.numerator,mean.denominator;cost=q*W-p;pi=np.zeros(meta['states'],np.int64);verified=False
 for iteration in range(1000):
  new=pi.copy();np.minimum.at(new,V,pi[U]+cost)
  if np.array_equal(new,pi):verified=True;break
  pi=new
  if iteration%25==0:print('Integer potential iteration',iteration,'range',int(pi.max()-pi.min()),flush=True)
 if verified:
  assert np.all(p+pi[V]<=q*W+pi[U]);pi-=pi.min()
  encoded=pi.astype('<i8').tobytes();(HERE/'data/potential.i64.gz').write_bytes(gzip.compress(encoded,mtime=0))
  potential_sha=hashlib.sha256(encoded).hexdigest()
 else:potential_sha=None
 records=[]
 for e in ci:
  g=int(ids[e]);records.append(dict(state=int(U[e]),next_state=int(V[e]),directions=meta['extensions'][int(a['direction'][g])],counts=decode(int(a['count_code'][g]),7),weight=int(W[e]),demand=int(a['demand'][g]),share_event=int(a['share'][g]),share_lower=int(a['share_lower'][g])))
 out=dict(status='EXACT_FINITE_MODEL' if verified else 'CANDIDATE_ONLY',algorithm_source_sha256=sha,states=meta['states'],edges=len(U),cyclic_states=len(active),cyclic_edges=len(pool),integer_weight_mean=str(mean),normalized_charge_mean=str(mean/336),cycle=records,potential_verified=verified,potential_sha256=potential_sha,potential_range=int(pi.max()-pi.min()) if verified else None,potential_iterations=iteration+1,seconds=round(time.monotonic()-start,3),scope='Exact graph mean only if cycle and all-edge integer potential agree. No full-snake existence, no Lean graph-to-snake coverage proof, and no new global bound.')
 (HERE/'data/analysis.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='cycle'},flush=True)
if __name__=='__main__':main()
