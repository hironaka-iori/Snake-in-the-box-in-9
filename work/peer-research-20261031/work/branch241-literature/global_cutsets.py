"""Endpoint-deficit cutset separators inspired by LIPP cut formulations.
No SAT cuts are emitted without a complete neighborhood/domain check.
"""
from itertools import combinations

def edges(S,n):return [(u,u^(1<<d)) for u in sorted(S) for d in range(n) if u<(u^(1<<d)) and u^(1<<d) in S]
def closed(U,n):return set(U)|{u^(1<<d) for u in U for d in range(n)}
def cut_value(S,U,n,endpoints=None,domain=None):
 S=set(S);U=set(U)
 if domain is not None and not closed(U,n)<=set(domain):raise ValueError('cut neighborhood incomplete: unknown outside edges cannot be set to zero')
 if any(not 0<=v<1<<n for v in S|U):raise ValueError('vertex outside cube')
 deg={v:sum(v^(1<<d) in S for d in range(n)) for v in S}
 if any(d>2 for d in deg.values()):raise ValueError('degree exceeds two')
 cross=sum((u in U)!=(v in U) for u,v in edges(S,n))
 deficit=sum((2-deg[v]) if endpoints is None else (v in endpoints) for v in S&U)
 return {'cross_edges':cross,'endpoint_deficit':deficit,'lhs':cross+deficit,'nonempty':bool(S&U),'violated':bool(S&U) and cross+deficit<2}
def acyclic(S,n):
 S=set(S);adj={v:[] for v in S}
 for u,v in edges(S,n):adj[u].append(v);adj[v].append(u)
 seen=set()
 def visit(v,parent):
  seen.add(v)
  for w in adj[v]:
   if w==parent:continue
   if w in seen or not visit(w,v):return False
  return True
 return all(v in seen or visit(v,None) for v in S)

def test():
 import json
 from pathlib import Path
 checked=0;forests=0
 for mask in range(256):
  S={v for v in range(8) if mask>>v&1}
  if any(sum(v^(1<<d) in S for d in range(3))>2 for v in S) or not acyclic(S,3):continue
  forests+=1
  for bits in range(256):
   U={v for v in range(8) if bits>>v&1};r=cut_value(S,U,3);assert not r['violated'];assert r['lhs']==2*(len(S&U)-len(edges(S&U,3)));checked+=1
 cycle={0,1,3,7,6,4};assert cut_value(cycle,cycle,3)['violated']
 # True Q2 path; omitting outside crossing edge gives a FALSE cut if not guarded.
 S={0,1,3};U={0,1};D={0,1};E={0,3};full=cut_value(S,U,2,E);assert full['lhs']==2
 truncated=cut_value(S&D,U,2,E);assert truncated['violated']
 try:cut_value(S&D,U,2,E,domain=D)
 except ValueError:guard=True
 else:raise AssertionError('missing boundary guard')
 r={'forest_sets_Q3':forests,'all_subset_cut_checks':checked,'actual_induced_cycle_rejected':True,'boundary_false_cut_example':{'global_path':[0,1,3],'U':sorted(U),'truncated_domain':sorted(D),'full_lhs':full['lhs'],'wrong_truncated_lhs':truncated['lhs'],'guard_rejected':guard},'status':'finite verification plus general proof in notes; no new numerical bound or Lean bridge'}
 Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
if __name__=='__main__':test()
