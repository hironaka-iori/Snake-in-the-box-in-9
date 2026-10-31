"""Compact forbidden-edge-history lift. States are indexed by trie prefix endpoint.
Every nonempty AC prefix ends at one fixed original graph vertex, so the lift
needs only one extra graph state per nonterminal prefix, not |V| times |AC|.
"""
from collections import deque,defaultdict,Counter
from pathlib import Path
import json,time,hashlib
from probe_critical_cycles import scc,shortest_cycle,realize
H=Path(__file__).resolve().parent

class AC:
 def __init__(self,patterns):
  self.next=[{}];self.fail=[0];self.bad=[False];self.prefix=[()]
  for pattern in patterns:
   q=0
   for token in pattern:
    if token not in self.next[q]:
     self.next[q][token]=len(self.next);self.next.append({});self.fail.append(0);self.bad.append(False);self.prefix.append(self.prefix[q]+(token,))
    q=self.next[q][token]
   self.bad[q]=True
  todo=deque(self.next[0].values())
  while todo:
   q=todo.popleft();self.bad[q]|=self.bad[self.fail[q]]
   for t,v in self.next[q].items():
    f=self.fail[q]
    while f and t not in self.next[f]:f=self.fail[f]
    self.fail[v]=self.next[f].get(t,0);todo.append(v)
  self.cache={}
 def step(self,q,t):
  key=(q,t)
  if key not in self.cache:
   v=q
   while v and t not in self.next[v]:v=self.fail[v]
   self.cache[key]=self.next[v].get(t,0)
  return self.cache[key]

def lift(edges,patterns):
 byid={e['source_edge']:e for e in edges};assert len(byid)==len(edges)
 ac=AC(patterns);nodes=sorted({v for e in edges for v in [e['u'],e['v']]});states=[(v,0) for v in nodes];index={s:i for i,s in enumerate(states)}
 endpoint={}
 for q,prefix in enumerate(ac.prefix):
  if not q or ac.bad[q]:continue
  assert all(token in byid for token in prefix)
  assert all(byid[a]['v']==byid[b]['u'] for a,b in zip(prefix,prefix[1:]))
  endpoint[q]=byid[prefix[-1]]['v'];index[endpoint[q],q]=len(states);states.append((endpoint[q],q))
 adj=defaultdict(list)
 for e in edges:adj[e['u']].append(e)
 out=[]
 for source,(v,q) in enumerate(states):
  for e in adj[v]:
   destq=ac.step(q,e['source_edge'])
   if ac.bad[destq]:continue
   if destq:assert endpoint[destq]==e['v']
   out.append({'source_edge':len(out),'u':source,'v':index[e['v'],destq],'weight':e['weight'],'projection':e['source_edge']})
 return states,out,ac

def patterns_from_probes(probes):
 result=[]
 for r in probes['candidate_cycles']:
  if r['status']!='REFUTED':continue
  ids=r['source_edge_ids'];count=r['forbidden_edges'];result.append(tuple(ids[j%len(ids)] for j in range(count)))
 return sorted(set(result))

def main():
 start=time.perf_counter();base=json.loads((H/'filtered_critical_edges.json').read_text());probes=json.loads((H/'critical_cycle_probes.json').read_text());patterns=patterns_from_probes(probes);byid={e['source_edge']:e for e in base};rounds=[];unresolved=[]
 for iteration in range(5):
  states,edges,ac=lift(base,patterns);comps,labels=scc(edges);inside=defaultdict(list)
  for e in edges:
   if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
  cyclic=[(k,S,inside[k]) for k,S in enumerate(comps) if len(S)>1 or any(e['u']==e['v'] for e in inside[k])];new=[];checks=[]
  for k,S,E in sorted(cyclic,key=lambda x:-len(x[1])):
   adj=defaultdict(list)
   for e in E:adj[e['u']].append(e)
   vs=sorted(S)
   for root in [vs[i*(len(vs)-1)//min(7,len(vs)-1)] for i in range(min(8,len(vs)))]:
    C=shortest_cycle(adj,root,maxdepth=64)
    if not C:continue
    projected=[byid[e['projection']] for e in C];r=realize(projected,max_edges=64,max_states=20000);ids=[e['source_edge'] for e in projected]
    r.update({'lift_cycle_length':len(C),'projected_ids':ids,'lift_component':k});checks.append(r)
    if r['status']=='REFUTED':
     word=tuple(ids[j%len(ids)] for j in range(r['forbidden_edges']))
     if word not in patterns and word not in new:new.append(word)
    else:unresolved.append(r)
  stats={'iteration':iteration,'base_vertices':len({v for e in base for v in [e['u'],e['v']]}),'lift_states':len(states),'lift_edges':len(edges),'patterns':len(patterns),'AC_states':len(ac.next),'cyclic_components':[{'nodes':len(S),'edges':len(E)} for _,S,E in cyclic],'new_refuted_patterns':len(new),'checked_cycles':checks}
  rounds.append(stats);print(json.dumps({k:v for k,v in stats.items() if k!='checked_cycles'}),flush=True)
  if not new:break
  if iteration<4:patterns=sorted(set(patterns)|set(new))
 out={'status':'CHECKED_FORBIDDEN_HISTORIES_ON_FROZEN_SUBSET','source_scope':'filtered frozen tight subgraph, NOT the complete current graph','forbidden_patterns':[list(p) for p in patterns],'rounds':rounds,'unresolved_cycle_probes':unresolved,'seconds':time.perf_counter()-start,'new_global_bound':None,'mean_above480_proved':False}
 (H/'history_separation.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
