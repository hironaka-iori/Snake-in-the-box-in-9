"""Reuse proved sum13 to recover clipped-six excess, without double charging.
Actual alpha_i>=bucket_i+gain_i pointwise; uniform averaging across six
positions adds20*sum(gain) to the120-per-entering-count weight up to a
count-state coboundary. A zero-gain cycle obstructs any such gain-only upgrade.
"""
from pathlib import Path
from collections import Counter,defaultdict
import json,gzip
from probe_critical_cycles import scc,shortest_cycle
H=Path(__file__).resolve().parent

def canon(w):
 seen={};return [seen.setdefault(a,len(seen)) for a in w]
def gains(e):
 b=e['counts'];g=[0]*6
 for o in range(4):
  if canon(e['directions'][o:o+6])!=[0,1,2,3,4,0]:continue
  for pos in [[o+1,o+4,o+5],[o+5,o+2,o+1]]:
   if not all(3<=j<=8 for j in pos):continue
   ix=[j-3 for j in pos];delta=13-sum(b[j] for j in ix)
   if delta>0:
    assert sum(b[j]==6 for j in ix)==1
    target=next(j for j in ix if b[j]==6);g[target]=max(g[target],delta)
 return g
if __name__=='__main__':
 base=json.loads((H/'filtered_critical_edges.json').read_text());G={e['source_edge']:gains(e) for e in base};hist=Counter(sum(g) for g in G.values() if any(g));D=json.loads(gzip.decompress((H/'short_closure_lift.json.gz').read_bytes()));zero=[dict(e,source_edge=i) for i,e in enumerate(D['edges']) if not any(G[e['projection']])];cs,labels=scc(zero);inside=defaultdict(list)
 for e in zero:
  if labels[e['u']]==labels[e['v']]:inside[labels[e['u']]].append(e)
 cyclic=[(k,S,inside[k]) for k,S in enumerate(cs) if len(S)>1 or any(e['u']==e['v'] for e in inside[k])]
 r={'affected_base_edges':sum(hist.values()),'total_gain_histogram':dict(hist),'lift_zero_gain_edges':len(zero),'zero_gain_cyclic_SCCs':[{'nodes':len(S),'edges':len(E)} for _,S,E in cyclic],'new_global_bound':None,'scope':'existing sum13 consequences on one explicit subgraph; no new boundary theorem'}
 if cyclic:
  _,S,E=min(cyclic,key=lambda t:len(t[1]));adj=defaultdict(list)
  for e in E:adj[e['u']].append(e)
  C=shortest_cycle(adj,min(S),10000);r['zero_gain_cycle']=[e['projection'] for e in C]
 (H/'bucket_excess_probe.json').write_text(json.dumps(r,indent=2)+'\n');(H/'bucket_excess_gains.json').write_text(json.dumps(G,separators=(',',':'))+'\n');print(json.dumps({k:v for k,v in r.items() if k!='zero_gain_cycle'},indent=2))
