from pathlib import Path
import json,hashlib,collections,time
H=Path(__file__).resolve().parent;P=H.parent/'global-cycle-compression-20261031/critical_edges_frozen.json';raw=P.read_bytes();D=json.loads(raw);groups=collections.defaultdict(list)
for e in D:groups[e['component']].append(e)

def vertices(word):
 out=[0]
 for a in word:out.append(out[-1]^(1<<a))
 return out

def analyze(C,phase,max_edges=30,max_states=200000):
 order=[];v=phase
 for _ in range(len(C)):
  es=[e for e in C if e['u']==v];assert len(es)==1;e=es[0];order.append(e);v=e['v']
 assert v==phase and len({e['u'] for e in order})==len(C)
 first=order[0]['directions'];V=vertices(first)
 assert all((a^b).bit_count()>1 for i,a in enumerate(V) for j,b in enumerate(V) if j>i+1)
 frontier=[(first,V)];stats=[];total=1
 for count in range(2,max_edges+1):
  word=order[(count-1)%len(order)]['directions'];nxt=[];rejected=collections.Counter();options=0;newlabelbranches=0
  for directions,verts in frontier:
   mp={}
   for symbol,coord in zip(word[:8],directions[-8:]):
    assert symbol not in mp or mp[symbol]==coord
    mp[symbol]=coord
   assert len(set(mp.values()))==len(mp)
   if word[-1] in mp:choices=[mp[word[-1]]]
   else:choices=[c for c in range(9) if c not in mp.values()];newlabelbranches+=len(choices)
   for c in choices:
    options+=1;x=verts[-1]^(1<<c);bad=[i for i,v in enumerate(verts[:-1]) if (x^v).bit_count()<=1]
    if bad:rejected['repeat' if any(x==verts[i] for i in bad) else 'chord']+=1
    else:nxt.append((directions+[c],verts+[x]))
  total+=len(nxt);stats.append({'edge_count':count,'transition_count':8+count,'alive':len(nxt),'candidate_extensions':options,'new_label_choices':newlabelbranches,'rejected':dict(rejected),'alive_directions_sha256':hashlib.sha256(json.dumps(sorted(x[0] for x in nxt),separators=(',',':')).encode()).hexdigest()})
  if not nxt:return {'phase_vertex':phase,'cycle_ids':[e['source_edge'] for e in order],'status':'ALL_BRANCHES_REJECTED','forbidden_edge_count':count,'total_alive_states':total,'longest_survivor_directions':frontier[0][0],'forbidden_9edge_pattern':[order[j%len(order)]['source_edge'] for j in range(count)],'levels':stats}
  if total>max_states:return {'phase_vertex':phase,'cycle_ids':[e['source_edge'] for e in order],'status':'BUDGET','total_alive_states':total,'last_level':stats[-1],'witness_directions':nxt[0][0]}
  frontier=nxt
 return {'phase_vertex':phase,'cycle_ids':[e['source_edge'] for e in order],'status':'DEPTH_LIMIT','total_alive_states':total,'last_level':stats[-1],'witness_directions':frontier[0][0]}
rows=[]
for component,C in groups.items():
 nodes={v for e in C for v in [e['u'],e['v']]}
 if len(nodes)>4:continue
 for phase in sorted(nodes):
  row=analyze(C,phase);row['component']=component;rows.append(row);print(json.dumps({k:v for k,v in row.items() if k!='levels'}),flush=True)
result={'source_sha256':hashlib.sha256(raw).hexdigest(),'source_records':len(D),'scope':'old frozen six-component edge family; not current eight-case graph; counts/history bridge not proved here','components':[{'component':c,'nodes':len({v for e in C for v in [e['u'],e['v']]}),'edges':len(C)} for c,C in groups.items()],'small_cycle_results':rows}
(H/'review.json').write_text(json.dumps(result,indent=2))
