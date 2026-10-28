"""Extract all minimum-charge cyclic components from the exact potential."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np
SOURCE=ROOT/'milestones/57-replacement-share-family/combined'

def decode(value,width):
    return tuple(value//6**j%6+1 for j in range(width-1,-1,-1))

meta=json.loads((SOURCE/'data/model.json').read_text());result=json.loads((SOURCE/'data/analysis-share.json').read_text())
with np.load(SOURCE/'build/graph.npz') as z:a={k:z[k] for k in z.files}
raw=gzip.decompress((SOURCE/'data/potential-share.i64.gz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==result['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mean=Fraction(result['integer_weight_mean']);p,q=mean.numerator,mean.denominator
W=120*a['count'].astype(np.int64)+a['share_lower'];slack=q*W+pi[a['U']]-pi[a['V']]-p
assert np.all(slack>=0)
ids=np.flatnonzero(slack==0);adj={};rev={}
for u,v in zip(a['U'][ids].tolist(),a['V'][ids].tolist()):
    adj.setdefault(u,[]).append(v);adj.setdefault(v,[])
    rev.setdefault(v,[]).append(u);rev.setdefault(u,[])
seen=set();order=[]
for root in adj:
    if root in seen:continue
    seen.add(root);stack=[(root,iter(adj[root]))]
    while stack:
        node,children=stack[-1];nxt=next(children,None)
        if nxt is None:order.append(node);stack.pop()
        elif nxt not in seen:seen.add(nxt);stack.append((nxt,iter(adj[nxt])))
component={};label=0
for root in reversed(order):
    if root in component:continue
    component[root]=label;stack=[root]
    while stack:
        node=stack.pop()
        for nxt in rev[node]:
            if nxt not in component:component[nxt]=label;stack.append(nxt)
    label+=1
ids=ids[np.array([component[int(u)]==component[int(v)] for u,v in zip(a['U'][ids],a['V'][ids])])]
windows=collections.Counter();coverage=collections.defaultdict(set);edges=collections.Counter();nodes=collections.defaultdict(set)
for i in ids:
    u,v=int(a['U'][i]),int(a['V'][i]);c=component[u]
    ds=meta['extensions'][int(a['direction'][i])][-6:];cs=decode(int(a['count_code'][i]),6)[-5:]
    key=min((model.canon(ds),cs),(model.canon(ds[::-1]),cs[::-1]))
    windows[key]+=1;coverage[key].add(c);edges[c]+=1;nodes[c].update([u,v])
ranking=sorted(windows,key=lambda k:(-len(coverage[k]),-windows[k],k))
rows=[dict(directions=list(ds),counts=list(cs),occurrences=windows[(ds,cs)],components=sorted(coverage[(ds,cs)])) for ds,cs in ranking]
(HERE/'data').mkdir(parents=True,exist_ok=True)
window_ids={key:i for i,key in enumerate(ranking)}
edge_records=[]
for i in ids:
    ds=meta['extensions'][int(a['direction'][i])][-6:];cs=decode(int(a['count_code'][i]),6)[-5:]
    key=min((model.canon(ds),cs),(model.canon(ds[::-1]),cs[::-1]))
    edge_records.append(dict(source_edge=int(i),u=int(a['U'][i]),v=int(a['V'][i]),window=window_ids[key]))
(HERE/'data/critical-edges.json').write_text(json.dumps(edge_records,indent=2)+'\n')
out=dict(status='EXACT_CRITICAL_FAMILY',source=SOURCE.relative_to(ROOT).as_posix(),source_mean=str(mean/120),
    source_potential_sha256=result['potential_sha256'],critical_edges=len(ids),
    critical_states=len(set(a['U'][ids].tolist()+a['V'][ids].tolist())),
    components=[dict(id=c,states=len(nodes[c]),edges=edges[c]) for c in sorted(edges)],
    positive_share_edges=int((a['share_lower'][ids]>0).sum()),windows=rows,
    scope='All tight cyclic edges under an exact finite-model potential. Model premises include numerical rules; this is not a global snake theorem.')
(HERE/'data/critical-family.json').write_text(json.dumps(out,indent=2)+'\n')
(HERE/'data/windows.json').write_text(json.dumps(rows,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['windows','components']},flush=True)
print('Components',out['components'],'windows',len(rows),'top five',rows[:5],flush=True)
