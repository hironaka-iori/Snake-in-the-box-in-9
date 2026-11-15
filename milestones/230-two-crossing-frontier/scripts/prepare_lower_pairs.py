"""Reduce forced single-lower-segment replacements to Q8 path pairs."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def adjacent(x,y):return (x^y).bit_count()==1
def upper_paths(domain,start,other,ports):
    out=[];stack=[[start]];nodes=0
    while stack:
        path=stack.pop();nodes+=1
        if path[-1]-256 in ports:out.append(path)
        for z in sorted(domain-set(path)-{other},reverse=True):
            if adjacent(z,path[-1]) and not any(adjacent(z,v) for v in path[:-1]):stack.append(path+[z])
    return out,nodes
def templates(part,w):
    u,v=part['anchors'];low={z for z in part['allowed'] if z<256};upper=set(part['allowed'])-low
    ports={z for z in low if z+256 in upper}
    left,ln=upper_paths(upper,u,v if v>=256 else None,ports) if u>=256 else ([[]],0)
    right,rn=upper_paths(upper,v,u if u>=256 else None,ports) if v>=256 else ([[]],0)
    out=[]
    for a in left:
        for reverseb in right:
            if any(x==y or adjacent(x,y) for x in a for y in reverseb):continue
            b=list(reversed(reverseb));s=a[-1]-256 if a else u;t=b[0]-256 if b else v
            edges=w-len(a)-len(b);projections={z-256 for z in a+b}
            own_ports=({s} if a else set()) | ({t} if b else set())
            allowed=low-(projections-own_ports)
            if edges<0 or (s==t)!=(edges==0) or not {s,t}<=allowed:continue
            out.append(dict(anchors=[s,t],edges=edges,allowed=sorted(allowed),upper_prefix=a,upper_suffix=b,projections=sorted(projections)))
    return out,dict(upper_vertices=len(upper),ports=sorted(ports),prefix_nodes=ln,suffix_nodes=rn,templates=len(out))
source=H/'data/regions46.json';resultpath=H/'data/baseline46.json'
raw=json.loads(source.read_bytes());result=json.loads(resultpath.read_bytes())
assert result['status']=='STATIC_BASELINE'
assert len(result['contexts'])==len(raw['contexts'])
ids=[r['id'] for r in result['contexts'] if r['status']=='OPEN']
rows=[];configs=[];unsupported=[];w=raw['width']
for ident in ids:
    row=raw['contexts'][ident];budget=row['replacement_crossings']-2;assert budget>=0
    choices=[];desired=[]
    for part in row['parts']:
        u,v=part['anchors'];parity=int((u<256)!=(v<256))
        allowed=[k for k in range(parity,budget+1,2) if k!=0 or sum((z<256)==(u<256) for z in part['allowed'])>=w+1]
        choices.append(allowed);desired.append(int(u>=256)+int(v>=256))
    allocations=[[a,b] for a in choices[0] for b in choices[1] if a+b==budget]
    if allocations!=[desired]:
        unsupported.append(dict(context=ident,allocations=allocations,desired=desired));continue
    first,fa=templates(row['parts'][0],w);second,sa=templates(row['parts'][1],w);made=[]
    for p in first:
        for q in second:
            up=p['upper_prefix']+p['upper_suffix'];uq=q['upper_prefix']+q['upper_suffix']
            if any(x==y or adjacent(x,y) for x in up for y in uq):continue
            pd=set(p['allowed'])-set(q['projections']);qd=set(q['allowed'])-set(p['projections'])
            if not set(p['anchors'])<=pd or not set(q['anchors'])<=qd:continue
            c=dict(id=len(configs),context=ident,intervals=row['intervals'],first_anchors=p['anchors'],first_edges=p['edges'],first_domain=sorted(pd),lower_anchors=q['anchors'],lower_edges=q['edges'],lower_domain=sorted(qd),first_upper_prefix=p['upper_prefix'],first_upper_suffix=p['upper_suffix'],upper_prefix=q['upper_prefix'],upper_suffix=q['upper_suffix'])
            configs.append(c);made.append(c['id'])
    rows.append(dict(context=ident,allocations=allocations,first_enumeration=fa,second_enumeration=sa,configurations=made))
groups=collections.defaultdict(list)
for c in configs:
    key=(tuple(c['first_anchors']),c['first_edges'],tuple(c['first_domain']),tuple(c['lower_anchors']),c['lower_edges'],tuple(c['lower_domain']))
    groups[key].append(c['id'])
groups=list(groups.values());reps=[g[0] for g in groups];dominated={}
for i in reps:
    c=configs[i]
    for j in reps:
        if i==j:continue
        d=configs[j]
        if (c['first_anchors'],c['first_edges'],c['lower_anchors'],c['lower_edges'])!=(d['first_anchors'],d['first_edges'],d['lower_anchors'],d['lower_edges']):continue
        if set(c['first_domain'])<=set(d['first_domain']) and set(c['lower_domain'])<=set(d['lower_domain']):dominated[str(i)]=j;break
for i in dominated:
    seen=set();v=int(i)
    while str(v) in dominated:assert v not in seen;seen.add(v);v=dominated[str(v)]
    dominated[i]=v
reps=[i for i in reps if str(i) not in dominated]
out=dict(status='COMPLETE_FOR_REDUCIBLE_CONTEXTS',width=w,total_crossings=2,pins={str(p):sha(p) for p in [source,resultpath,Path(__file__)]},contexts=rows,unsupported=unsupported,configurations=configs,exact_groups=groups,dominated=dominated,representatives=reps,scope='Only still-open contexts with uniquely forced allocation equal to the number of upper anchors in each replacement. Both paths then have one lower segment. Complete small-upper enumeration and pair separation give explicit Q8 tasks. Unsupported contexts remain unresolved. No inherited upward exclusion; no boundary cut is required in the reduced model. Native preparation, not a Lean traversal proof.')
dest=H/'data/lower-pairs.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(open_contexts=len(ids),reduced_contexts=len(rows),unsupported=unsupported,configurations=len(configs),groups=len(groups),representatives=len(reps),empty_contexts=[r['context'] for r in rows if not r['configurations']]),indent=2))
