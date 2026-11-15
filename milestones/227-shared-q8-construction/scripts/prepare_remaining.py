"""Reduce the other 35 width44 contexts to pairs of lower-face paths."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def adjacent(x,y):return (x^y).bit_count()==1
def paths(domain,start,other,ports):
    found=[];stack=[[start]];nodes=0
    while stack:
        p=stack.pop();nodes+=1
        if p[-1]-256 in ports:found.append(p)
        for z in sorted(domain-set(p)-{other},reverse=True):
            if adjacent(z,p[-1]) and not any(adjacent(z,w) for w in p[:-1]):stack.append(p+[z])
    return found,nodes
source=H/'data/regions44.json';raw=json.loads(source.read_bytes())
previous=R/'milestones/226-connected-replacement-search/data/search-summary.json';s=json.loads(previous.read_bytes())
ids=sorted(set(s['width44_unresolved'])-set(s['shared_q8_contexts']));assert len(ids)==35
configs=[];rows=[]
for ident in ids:
    row=raw['contexts'][ident];first,second=row['parts'];u,v=second['anchors'];budget=row['replacement_crossings']
    firstlow={x for x in first['allowed'] if x<256};low={x for x in second['allowed'] if x<256};upper=set(second['allowed'])-low
    assert max(first['anchors'])<256
    if budget==1:assert (u<256)!=(v<256);allocation='endpoint parity forces (0,1)'
    else:assert budget==2 and min(u,v)>=256 and len(upper)<45;allocation='upper-face shortage and endpoint parity force (0,2)'
    ports={x for x in low if x+256 in upper};count=[];lc=rc=0
    if u>=256:left,lc=paths(upper,u,v if v>=256 else None,ports)
    else:left=[[]]
    if v>=256:right,rc=paths(upper,v,u if u>=256 else None,ports)
    else:right=[[]]
    for a in left:
        for br in right:
            if any(x==y or adjacent(x,y) for x in a for y in br):continue
            b=list(reversed(br));s0=a[-1]-256 if a else u;t0=b[0]-256 if b else v
            length=44-len(a)-len(b)
            projections={x-256 for x in a+b}
            domain=low-(projections-{s0,t0});fd=firstlow-projections
            if length<1 or s0==t0 or not {s0,t0}<=domain or not set(first['anchors'])<=fd:continue
            cfg=dict(id=len(configs),context=ident,first_anchors=first['anchors'],first_edges=44,first_domain=sorted(fd),lower_anchors=[s0,t0],lower_edges=length,lower_domain=sorted(domain),upper_prefix=a,upper_suffix=b,intervals=row['intervals'])
            configs.append(cfg);count.append(cfg['id'])
    rows.append(dict(context=ident,allocation=allocation,first_anchors=first['anchors'],second_anchors=second['anchors'],upper_vertices=len(upper),ports=sorted(ports),prefix_nodes=lc,suffix_nodes=rc,configurations=count))
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
        if set(c['first_domain'])<=set(d['first_domain']) and set(c['lower_domain'])<=set(d['lower_domain']):
            dominated[str(i)]=j;break
assert all(int(i)!=j for i,j in dominated.items())
for i in dominated:
    seen=set();v=int(i)
    while str(v) in dominated:assert v not in seen;seen.add(v);v=dominated[str(v)]
    dominated[i]=v
reps=[i for i in reps if str(i) not in dominated]
out=dict(status='COMPLETE_UPPER_ENUMERATION',pins={str(source):sha(source),str(previous):sha(previous),str(Path(__file__)):sha(__file__)},contexts=rows,configurations=configs,exact_groups=groups,dominated=dominated,representatives=reps,scope='Other35 previously unresolved width44 contexts. Crossing parity/upper-face shortage force first path in Q8. Complete small-upper-face enumeration reduces the second to one Q8 excursion. Exact duplicates and same-endpoint/length domain-contained tasks are removed for existence search only. Native enumeration, not Lean traversal.')
(H/'data/remaining-companions.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(contexts=len(rows),configurations=len(configs),groups=len(groups),representatives=reps,empty_contexts=[r['context'] for r in rows if not r['configurations']]),indent=2))
