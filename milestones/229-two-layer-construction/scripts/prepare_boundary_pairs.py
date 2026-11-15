"""Apply the width45 boundary disjunction and necessary Q8 pruning to templates."""
from pathlib import Path
import collections,copy,hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
N=[{v^(1<<k) for k in range(8)} for v in range(256)]
def prune(domain,anchors,edges):
    domain=set(domain);u,v=anchors
    if not {u,v}<=domain:return None,'ANCHOR'
    queue=collections.deque(x for x in domain if x not in anchors and len(N[x]&domain)<2)
    while queue:
        x=queue.popleft()
        if x not in domain or len(N[x]&domain)>=2:continue
        adjacent=N[x]&domain;domain.remove(x);queue.extend(z for z in adjacent if z not in anchors and len(N[z]&domain)<2)
    comp={u};queue=[u]
    while queue:
        x=queue.pop()
        for z in N[x]&domain-comp:comp.add(z);queue.append(z)
    if v not in comp:return None,'DISCONNECTED'
    if len(comp)<edges+1:return None,'SIZE'
    even=(edges+2)//2 if u.bit_count()%2==0 else (edges+1)//2
    if sum(x.bit_count()%2==0 for x in comp)<even or sum(x.bit_count()%2==1 for x in comp)<edges+1-even:return None,'COLOUR'
    return sorted(comp),None
source=H/'data/lower-pairs.json';rawpath=H/'data/regions46.json';closurepath=H/'data/coverage45.json'
old=read(source);raw=read(rawpath);closure=read(closurepath)
assert raw['width']==46 and closure['status']=='COMPLETE_NATIVE_EXCLUSION' and closure['width']==45
assert all(sha(p)==h for p,h in closure['pins'].items())
seed=raw['seed'];configs=[];origins={};rejections=collections.Counter();records=[]
for c in old['configurations']:
    upper=[c['first_upper_prefix']+c['first_upper_suffix'],c['upper_prefix']+c['upper_suffix']]
    anchors=[c['first_anchors'],c['lower_anchors']];domains=[set(c['first_domain']),set(c['lower_domain'])];edges=[c['first_edges'],c['lower_edges']]
    created=[];branchrecords=[]
    for chosen in [0,1]:
        i,j=c['intervals'][chosen];oldneighbours=[seed[i+1],seed[j-1]]
        if any(z in upper[chosen] or z in anchors[chosen] for z in oldneighbours):
            rejections['FIXED_BOUNDARY_NEIGHBOUR']+=1;branchrecords.append(dict(chosen=chosen,status='FIXED_BOUNDARY_NEIGHBOUR'));continue
        ds=[set(x) for x in domains];ds[chosen]-=set(oldneighbours)
        for k in [0,1]:
            for u in anchors[1-k]:ds[k]-=N[u]|{u}
        reduced=[];failure=None
        for k in [0,1]:
            values,reason=prune(ds[k],anchors[k],edges[k])
            if reason:failure=f'PART{k}_{reason}';break
            reduced.append(values)
        if failure:
            rejections[failure]+=1;branchrecords.append(dict(chosen=chosen,status=failure));continue
        new=copy.deepcopy(c);new.update(id=len(configs),parent_configuration=c['id'],boundary_choice=chosen,first_domain=reduced[0],lower_domain=reduced[1])
        configs.append(new);created.append(new['id']);branchrecords.append(dict(chosen=chosen,status='PREPARED',configuration=new['id']))
    origins[str(c['id'])]=created;records.append(dict(parent_configuration=c['id'],branches=branchrecords))
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
contexts=[]
for row in old['contexts']:
    x=dict(row);x['original_configurations']=row['configurations'];x['configurations']=[i for oldid in row['configurations'] for i in origins[str(oldid)]];contexts.append(x)
out=dict(status='COMPLETE_BOUNDARY_REDUCTION',width=46,pins={str(p):sha(p) for p in [source,rawpath,closurepath,Path(__file__)]},contexts=contexts,unsupported=old['unsupported'],configurations=configs,parent_configuration_map=origins,branch_records=records,branch_rejections=dict(rejections),exact_groups=groups,dominated=dominated,representatives=reps,scope='Width46 only. Each original upper template is split by which block changes both original boundary neighbours, using complete native45closure. Fixedupper/anchor contradictions and necessary lower-graph anchor, peeling, connectivity, size andcolour conditions remove branches. The boundary condition is fully instantiated in literal domains; no residual disjunction is omitted by task deduplication. Native preparation, not a Lean certificate.')
dest=H/'data/boundary-lower-pairs.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(configurations=len(configs),groups=len(groups),representatives=len(reps),empty_contexts=[r['context'] for r in contexts if not r['configurations']],branch_rejections=dict(rejections)),indent=2))
