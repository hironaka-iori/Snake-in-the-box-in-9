from pathlib import Path
import json,collections,hashlib,shutil
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';PRE=R/'milestones/188-dimensional-constructions'
for name in ['data','scripts','lean','build','logs','sources']:(H/name).mkdir(parents=True,exist_ok=True)
for name in ['check_core.py','native_resources.py']:
    if not (H/'scripts'/name).exists():shutil.copyfile(PRE/'scripts'/name,H/'scripts'/name)
(H/'.gitattributes').write_text('* -text\n')
bank=json.loads((R/'work/bank9.json').read_text());ancestry=json.loads((PRE/'data/middle-ancestry.json').read_text())['rows']
def project(v,k):return (v&((1<<k)-1))|((v>>(k+1))<<k)
def check(p):
    assert len(p)==len(set(p))
    assert all(((u^v).bit_count()==1)==(j==i+1) for i,u in enumerate(p) for j,v in enumerate(p) if i<j)
def graph(vs):return {v:{v^(1<<k) for k in range(8)}&vs for v in vs}
def peel(vs,ports):
    vs=set(vs);g=graph(vs);removed=[];todo=collections.deque(v for v in vs if v not in ports and len(g[v])<2)
    while todo:
        v=todo.popleft()
        if v not in vs or v in ports or len(g[v])>=2:continue
        removed.append(v);vs.remove(v)
        for u in g[v]:
            g[u].remove(v)
            if u not in ports and len(g[u])<2:todo.append(u)
        g[v]=set()
    return vs,removed
def blocks(g):
    seen={};low={};stack=[];out=[]
    def dfs(u,parent):
        seen[u]=low[u]=len(seen)
        for v in sorted(g[u]):
            if v==parent:continue
            if v not in seen:
                stack.append((u,v));dfs(v,u);low[u]=min(low[u],low[v])
                if low[v]>=seen[u]:
                    block=set()
                    while True:
                        edge=stack.pop();block.update(edge)
                        if edge==(u,v):break
                    out.append(block)
            elif seen[v]<seen[u]:stack.append((u,v));low[u]=min(low[u],seen[v])
    for v in sorted(g):
        if v not in seen:dfs(v,None)
    return out
def route_vertices(g,ports):
    bs=blocks(g);belongs={v:[i for i,b in enumerate(bs) if v in b] for v in g}
    tree={('b',i):set() for i in range(len(bs))}
    for v,ids in belongs.items():
        if len(ids)>1:
            node=('v',v);tree[node]={('b',i) for i in ids}
            for i in ids:tree[('b',i)].add(node)
    anchors=[('v',v) if len(belongs[v])>1 else ('b',belongs[v][0]) for v in ports]
    parent={anchors[0]:None};todo=collections.deque([anchors[0]])
    while todo:
        u=todo.popleft()
        for v in tree[u]:
            if v not in parent:parent[v]=u;todo.append(v)
    assert anchors[1] in parent
    route=[];u=anchors[1]
    while u is not None:route.append(u);u=parent[u]
    ids=[x[1] for x in route if x[0]=='b'];retained=set().union(*(bs[i] for i in ids))
    return retained,[sorted(bs[i]) for i in ids]
rows=[]
for a in ancestry:
    k=a['coordinate'];p=bank[a['bank_index']]['vertex_sequence'];cuts=[i for i in range(len(p)-1) if p[i]^p[i+1]==1<<k];i,j=cuts
    left=[project(v,k) for v in p[:i+1]];middle=[project(v,k) for v in p[i+1:j+1]];right=[project(v,k) for v in p[j+1:]]
    for q in [left,middle,right]:check(q)
    ports=[middle[0],middle[-1]];outer=set(left)|set(right);assert set(middle)&outer==set(ports)
    assert not set(left)&set(right) and not any((u^v).bit_count()==1 for u in left for v in right)
    allowed=set(range(256))-(outer-set(ports));peeled,removed=peel(allowed,set(ports));retained,bs=route_vertices(graph(peeled),ports)
    assert set(middle)<=retained
    parity=collections.Counter(v.bit_count()%2 for v in retained)
    s,t=[v.bit_count()%2 for v in ports]
    maxvertices=2*min(parity.values()) if s!=t else 2*min(parity[s]-1,parity[1-s])+1
    rows.append({'bank_index':a['bank_index'],'coordinate':k,'middle_class':a['middle_class'],'middle_edges':len(middle)-1,'outer_edges':len(left)+len(right)-2,'ports':ports,'port_distance':(ports[0]^ports[1]).bit_count(),'left':left,'middle':middle,'right':right,'allowed':sorted(allowed),'peeled':sorted(peeled),'peel_order':removed,'retained':sorted(retained),'blocks':bs,'parity_counts':dict(parity),'parity_max_edges':maxvertices-1,'degree_histogram':dict(collections.Counter(map(len,graph(retained).values())))})
out={'source_bank_sha256':hashlib.sha256((R/'work/bank9.json').read_bytes()).hexdigest(),'rows':rows,'summary':dict(collections.Counter(str((r['middle_class'],len(r['allowed']),len(r['peeled']),len(r['retained']),len(r['blocks']),r['parity_max_edges'])) for r in rows))}
(H/'data/replacement-contexts.json').write_text(json.dumps(out,indent=2)+'\n');(H/'scripts/anatomy.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(out['summary'],indent=2))
