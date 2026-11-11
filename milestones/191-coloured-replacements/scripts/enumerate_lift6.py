from pathlib import Path
import hashlib,json,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/191-coloured-replacements';source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json'
middle=json.loads(source.read_text())['6']['vertices'];ports=[middle[0],middle[-1]];allowed=set(range(64))-(set(middle)-set(ports));nb=[{v^(1<<i) for i in range(6)} for v in range(64)];start=time.monotonic()
def paths(root,other):
    result=[];path=[root]
    def visit():
        if time.monotonic()-start>60:raise TimeoutError('Enumeration incomplete; no bound.')
        mask=sum(1<<v for v in path);closed=mask
        for v in path:
            for u in nb[v]:closed|=1<<u
        result.append({'vertices':path.copy(),'mask':mask,'closed_mask':closed,'size':len(path)})
        for v in sorted((nb[path[-1]]&allowed)-set(path)-{other}):
            if any(v in nb[u] for u in path[:-1]):continue
            path.append(v);visit();path.pop()
    visit();return result
a=paths(ports[0],ports[1]);b=paths(ports[1],ports[0]);b.sort(key=lambda x:x['size'],reverse=True);best=0;witness=None;examined=0
for x in a:
    for y in b:
        if x['size']+y['size']<=best:break
        examined+=1
        if x['mask']&y['closed_mask']:continue
        best=x['size']+y['size'];witness=[x['vertices'],y['vertices']];break
joined=witness[0][::-1]+[v+64 for v in middle]+witness[1]
assert len(joined)==len(set(joined)) and all(((joined[i]^joined[j]).bit_count()==1)==(j==i+1) for i in range(len(joined)) for j in range(i+1,len(joined)))
out={'status':'COMPLETE','seconds':time.monotonic()-start,'allowed_vertices':len(allowed),'path_counts':[len(a),len(b)],'pair_checks_after_size_pruning':examined,'maximum_outer_vertices':best,'maximum_joined_edges':len(joined)-1,'outside_paths':witness,'joined_vertices':joined,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'scope':'All induced paths starting at either port in the allowed Q6 graph, excluding the other port. All disjoint nonadjacent pairs covered, with size-only pruning. Singleton paths included. Finite native enumeration, no complete Lean certificate.'}
(H/'data/fixed26-enumeration.json').write_text(json.dumps(out,indent=2)+'\n')
(H/'data/fixed26-paths.json').write_text(json.dumps({'ports':ports,'first':a,'second':b},indent=2)+'\n')
(H/'scripts/enumerate_lift6.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({k:v for k,v in out.items() if k not in ['outside_paths','joined_vertices']},indent=2))
