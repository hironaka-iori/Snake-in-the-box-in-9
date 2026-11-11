from pathlib import Path
import json,itertools,collections,hashlib,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';PRE=R/'milestones/188-dimensional-constructions'
rows=json.loads((H/'data/replacement-contexts.json').read_text())['rows'];seeds=json.loads((PRE/'data/lower-dimensional-seeds.json').read_text());p98=seeds['8']['vertices']
def norm_context(row):
    variants=[]
    for path in [row['middle'],row['middle'][::-1]]:
        order={}
        for u,v in zip(path,path[1:]):order.setdefault((u^v).bit_length()-1,len(order))
        def transform(v):return sum((((v^path[0])>>i)&1)<<j for i,j in order.items())
        path2=[transform(v) for v in path];left=[transform(v) for v in row['left']];right=[transform(v) for v in row['right']]
        variants.append((tuple(path2),tuple(left),tuple(right),tuple(sorted((i,j) for i,j in order.items())),path[0]))
    return min(variants)
group=[(idx,norm_context(r)) for idx,r in enumerate(rows) if r['middle_edges']==95];target=list(group[0][1][0]);assert all(list(c[0])==target for idx,c in group)
d=target[-1];assert d.bit_count()==3
ds=[i for i in range(8) if d>>i&1];dn=[i for i in range(8) if not d>>i&1]
sourcepaths=[p98[:-1],p98[1:]];candidates=[]
for trim,src in enumerate(sourcepaths):
    for reverse in [False,True]:
        path=src[::-1] if reverse else src;path=[v^path[0] for v in path];delta=path[-1]
        if delta.bit_count()!=d.bit_count():continue
        ss=[i for i in range(8) if delta>>i&1];sn=[i for i in range(8) if not delta>>i&1]
        for a in itertools.permutations(ds):
            for b in itertools.permutations(dn):
                order=dict(zip(ss+sn,a+b));mapped=[sum(((v>>i)&1)<<j for i,j in order.items()) for v in path]
                assert mapped[0]==0 and mapped[-1]==d
                mask=sum(1<<v for v in mapped);candidates.append({'trim':trim,'reverse':reverse,'mapping':[order[i] for i in range(8)],'vertices':mapped,'mask':mask})
assert len(candidates)==1440,len(candidates)
results=[];best_global=None
for idx,ctx in group:
    forbidden=(set(ctx[1])|set(ctx[2]))-{0,d};mask=sum(1<<v for v in forbidden)
    counts=[(c['mask']&mask).bit_count() for c in candidates];best=min(counts);winner=counts.index(best);c=candidates[winner]
    results.append({'context_index':idx,'minimum_forbidden_overlap':best,'number_attaining':counts.count(best),'best_candidate_index':winner,'overlap_vertices':sorted(forbidden&set(c['vertices'])),'histogram':dict(collections.Counter(counts))})
    if best_global is None or best<best_global['overlap']:best_global={'overlap':best,'context_index':idx,'canonical_context':{'middle':list(ctx[0]),'left':list(ctx[1]),'right':list(ctx[2]),'original_coordinate_mapping':list(ctx[3]),'translation':ctx[4]},'candidate':{k:v for k,v in c.items() if k!='mask'},'overlap_vertices':results[-1]['overlap_vertices']}
out={'candidate_placements':len(candidates),'distinct_candidate_vertex_sets':len({c['mask'] for c in candidates}),'endpoint_distance':3,'source_paths':'The two endpoint truncations of the displayed98-edgeQ8snake; only the distance3 truncation fits, in both orientations. All3!5! coordinate permutations per orientation.','source_sha256':hashlib.sha256((PRE/'data/lower-dimensional-seeds.json').read_bytes()).hexdigest(),'contexts':results,'minimum_overlap_distribution':dict(collections.Counter(r['minimum_forbidden_overlap'] for r in results)),'best_case':best_global}
(H/'data/known97-replacements.json').write_text(json.dumps(out,indent=2)+'\n');(H/'scripts/known_replacements.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'placements':len(candidates),'distinct':out['distinct_candidate_vertex_sets'],'minima':out['minimum_overlap_distribution'],'best_context':best_global['context_index'],'best_overlap':best_global['overlap'],'overlap_vertices':best_global['overlap_vertices']},indent=2))
