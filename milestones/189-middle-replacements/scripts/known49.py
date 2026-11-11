from pathlib import Path
import json,itertools,collections
R=Path('E:/Snake-in-a-box');H=R/'milestones/189-middle-replacements';P=R/'milestones/188-dimensional-constructions'
rows=json.loads((H/'data/nested-contexts.json').read_text());p50=json.loads((P/'data/lower-dimensional-seeds.json').read_text())['7']['vertices']
def norm(row):
    options=[]
    for path in [row['middle'],row['middle'][::-1]]:
        names={}
        for u,v in zip(path,path[1:]):names.setdefault((u^v).bit_length()-1,len(names))
        assert len(names)==7
        def f(v):return sum((((v^path[0])>>k)&1)<<j for k,j in names.items())
        options.append((tuple(f(v) for v in path),tuple(sorted(f(v) for v in row['allowed']))))
    return min(options)
contexts=[norm(r) for r in rows];target=contexts[0][0];assert all(c[0]==target for c in contexts);delta=target[-1];assert delta.bit_count()==5
target_on=[k for k in range(7) if delta>>k&1];target_off=[k for k in range(7) if not delta>>k&1];masks=[]
for src in [p50[:-1],p50[1:]]:
    for path in [src,src[::-1]]:
        path=[v^path[0] for v in path];d=path[-1];assert d.bit_count()==5
        source_on=[k for k in range(7) if d>>k&1];source_off=[k for k in range(7) if not d>>k&1]
        for a in itertools.permutations(target_on):
            for b in itertools.permutations(target_off):
                mapping=dict(zip(source_on+source_off,a+b));image=[sum(((v>>k)&1)<<j for k,j in mapping.items()) for v in path];masks.append(sum(1<<v for v in image))
assert len(masks)==960 and len(set(masks))==960
results=[]
for r,c in zip(rows,contexts):
    forbidden=set(range(128))-set(c[1]);mask=sum(1<<v for v in forbidden);counts=[(mask&m).bit_count() for m in masks]
    results.append({'context_index':r['context_index'],'minimum_forbidden_overlap':min(counts),'number_attaining':counts.count(min(counts)),'histogram':dict(collections.Counter(counts))})
out={'candidate_placements':960,'distinct_vertex_sets':len(set(masks)),'endpoint_distance':5,'scope':'Both49-edge endpoint truncations of the displayed50-edgeQ7snake, both orientations, and all5!2! endpoint-preserving coordinate permutations. All84nestedcontexts.','contexts':results,'minimum_overlap_distribution':dict(collections.Counter(r['minimum_forbidden_overlap'] for r in results))}
(H/'data/known49-replacements.json').write_text(json.dumps(out,indent=2)+'\n');(H/'scripts/known49.py').write_bytes(Path(__file__).read_bytes());print(json.dumps(out['minimum_overlap_distribution'],indent=2))
