"""Align known49-edge subpaths with the anchors of the fixed48-edge lift."""
from pathlib import Path
import hashlib,itertools,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json'
catalog=json.loads(source.read_text())['7']['vertices']
old=json.loads((H/'data/lower-input.json').read_text())[0]['vertex_sequence']
targetdiff=old[0]^old[-1];best=None;placements=0
def valid(p):
    return len(set(p))==len(p) and all((((u^p[j]).bit_count()==1)==(j==i+1)) for i,u in enumerate(p) for j in range(i+1,len(p)))
for offset in [0,1]:
    base=catalog[offset:offset+50]
    for reverse in [False,True]:
        path=base[::-1] if reverse else base
        diff=path[1]^path[-1]
        if diff.bit_count()!=targetdiff.bit_count():continue
        source1=[k for k in range(7) if diff&(1<<k)];source0=[k for k in range(7) if not diff&(1<<k)]
        dest1=[k for k in range(7) if targetdiff&(1<<k)];dest0=[k for k in range(7) if not targetdiff&(1<<k)]
        for ones in itertools.permutations(dest1):
            for zeroes in itertools.permutations(dest0):
                perm=dict(zip(source1+source0,ones+zeroes))
                def image(v):return sum(1<<perm[k] for k in range(7) if v&(1<<k))
                translation=old[0]^image(path[1])
                full=[image(v)^translation for v in path];q=full[1:]
                assert q[0]==old[0] and q[-1]==old[-1] and valid(full)
                changes=[i for i in range(49) if q[i]!=old[i]]
                assert changes
                i=min(changes)-1;j=max(changes)+1;placements+=1
                if best is None or j-i<best['block_length']:
                    best=dict(block_length=j-i,start=i,end=j,path=full,replacement=q[i:j+1],old_path=old,
                        source_offset=offset,source_reversed=reverse,coordinate_map=[perm[k] for k in range(7)],translation=translation,
                        extension_vertex=full[0],altered_positions=changes)
out=dict(status='COMPLETE',placements=placements,best=best,source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    scope='All coordinate permutations and translations aligning the48-edge tail of each oriented49-edge subpath of the displayed50-edge Q7 snake to the two fixed anchors. This is a restricted family of49-edge witnesses, not an exhaustive search over all such snakes.')
target=H/'data/aligned-lower49.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(placements=placements,best_block=best['block_length'],start=best['start'],end=best['end'],map=best['coordinate_map'],translation=best['translation'])))
