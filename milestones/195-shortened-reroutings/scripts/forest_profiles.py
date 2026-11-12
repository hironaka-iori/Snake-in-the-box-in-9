"""Extract four-crossing path forests and compare the dimensional examples."""
from pathlib import Path
import collections, hashlib, json
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
seedpath=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json'
bankpath=R/'work/bank9.json'
seeds=json.loads(seedpath.read_bytes()); bank=json.loads(bankpath.read_bytes())

def project(v,k): return (v&((1<<k)-1))|((v>>(k+1))<<k)
def cut(p,n,k):
    blocks=[]; start=0
    for i,(u,v) in enumerate(zip(p,p[1:])):
        if u^v==1<<k:
            blocks.append([project(w,k) for w in p[start:i+1]]); start=i+1
    blocks.append([project(w,k) for w in p[start:]])
    return blocks

comparisons={}
for n in [6,7,8]:
    p=seeds[str(n)]['vertices']; k=min(range(n),key=lambda k:sum(u^v==1<<k for u,v in zip(p,p[1:])))
    blocks=cut(p,n,k)
    comparisons[n]=dict(coordinate=k,component_edges=[len(b)-1 for b in blocks],
        face_vertices=[sum(len(b) for b in blocks[parity::2]) for parity in [0,1]],blocks=blocks)
forests=[]; seen=set()
for si,row in enumerate(bank):
    p=row['vertex_sequence']
    for k in range(9):
        blocks=cut(p,9,k)
        if len(blocks)!=5: continue
        paths=blocks[1::2]; fixed=set(paths[0]+paths[1]); ports=[b[0] for b in paths]+[b[-1] for b in paths]
        assert len(ports)==len(set(ports))==4
        assert len(fixed)==sum(map(len,paths))
        assert all((u^v).bit_count()!=1 for u in paths[0] for v in paths[1])
        key=tuple(sorted(fixed)),tuple(sorted(ports))
        if key in seen:continue
        seen.add(key)
        forests.append(dict(seed=si,coordinate=k,paths=paths,ports=ports,vertices=len(fixed),
            complement_paths=blocks[::2],complement_vertices=sum(map(len,blocks[::2]))))
forests.sort(key=lambda r:(-r['vertices'],r['seed'],r['coordinate']))
# Deleting one internal vertex of the displayed optimal Q8 path gives two
# induced, nonadjacent path components, with four distinct endpoints.
p=seeds['8']['vertices']; derived=[]
for index in range(2,len(p)-2):
    paths=[p[:index],p[index+1:]]
    derived.append(dict(deleted_index=index,paths=paths,ports=[b[0] for b in paths]+[b[-1] for b in paths],vertices=len(p)-1))
out=dict(status='COMPLETE',inputs={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in [seedpath,bankpath]},
    comparisons=comparisons,bank_forests=forests,derived_forests=derived,
    forest_vertex_histogram=dict(collections.Counter(r['vertices'] for r in forests)))
target=H/'data/forest-profiles.json'; assert not target.exists(); target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(comparisons={n:{k:v for k,v in r.items() if k!='blocks'} for n,r in comparisons.items()},
    bank_forests=len(forests),forest_vertex_histogram=out['forest_vertex_histogram'],derived_forests=len(derived))))
