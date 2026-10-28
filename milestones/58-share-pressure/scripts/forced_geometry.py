"""Count empty faces forced solely by selected-segment internal degrees."""
from pathlib import Path
import itertools,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
source=ROOT/'milestones/57-replacement-share-family/combined'
meta=json.loads((source/'data/model.json').read_text());records=[]
pairs=list(itertools.combinations(range(9),2))
for ds in meta['extensions']:
    path=[0]
    for d in ds:path.append(path[-1]^(1<<d))
    selected=set(path)
    absent={v^(1<<a) for v in path[1:-1] for a in range(9)}-selected
    assert all(sum((x^(1<<a)) in selected for a in range(9))==2 for x in path[1:-1])
    centres=path[-6:-1];terms=[];total=0
    for x in centres:
        for a in range(9):
            q=x^(1<<a)
            if q in selected:continue
            faces=[sorted([q,q^(1<<b),q^(1<<c),q^(1<<b)^(1<<c)]) for b,c in pairs if {q,q^(1<<b),q^(1<<c),q^(1<<b)^(1<<c)}<=absent]
            upper=sum((q^(1<<b)) not in absent for b in range(9))
            assert 1<=upper<=9
            term=12*len(faces)//upper
            if term:terms.append(dict(centre=x,corner=q,forced_empty_faces=faces,degree_upper=upper,credit=term))
            total+=term
    records.append(dict(directions=ds,centres=centres,forced_absent=sorted(absent),share_lower=total,terms=terms))
analyses=[]
for folder in [source,HERE/'candidate']:
    if not (folder/'data/analysis-share.json').exists():continue
    r=json.loads((folder/'data/analysis-share.json').read_text())
    credits=[records[meta['extensions'].index(e['directions'])]['share_lower'] for e in r['cycle']]
    analyses.append(dict(source=folder.relative_to(ROOT).as_posix(),cycle_length=len(credits),credits=credits,total=sum(credits)))
out=dict(patterns=records,cycle_comparisons=analyses,scope='Explicit forced-absence geometric certificates computed from each segment. Lean status is recorded separately in data/lean-audit.json; the complete finite-model-to-snake assembly is a separate obligation.')
(HERE/'data/forced-geometry.json').write_text(json.dumps(out,indent=2)+'\n')
print(dict(positive_shapes=sum(r['share_lower']>0 for r in records),shapes=len(records),maximum=max(r['share_lower'] for r in records),cycles=analyses))
