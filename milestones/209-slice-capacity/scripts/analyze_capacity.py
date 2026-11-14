"""Calculate the square-slice capacity consequence for the fixed source."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
P=H.parent/'207-five-history'
rows=json.loads((P/'data/six-coordinate-summary.json').read_bytes())['covered_records']
records=[]
for row in rows:
    path=P/row['folder']/'model.json'
    m=json.loads(path.read_bytes())
    visits=[set() for _ in range(m['variables'])]
    for z,g in zip(m['z'],m['group']): visits[g].add(z)
    parities=[]
    for parity in range(2):
        multi=[g for g,s in enumerate(visits) if g%2==parity and len(s)>1]
        single=[[g for g,s in enumerate(visits) if g%2==parity and s=={z}] for z in range(4)]
        a=max([0,3],key=lambda z:len(single[z]))
        b=max([1,2],key=lambda z:len(single[z]))
        clique=multi+single[a]+single[b]
        outside=[g for g in range(m['variables']) if g%2==parity and g not in clique]
        partners={str(g):single[next(iter(visits[g]))^3] for g in outside}
        parities.append({'parity':parity,'multi':multi,'single':single,
            'chosen_singleton_slices':[a,b],'clique':clique,
            'demand':len(clique),'available_words':32,'saturated':len(clique)==32,
            'outside':outside,'opposite_singleton_partners':partners})
    records.append({'index':row['index'],'base':m['base'],'variables':m['variables'],
        'model_path':str(path.relative_to(H.parent.parent)),
        'model_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'visits':[sorted(s) for s in visits],'parities':parities})
out={'source_sha256':hashlib.sha256((H/'data/lower-dimensional-input.json').read_bytes()).hexdigest(),
    'records':records,'scope':'Native extraction of interval visits and clique counts. Geometric proof is separate; no model is excluded by these counts.'}
(H/'data/square-capacity.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps([{'index':r['index'],'base':r['base'],'demand':[p['demand'] for p in r['parities']]} for r in records if any(p['saturated'] for p in r['parities'])],indent=2))
