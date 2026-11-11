from pathlib import Path
import json,collections
H=Path('E:/Snake-in-a-box/milestones/188-dimensional-constructions')
rows=json.loads((H/'data/middle-ancestry.json').read_text())['rows'];out=[];seen=set()
for row in rows:
    if row['middle_class'] in seen:continue
    seen.add(row['middle_class']);p=row['middle_vertices'];profiles=[]
    ds=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    for k in range(8):
        cuts=[i for i,d in enumerate(ds) if d==k];stops=[-1]+cuts+[len(p)-1]
        profiles.append({'coordinate':k,'crossings':len(cuts),'component_edges':[b-a-1 for a,b in zip(stops,stops[1:])]})
    profiles.sort(key=lambda x:x['crossings']);rec={'middle_class':row['middle_class'],'edges':len(p)-1,'profiles':profiles};out.append(rec)
    print(rec['middle_class'],rec['edges'],profiles[:2])
(H/'data/middle-face-profiles.json').write_text(json.dumps(out,indent=2)+'\n')
(H/'scripts/middle_profiles.py').write_bytes(Path(__file__).read_bytes())
