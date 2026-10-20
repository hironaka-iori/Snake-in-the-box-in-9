"""Describe fixed outside path components in unresolved Q8 face searches."""
import json
from pathlib import Path
from opposite_cells import ROOT,HERE
from search_faces import sha
def run():
    seed=json.loads((ROOT/'milestones/18-expanded-cells/data/aligned-seed.json').read_text())['path_vertices']
    first=json.loads((HERE/'data/faces8-192.json').read_text())
    second=json.loads((HERE/'data/faces8-193.json').read_text())
    rows=[]
    for r,t in zip(first['faces'],second['faces']):
        assert r['index']==t['index']
        if r['status']!='UNKNOWN' and t['status']!='UNKNOWN':continue
        inside={v for v in range(512) if v&r['fixed_mask']==r['fixed_value']}
        outside=set(seed)-inside
        neighbors={v:[w for w in outside if (v^w).bit_count()==1] for v in outside}
        unseen=set(outside);components=[]
        while unseen:
            start=min(v for v in unseen if len(neighbors[v])<=1);path=[start];unseen.remove(start)
            while True:
                nxt=[w for w in neighbors[path[-1]] if w in unseen]
                if not nxt:break
                assert len(nxt)==1;path+=nxt;unseen.remove(nxt[0])
            components.append(path)
        internal={v for p in components for v in p[1:-1]}
        forbidden={v for v in inside if any((v^w).bit_count()==1 for w in internal)}
        allowed=inside-forbidden
        retained=outside-internal
        assert not (set(seed)&forbidden)
        rows.append({'face_index':r['index'],'fixed_mask':r['fixed_mask'],'fixed_value':r['fixed_value'],'outside_components':components,'outside_selected':len(outside),'internal_vertices':len(internal),'forbidden_inside':sorted(forbidden),'allowed_inside':len(allowed),'retained_outside':len(retained),'contracted_model_vertices':len(allowed)+len(retained),'target192_status':r['status'],'target193_status':t['status']})
    rows.sort(key=lambda r:(r['contracted_model_vertices'],r['face_index']))
    data={'script_sha256_lf':sha(Path(__file__)),'rows':rows,'scope':'Construction preprocessing inventory only. An outside internal vertex already has two selected outside neighbors, so an inside neighbor cannot be selected. Contracting each fixed outside path is proposed, not yet implemented or validated.'}
    (HERE/'data/boundary-inventory.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps([{k:r[k] for k in ('face_index','outside_selected','internal_vertices','allowed_inside','retained_outside','contracted_model_vertices')} for r in rows],indent=2))
if __name__=='__main__':run()
