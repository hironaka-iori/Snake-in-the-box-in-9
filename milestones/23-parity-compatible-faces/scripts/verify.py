"""Audit search scopes, coverage, controls and Lean target-selection proofs."""
import json,sys
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/19-coordinate-face-repair/scripts'))
from search_faces import faces,sha
from opposite_cells import regions,check
def main():
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    p=json.loads(source.read_text())['path_vertices'];check(p);occupied=set(p);summary={}
    for path in sorted((HERE/'data').glob('faces*.json')):
        d=json.loads(path.read_text())
        assert d['source_sha256_lf']==sha(source)
        assert d['script_sha256_lf']==sha(ROOT/'milestones/19-coordinate-face-repair/scripts/search_faces.py')
        assert d['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
        expected=faces(d['dimension']);seen=set()
        for r in d['faces']:
            i=r['index'];assert i not in seen;seen.add(i)
            assert all(r[k]==v for k,v in expected[i].items())
            inside={v for v in range(512) if v&r['fixed_mask']==r['fixed_value']}
            assert r['selected_inside']==len(inside&occupied)
            if 'path_vertices' in r:
                q=r['path_vertices'];check(q)
                assert len(q)==d['target_edges']+1 and set(q)^occupied<=inside
        assert len(d['faces'])==d['requested_faces']
        if 'retry' not in path.name:assert seen==set(range(len(expected)))
        summary[path.name]=dict(Counter(r['status'] for r in d['faces']))
    expected=list(regions());assert len(expected)==1008
    for path in sorted((HERE/'data').glob('opposite*.json')):
        d=json.loads(path.read_text())
        assert d['script_sha256_lf']==sha(HERE/'scripts/opposite_cells.py')
        assert d['source_sha256_lf']==sha(source) and d['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
        for r in d['regions']:
            assert all(r[k]==v for k,v in expected[r['index']].items())
            inside={v for v in range(512) if v&r['fixed_mask'] in r['values']}
            assert len(inside)==64 and len(occupied&inside)==r['selected_inside']
            assert all(any((v>>k&1)!=(min(inside)>>k&1) for v in inside) for k in range(9))
            if 'path_vertices' in r:
                q=r['path_vertices'];check(q);assert len(q)==d['target_edges']+1 and set(q)^occupied<=inside
        if d['target_edges']==193:
            assert d['complete'] and [r['index'] for r in d['regions']]==list(range(1008))
        else:assert d['regions'][0]['status']=='OPTIMAL'
        summary[path.name]=dict(Counter(r['status'] for r in d['regions']))
    log=(HERE/'logs/targets.log').read_text(encoding='utf-8-sig')
    assert 'sorryAx' not in log and 'error:' not in log and log.count('depends on axioms:')==4
    inventory=json.loads((HERE/'data/boundary-inventory.json').read_text())
    assert inventory['script_sha256_lf']==sha(HERE/'scripts/boundary_inventory.py')
    for row in inventory['rows']:
        inside={v for v in range(512) if v&row['fixed_mask']==row['fixed_value']}
        flat=[v for component in row['outside_components'] for v in component]
        assert len(flat)==len(set(flat)) and set(flat)==occupied-inside
        for component in row['outside_components']:check(component)
        component_edges={tuple(sorted((v,w))) for component in row['outside_components'] for v,w in zip(component,component[1:])}
        actual_edges={(v,w) for v in flat for w in flat if v<w and (v^w).bit_count()==1}
        assert component_edges==actual_edges
        internal={v for component in row['outside_components'] for v in component[1:-1]}
        forbidden={v for v in inside if any((v^w).bit_count()==1 for w in internal)}
        assert sorted(forbidden)==row['forbidden_inside'] and not (forbidden&occupied)
        assert row['contracted_model_vertices']==len(inside-forbidden)+len(flat)-len(internal)
    files=[p for f in ['scripts','lean','logs','data'] for p in (HERE/f).glob('*') if p.is_file() and p.name!='verification.json']
    report={'status':'PASSED','search_outcomes':summary,'lean_audits':4,'scope':'Search coverage, hashes, feasible controls and boundary inventory; solver exclusions are not Lean-certified. Lean proofs concern target selection and exclusion of a third neighbor, not the unimplemented contraction model.','sha256_lf':{p.relative_to(ROOT).as_posix():sha(p) for p in files}}
    (HERE/'data/verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='sha256_lf'},indent=2))
if __name__=='__main__':main()
