"""Audit saved search witnesses, provenance, finite controls and Lean receipt."""
import json,re
from pathlib import Path
from contracted import ROOT,HERE,sha
def pair_check(p,n):
    assert len(set(p))==len(p) and all(0<=v<2**n for v in p)
    for i in range(len(p)):
        for j in range(i+1,len(p)):
            assert ((p[i]^p[j]).bit_count()==1)==(j==i+1)
def main():
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    inventory=ROOT/'milestones/23-parity-compatible-faces/data/boundary-inventory.json'
    seed=json.loads(source.read_text())['path_vertices'];pair_check(seed,9)
    faces={r['face_index']:r for r in json.loads(inventory.read_text())['rows']}
    counts={}
    for filename,script in [('max-search.json','contracted.py'),('strengthened-search.json','strengthened.py')]:
        report=json.loads((HERE/'data'/filename).read_text())
        assert report['script_sha256_lf']==sha(HERE/'scripts'/script)
        assert report['source_sha256_lf']==sha(source)
        assert report['inventory_sha256_lf']==sha(inventory)
        if 'model_sha256_lf' in report:assert report['model_sha256_lf']==sha(HERE/'scripts/contracted.py')
        for kind in ('controls','runs'):
            rows=report[kind];assert len(rows)==10 and {r['face_index'] for r in rows}==set(faces)
            for r in rows:
                f=faces[r['face_index']]
                inside={v for v in range(512) if v&f['fixed_mask']==f['fixed_value']}
                outside=set(seed)-inside
                components=r['components'];flat=[v for c in components for v in c]
                assert len(flat)==len(set(flat)) and set(flat)==outside
                actual={frozenset((v,w)) for v in outside for w in outside if v<w and (v^w).bit_count()==1}
                described={frozenset(e) for c in components for e in zip(c,c[1:])}
                assert actual==described
                internal={v for c in components for v in c[1:-1]}
                forbidden={v for v in inside if any((v^w).bit_count()==1 for w in internal)}
                assert r['contracted_internal_vertices']==len(internal)
                assert r['forbidden_inside']==len(forbidden)
                assert r['model_vertices']==len(inside-forbidden)+len(outside-internal)
                p=r['path_vertices'];pair_check(p,9)
                assert set(p)-inside==outside
                assert len(p)-1==r['edges']
                assert [v for v in p if v not in internal]==r['compressed_path']
                assert len(p)==len(r['compressed_path'])+len(internal)
                if kind=='controls':assert r['status']=='OPTIMAL' and r['edges']==191
                if 'short_cycle_cuts' in r:
                    import strengthened
                    assert r['short_cycle_cuts']==strengthened.build(9,seed,inside)[-1]['short_cycle_cuts']
        counts[filename]=len(report['runs'])
    for filename,script in [('small-controls.json','small_controls.py'),('strengthened-controls.json','strengthened.py')]:
        r=json.loads((HERE/'data'/filename).read_text())
        assert r['status']=='PASSED' and len(r['cases'])==592
        assert r['script_sha256_lf']==sha(HERE/'scripts'/script)
        assert r['model_sha256_lf']==sha(HERE/'scripts/contracted.py')
        assert all(c['oracle_edges']==c['model_edges'] for c in r['cases'])
        if 'oracle_sha256_lf' in r:assert r['oracle_sha256_lf']==sha(HERE/'scripts/small_controls.py')
    lean=(HERE/'logs/rigidity.log').read_text(encoding='utf-8-sig')
    assert 'sorryAx' not in lean and 'error:' not in lean
    audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",lean)
    assert len(audits)==5
    for _,axioms in audits:assert set(axioms.split(', '))<={'propext','Classical.choice','Quot.sound'}
    report={'status':'PASSED','searches':counts,'checked_saved_paths':40,'finite_control_cases':1184,
        'lean_axiom_audits':5,'files_sha256_lf':{
            str(p.relative_to(HERE)).replace('\\','/'):sha(p)
            for folder in ['scripts','lean','data','logs'] for p in sorted((HERE/folder).glob('*'))
            if p.is_file() and p.name!='verification.json'},
        'scope':'Independent pair, membership, component and arithmetic checks of saved witnesses; source hashes and receipts. Small-cube optimality controls are finite computations. Complete solver encoding equivalence is not Lean-checked.'}
    (HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='files_sha256_lf'},indent=2))
if __name__=='__main__':main()
