"""Independently check paths and compare transition words with the bank."""
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def check(p,n=9):
    assert len(p)==len(set(p)) and all(0<=v<2**n for v in p)
    for i,a in enumerate(p):
        for j in range(i+1,len(p)):
            assert ((a^p[j]).bit_count()==1)==(j==i+1)
def word(p):return [(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
def normalize(t):
    names={};out=[]
    for k in t:
        if k not in names:names[k]=len(names)
        out.append(names[k])
    return tuple(out)
def signature(p):
    t=word(p);return min(normalize(t),normalize(t[::-1]))
def mapping(q,p):
    for reverse in (False,True):
        qq=q[::-1] if reverse else q
        if normalize(word(qq))!=normalize(word(p)):continue
        axes={}
        for a,b in zip(word(qq),word(p)):
            assert a not in axes or axes[a]==b
            axes[a]=b
        assert len(set(axes.values()))==len(axes)
        for a,b in zip(sorted(set(range(9))-axes.keys()),sorted(set(range(9))-set(axes.values()))):axes[a]=b
        def perm(v):return sum(((v>>k)&1)<<axes[k] for k in range(9))
        translation=p[0]^perm(qq[0])
        assert [perm(v)^translation for v in qq]==p
        return dict(reverse=reverse,axis_images=[axes[k] for k in range(9)],xor_translation=translation)
    raise AssertionError('No matching coordinate map')
def main():
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    inventory=ROOT/'milestones/23-parity-compatible-faces/data/boundary-inventory.json'
    data=json.loads((HERE/'data/results.json').read_text())
    assert data['script_sha256_lf']==sha(HERE/'scripts/search.py')
    assert data['source_sha256_lf']==sha(source) and data['inventory_sha256_lf']==sha(inventory)
    for name,digest in data['dependencies_sha256_lf'].items():
        assert sha(ROOT/'milestones/24-contracted-face-search/scripts'/name)==digest
    seed=json.loads(source.read_text())['path_vertices'];check(seed)
    faces={r['face_index']:r for r in json.loads(inventory.read_text())['rows']}
    assert {(r['face_index'],r['target_edges']) for r in data['runs']}=={(f,t) for f in [3,0,4,5] for t in [191,190]}
    c=data['controls'];assert c['status']=='PASSED' and len(c['cases'])==608
    assert all((r['status']=='INFEASIBLE' and r['actual'] is None) if r['expected'] is None
        else (r['status']=='OPTIMAL' and r['actual']==r['expected']) for r in c['cases'])
    bankpath=ROOT/'work/bank9.json';bank=json.loads(bankpath.read_text())
    full={};short={}
    for i,r in enumerate(bank):
        q=r['vertex_sequence'];check(q)
        full.setdefault(signature(q),[]).append((i,'full',q))
        for label,p in [('delete_last',q[:-1]),('delete_first',q[1:])]:
            short.setdefault(signature(p),[]).append((i,label,p))
    records=[]
    for phase in ['runs','regrowth']:
        for i,r in enumerate(data[phase]):
            if 'path_vertices' not in r:
                assert r['status'] in ['UNKNOWN','INFEASIBLE'];continue
            p=r['path_vertices'];check(p);f=faces[r['face_index']]
            parent=seed if phase=='runs' else data['runs'][r['parent_run']]['path_vertices']
            inside={v for v in range(512) if v&f['fixed_mask']==f['fixed_value']}
            assert set(p)-inside==set(parent)-inside
            if phase=='runs':
                assert len(p)==r['target_edges']+1
                assert sorted(set(p)-set(seed))==r['new_vertices']
                assert sorted(set(seed)-set(p))==r['removed_vertices']
                assert len(r['new_vertices'])==r['objective_new_vertices']
                assert len(r['removed_vertices'])-len(r['new_vertices'])==191-r['target_edges']
            else:assert len(p)==r['edges']+1
            matches=[]
            for bi,label,q in (full if len(p)==192 else short).get(signature(p),[]):
                matches.append(dict(bank_index=bi,comparison=label,**mapping(q,p)))
            records.append(dict(phase=phase,row=i,edges=len(p)-1,bank_matches=matches))
    eligible=sorted([(i,r) for i,r in enumerate(data['runs']) if r.get('objective_new_vertices',0)>0],
        key=lambda ir:(-ir[1]['objective_new_vertices'],-ir[1]['target_edges']))[:2]
    expected={(i,f) for i,r in eligible for f in [3,0,4,5] if f!=r['face_index']}
    assert {(r['parent_run'],r['face_index']) for r in data['regrowth']}==expected
    protected=json.loads((HERE/'data/protected.json').read_text())
    assert protected['script_sha256_lf']==sha(HERE/'scripts/protected.py')
    assert protected['search_sha256_lf']==sha(HERE/'scripts/search.py')
    assert protected['parent_sha256_lf']==sha(HERE/'data/results.json')
    assert {(r['face_index'],r['target_edges']) for r in protected['runs']}=={
        (f,t) for f in [0,3,4,5] for t in [191,192]}
    parent=data['runs'][protected['parent_run']]['path_vertices']
    assert parent==[12]+data['runs'][4]['path_vertices'][2:]
    for i,r in enumerate(protected['runs']):
        if 'path_vertices' not in r:
            assert r['status'] in ['INFEASIBLE','UNKNOWN'];continue
        p=r['path_vertices'];check(p)
        assert protected['protected_vertex'] in p and len(p)==r['target_edges']+1
        f=faces[r['face_index']]
        inside={v for v in range(512) if v&f['fixed_mask']==f['fixed_value']}
        assert set(p)-inside==set(parent)-inside
        records.append(dict(phase='protected',row=i,edges=len(p)-1))
    pc=json.loads((HERE/'data/protected-controls.json').read_text())
    assert pc['status']=='PASSED' and len(pc['cases'])==256
    assert pc['script_sha256_lf']==sha(HERE/'scripts/protected_controls.py')
    assert pc['protected_sha256_lf']==sha(HERE/'scripts/protected.py')
    assert pc['search_sha256_lf']==sha(HERE/'scripts/search.py')
    assert all((r['status']=='INFEASIBLE' and r['actual'] is None) if r['expected'] is None
        else (r['status']=='OPTIMAL' and r['actual']==r['expected']) for r in pc['cases'])
    log=(HERE/'logs/diversity.log').read_text(encoding='utf-8-sig')
    assert 'sorryAx' not in log and 'error:' not in log
    audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    assert len(audits)==3
    for _,a in audits:assert set(a.split(', '))<={'propext','Classical.choice','Quot.sound'}
    out=dict(status='PASSED',small_cube_controls=608,protected_vertex_controls=256,
        verified_saved_paths=len(records),endpoint_substitution_verified=True,
        lean_audits=3,bank_sha256_lf=sha(bankpath),classifications=records,
        scope='Finite path and coordinate-map verification. Nonmatches refer only to full bank snakes or their two endpoint truncations. No claim of novelty beyond that comparison.',
        files_sha256_lf={str(p.relative_to(HERE)).replace('\\','/'):sha(p)
            for folder in ['scripts','lean','data','logs'] for p in sorted((HERE/folder).glob('*')) if p.is_file()})
    (HERE/'verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['files_sha256_lf','classifications']},indent=2))
if __name__=='__main__':main()
