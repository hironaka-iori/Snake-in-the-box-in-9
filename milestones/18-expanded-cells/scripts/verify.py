"""Audit transformed witnesses, repair scopes, provenance, and Lean receipts."""
import hashlib
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]

def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def canonical(path):
    def directed(seq):
        labels={};code=[]
        for a,b in zip(seq,seq[1:]):
            direction=(a^b).bit_length()-1
            if direction not in labels:labels[direction]=len(labels)
            code.append(labels[direction])
        return tuple(code)
    return min(directed(path),directed(path[::-1]))

def path_check(path,edges):
    assert len(path)==edges+1 and len(set(path))==len(path)
    assert all(0<=v<512 for v in path)
    for j,v in enumerate(path):
        for i,w in enumerate(path[:j]):assert ((v^w).bit_count()==1)==(i+1==j)

def main():
    bank_path=ROOT/'work/bank9.json';bank=json.loads(bank_path.read_text())
    base_path=ROOT/'milestones/16-cycle-reservoirs/data/base5-size14.json'
    bases=json.loads(base_path.read_text())['base_sets']
    unused=set(range(32))-set(bases[0])-set(bases[1])
    palette={32*h+v for h in range(16) for v in set(bases[h.bit_count()%2])|unused}
    alignment=HERE/'data/bank-alignments.json';d=json.loads(alignment.read_text())
    assert d['bank_sha256_lf']==sha(bank_path) and d['base_sha256_lf']==sha(base_path)
    assert d['script_sha256_lf']==sha(HERE/'scripts/align_bank.py')
    assert len(d['records'])==len(bank)==131
    for r in d['records']:
        inner=r['inner_coordinates'];p=r['path_vertices'];path_check(p,191)
        order=[inner[i] for i in r['inner_permutation']]+[i for i in range(9) if i not in inner]
        assert sorted(order)==list(range(9))
        shift=r['inner_shift']+32*r['outer_shift']
        expected=[]
        for v in bank[r['bank_index']]['vertex_sequence']:
            bits=format(v,'09b')[::-1]
            word=''.join(bits[k] for k in order)[::-1]
            expected.append(int(word,2)^shift)
        assert expected==p
        assert r['outside_vertices']==sorted(set(p)-palette)
        assert r['outside_count']==len(set(p)-palette)
        assert canonical(p)==canonical(bank[r['bank_index']]['vertex_sequence'])
    assert min(r['outside_count'] for r in d['records'])==d['minimum_outside_count']==29
    assert max(r['outside_count'] for r in d['records'])==d['maximum_bank_minimum']==38
    seed_path=HERE/'data/aligned-seed.json';seed=json.loads(seed_path.read_text())
    assert seed['source_sha256_lf']==sha(alignment)
    assert seed['path_vertices']==d['records'][seed['bank_index']]['path_vertices']
    order=[seed['inner_coordinates'][i] for i in seed['inner_permutation']]+[i for i in range(9) if i not in seed['inner_coordinates']]
    lean=(HERE/'lean/Alignment.lean').read_text(encoding='utf-8')
    expected_forward=' + '.join(f'(if n.testBit {i} then {1<<j} else 0)' for j,i in enumerate(order))
    expected_backward=' + '.join(f'(if n.testBit {j} then {1<<i} else 0)' for j,i in enumerate(order))
    assert 'def permute (n : Nat) : Nat := '+expected_forward in lean
    assert 'def inversePermute (n : Nat) : Nat := '+expected_backward in lean
    shift=seed['inner_shift']+32*seed['outer_shift']
    assert f'(permute v.val ^^^ {shift}) % 512' in lean
    assert f'inversePermute (v.val ^^^ {shift}) % 512' in lean
    occupied=set(seed['path_vertices'])
    out={'status':'PASSED','scope':'Witnesses, recorded symmetry transforms, source versions, and Lean map proof. The optimization coverage and solver exclusions are computational, not Lean completeness results.',
         'aligned_witnesses':131,'searches':{},'repairs':{},'sha256_lf':{}}
    for p in sorted((HERE/'data').glob('*.json')):
        r=json.loads(p.read_text())
        if 'driver_sha256_lf' not in r:continue
        assert r['driver_sha256_lf']==sha(HERE/'scripts/search.py')
        assert r['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
        assert r['seed_sha256_lf']==sha(seed_path)
        assert r['table_sha256_lf']==sha(ROOT/'milestones/16-cycle-reservoirs/data/cell-states.json')
        assert r['cut_source_sha256_lf']==sha(ROOT/'milestones/17-global-cell-construction/data/cycle-control.json')
        if 'path_vertices' in r:
            path_check(r['path_vertices'],r['target_edges']);selected=set(r['path_vertices'])
            assert sorted(selected-palette)==r['outside_vertices']
            assert len(selected-palette)<=r['max_outside']
            assert sorted(occupied-selected)==r['removed_vertices']
            assert len(occupied-selected)<=r['max_removed']
            assert sorted(selected-occupied)==r['added_vertices']
        out['searches'][p.name]=r['status']
    versions={sha(p) for p in [HERE/'scripts/repair_cells.py',*sorted((HERE/'scripts/snapshots').glob('*.py'))]}
    for p in sorted((HERE/'data').glob('*.json')):
        r=json.loads(p.read_text())
        if 'regions' not in r:continue
        assert r['source_sha256_lf']==sha(seed_path) and r['script_sha256_lf'] in versions
        assert r['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
        for region in r['regions']:
            if 'path_vertices' in region:
                path_check(region['path_vertices'],r['target_edges'])
                selected=set(region['path_vertices'])
                assert all(v>>5 in region['cells'] for v in selected^occupied)
                if r.get('different_vertex_set',False):assert selected!=occupied
        out['repairs'][p.name]=dict((status,sum(t['status']==status for t in r['regions'])) for status in {t['status'] for t in r['regions']})
    neutral=json.loads((HERE/'data/neutral-pair.json').read_text())['regions'][-1]['path_vertices']
    matches=[i for i,r in enumerate(bank) if canonical(neutral)==canonical(r['vertex_sequence'])]
    comparison={'changed_cells':[0,2],'removed_vertices':sorted(occupied-set(neutral)),
                'added_vertices':sorted(set(neutral)-occupied),'matching_bank_indices':matches,
                'same_symmetry_class_as_input':canonical(neutral)==canonical(seed['path_vertices']),
                'scope':'Canonical transition sequence under translation, coordinate permutation and path reversal; no novelty beyond the bank is claimed.'}
    assert matches==[127] and not comparison['same_symmetry_class_as_input']
    (HERE/'data/neutral-comparison.json').write_text(json.dumps(comparison,indent=2)+'\n',encoding='utf-8',newline='\n')
    log=(HERE/'logs/alignment.log').read_text(encoding='utf-8')
    assert 'error:' not in log and 'sorryAx' not in log
    audits=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    none=re.findall(r"'([^']+)' does not depend on any axioms",log)
    assert len(audits)+len(none)==7
    assert all(set(a.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in audits)
    out['lean_audits']=[n for n,_ in audits]+none
    assert out['searches']['control191.json']=='OPTIMAL'
    assert out['searches']['control-budget28.json']=='INFEASIBLE'
    for p in sorted(HERE.rglob('*')):
        if p.is_file() and p.suffix in ('.py','.lean','.json','.log') and p.name!='verification.json':
            out['sha256_lf'][p.relative_to(ROOT).as_posix()]=sha(p)
    (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':'PASSED','aligned_witnesses':131,'searches':len(out['searches']),
                      'repairs':out['repairs'],'lean_audits':len(out['lean_audits'])}))

if __name__=='__main__':main()
