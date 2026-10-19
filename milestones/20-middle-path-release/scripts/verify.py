"""Audit growth chains, fixed-endpoint witnesses, source hashes and Lean receipts."""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def check(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p)
    for j,v in enumerate(p):
        for i,w in enumerate(p[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
def canonical(p):
    codes=[]
    for q in (p,p[::-1]):
        order=[];code=[]
        for a,b in zip(q,q[1:]):
            k=(a^b).bit_length()-1
            if k not in order:order.append(k)
            code.append(order.index(k))
        codes.append(tuple(code))
    return min(codes)

def main():
    original=ROOT/'milestones/19-coordinate-face-repair/data/two-arm-seed186.json'
    seed=json.loads(original.read_text())['path_vertices']
    middle=json.loads((ROOT/'milestones/19-coordinate-face-repair/data/two-arm-growth.json').read_text())['fixed_path']
    versions={sha(p) for p in [HERE/'scripts/grow.py',*sorted((HERE/'scripts/snapshots').glob('*.py'))]}
    result={'status':'PASSED','scope':'Witnesses, local replacement scopes, finite bank comparison and Lean audits; solver exclusions are not kernel certificates.',
            'growth':{},'fixed_search':{},'sha256_lf':{}}
    for file in sorted((HERE/'data').glob('*growth*.json')):
        d=json.loads(file.read_text());assert d['source_sha256_lf']==sha(original)
        assert d['script_sha256_lf'] in versions and d['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
        assert d['face_driver_sha256_lf']==sha(ROOT/'milestones/19-coordinate-face-repair/scripts/search_faces.py')
        assert d['initial_path']==seed;current=seed;steps=[]
        for p in d['passes']:
            assert p['starting_edges']==len(current)-1
            assert p['target_edges']==min(196,len(current)-1+d.get('step',1))
            seen=set()
            for r in p['trials']:
                mask,value=r['fixed_mask'],r['fixed_value']
                assert (mask,value) not in seen;seen.add((mask,value))
                assert mask.bit_count()==9-d['dimension'] and value&~mask==0
                assert r['free_coordinates']==[k for k in range(9) if not mask>>k&1]
            if 'path_vertices' in p:
                new=p['path_vertices'];check(new);assert len(new)==p['target_edges']+1
                final=p['trials'][-1];mask,value=final['fixed_mask'],final['fixed_value']
                assert all(v&mask==value for v in set(current)^set(new))
                assert p['removed_vertices']==sorted(set(current)-set(new))
                assert p['added_vertices']==sorted(set(new)-set(current))
                assert p['original_middle_removed']==sorted(set(middle)-set(new))
                if d.get('fixed_endpoints',False):assert {new[0],new[-1]}=={current[0],current[-1]}
                current=new;steps.append(len(new)-1)
        assert d['path_vertices']==current and d['best_edges']==len(current)-1
        result['growth'][file.name]={'accepted_lengths':steps,'best_edges':len(current)-1,
            'last_pass_counts':dict(Counter(r['status'] for r in d['passes'][-1]['trials']))}
    growth=json.loads((HERE/'data/growth6.json').read_text());bank=json.loads((ROOT/'work/bank9.json').read_text())
    matches=[i for i,r in enumerate(bank) if canonical(r['vertex_sequence'])==canonical(growth['path_vertices'])]
    assert matches==[127];result['final_growth_bank_matches']=matches
    core=ROOT/'work/final_lean/Snake9.lean';paired=HERE/'data/paired-seed190.json';d=json.loads(paired.read_text())
    assert d['source_core_sha256_lf']==sha(core)
    values=ast.literal_eval('['+re.search(r'def witnessValues : Array Nat := #\[(.*?)\]',core.read_text()).group(1)+']')
    order=d['output_bit_sources'];shift=d['translation']
    expected=[sum(((v>>k)&1)<<j for j,k in enumerate(order))^shift for v in values[:191]]
    assert d['path_vertices']==d['seed_vertices']==expected;check(expected)
    assert len(expected)==191 and expected[0]==41 and expected[-1]==67
    lean=(HERE/'lean/PairedSeed.lean').read_text(encoding='utf-8')
    expression=' + '.join(f'(if n.testBit {k} then {1<<j} else 0)' for j,k in enumerate(order))
    assert 'def permute (n : Nat) : Nat := '+expression in lean
    assert f'(permute v.val ^^^ {shift}) % 512' in lean
    for file in sorted((HERE/'data').glob('fixed-*.json')):
        r=json.loads(file.read_text())
        assert r['source_sha256_lf']==sha(paired) and r['script_sha256_lf']==sha(HERE/'scripts/fixed_search.py')
        assert r['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
        if 'path_vertices' in r:
            p=r['path_vertices'];check(p);assert len(p)==r['target_edges']+1 and [p[0],p[-1]]==[41,67]
            assert len(set(expected)-set(p))<=r['removed_budget']
        result['fixed_search'][file.name]=r['status']
    direct=json.loads((HERE/'data/direct196.json').read_text())
    assert direct['source_sha256_lf']==sha(original) and direct['script_sha256_lf']==sha(HERE/'scripts/direct.py')
    assert direct['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
    if 'witness' in direct:
        check(direct['witness']);assert len(direct['witness'])==197
    result['direct196_status']=direct['status']
    result['lean_audits']={}
    for name,count in [('paired-seed',10),('parity',4),('endpoint-parity',2)]:
        log=(HERE/f'logs/{name}.log').read_text(encoding='utf-8')
        assert 'error:' not in log and 'sorryAx' not in log
        audits=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
        assert len(audits)==count
        assert all(set(a.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in audits)
        result['lean_audits'][name]=[n for n,_ in audits]
    result['dependency_sha256_lf']={str(p.relative_to(ROOT)):sha(p) for p in [core,ROOT/'work/final_lean/DfsParity.lean',ROOT/'milestones/18-expanded-cells/lean/Alignment.lean']}
    for p in sorted(HERE.rglob('*')):
        if p.is_file() and p.suffix in ('.py','.lean','.json','.log') and p.name!='verification.json':
            result['sha256_lf'][p.relative_to(ROOT).as_posix()]=sha(p)
    (HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':'PASSED','growth':result['growth'],'fixed_search':result['fixed_search'],
                      'lean_audits':sum(map(len,result['lean_audits'].values()))}))

if __name__=='__main__':main()
