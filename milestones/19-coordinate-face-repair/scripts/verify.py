"""Independently audit face coverage, repair witnesses and the compressed graph."""
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def adjacent(v,w):return (v^w).bit_count()==1
def check(path):
    assert len(path)==len(set(path)) and all(0<=v<512 for v in path)
    for j,v in enumerate(path):
        for i,w in enumerate(path[:j]):assert adjacent(v,w)==(i+1==j)

def canonical(path):
    codes=[]
    for p in (path,path[::-1]):
        order=[];code=[]
        for v,w in zip(p,p[1:]):
            direction=(v^w).bit_length()-1
            if direction not in order:order.append(direction)
            code.append(order.index(direction))
        codes.append(tuple(code))
    return min(codes)

def main():
    source=ROOT/'milestones/18-expanded-cells/data/aligned-seed.json'
    seed=json.loads(source.read_text())['path_vertices'];occupied=set(seed)
    versions={sha(p) for p in [HERE/'scripts/search_faces.py',HERE/'scripts/two_arms.py',*sorted((HERE/'scripts/snapshots').glob('*.py'))]}
    result={'status':'PASSED','scope':'Face enumeration, witness checks, compressed-graph bookkeeping, source hashes and Lean receipts; solver UNSAT claims are not kernel certificates.',
            'face_searches':{},'two_arm_searches':{},'sha256_lf':{}}
    allfaces={}
    for d in (6,7):
        # Enumerate fixed bit masks and their submasks, independently of the
        # search driver's free-coordinate ordering.
        expected=set()
        for mask in range(512):
            if mask.bit_count()!=9-d:continue
            for value in range(512):
                if value&~mask==0:expected.add((mask,value))
        assert len(expected)=={6:672,7:144}[d]
        allfaces[d]=expected
    for p in sorted((HERE/'data').glob('*.json')):
        data=json.loads(p.read_text())
        if 'faces' not in data:continue
        assert data['source_sha256_lf']==sha(source)
        assert data['script_sha256_lf'] in versions
        assert data['model_sha256_lf']==sha(ROOT/'work/neighborhood_search.py')
        pairs=[]
        for r in data['faces']:
            mask,value=r['fixed_mask'],r['fixed_value'];pairs.append((mask,value))
            assert (mask,value) in allfaces[data['dimension']]
            assert r['free_coordinates']==[k for k in range(9) if not mask>>k&1]
            inside={v for v in range(512) if all((v>>k&1)==(value>>k&1) for k in range(9) if mask>>k&1)}
            assert len(inside)==2**data['dimension']
            assert r['selected_inside']==len(occupied&inside)
            assert r['endpoints_inside']==sum(v in inside for v in [seed[0],seed[-1]])
            if 'path_vertices' in r:
                path=r['path_vertices'];check(path)
                assert len(path)==data['target_edges']+1 and set(path)^occupied<=inside
        assert len(pairs)==len(set(pairs))
        assert dict(Counter(r['status'] for r in data['faces']))==data['status_counts']
        if data['requested_faces']==len(allfaces[data['dimension']]):assert set(pairs)==allfaces[data['dimension']]
        else:assert len(pairs)==data['requested_faces']
        result['face_searches'][p.name]=data['status_counts']
    fixed=seed[50:];check(fixed)
    roots=[53,44]
    allowed=sorted(v for v in range(128) if all(not adjacent(v,w) for w in fixed[1:-1]))
    assert len(allowed)==78 and sum(adjacent(v,w) for i,v in enumerate(allowed) for w in allowed[:i])==147
    for w,r in zip([fixed[0],fixed[-1]],roots):assert [v for v in range(128) if adjacent(v,w)]==[r]
    for p in sorted((HERE/'data').glob('two-arm*.json')):
        data=json.loads(p.read_text())
        if 'required_inside_vertices' not in data:continue
        assert data['source_sha256_lf']==sha(source) and data['script_sha256_lf'] in versions
        assert data['fixed_path']==fixed and data['roots']==roots and data['allowed_inside']==allowed
        assert data['required_inside_vertices']==data['target_edges']+1-len(fixed)
        if 'path_vertices' in data:
            path=data['path_vertices'];check(path);c=data['compressed_path']
            assert len(c)==len(set(c)) and set(c)<=set(allowed) and set(roots)<=set(c)
            for j,v in enumerate(c):
                for i,w in enumerate(c[:j]):assert (adjacent(v,w) or {v,w}==set(roots))==(i+1==j)
            expanded=[c[0]]
            for v,w in zip(c,c[1:]):
                if [v,w]==roots:expanded.extend(fixed)
                elif [w,v]==roots:expanded.extend(fixed[::-1])
                expanded.append(w)
            assert path==expanded and len(path)==len(c)+142
            assert set(path)^occupied<=set(range(128))
            if data.get('maximize',False):assert len(path)<=data['target_edges']+1
            else:assert len(path)==data['target_edges']+1
        result['two_arm_searches'][p.name]={'status':data['status'],'actual_edges':len(data['path_vertices'])-1 if 'path_vertices' in data else None}
    fresh=json.loads((HERE/'data/two-arm-seed186.json').read_text())
    growth=json.loads((HERE/'data/two-arm-growth.json').read_text())
    assert fresh['source_sha256_lf']==sha(HERE/'data/two-arm-growth.json')
    assert fresh['seed_vertices']==fresh['path_vertices']==growth['path_vertices']
    assert fresh['edges']==186 and len(fresh['path_vertices'])==187
    bank=json.loads((ROOT/'work/bank9.json').read_text());key=canonical(fresh['path_vertices'])
    matches=[{'bank_index':i,'start_vertex_index':j} for i,r in enumerate(bank)
             for j in range(len(r['vertex_sequence'])-187+1)
             if canonical(r['vertex_sequence'][j:j+187])==key]
    assert matches==fresh['matching_bank_subpaths']==[]
    result['reusable_seed_edges']=186
    log=(HERE/'logs/face-repair.log').read_text(encoding='utf-8')
    assert 'error:' not in log and 'sorryAx' not in log
    audits=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    assert len(audits)==8 and all(set(a.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in audits)
    result['lean_audits']=[n for n,_ in audits]
    for p in sorted(HERE.rglob('*')):
        if p.is_file() and p.suffix in ('.py','.lean','.log','.json') and p.name!='verification.json':
            result['sha256_lf'][p.relative_to(ROOT).as_posix()]=sha(p)
    (HERE/'data/verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':'PASSED','face_searches':len(result['face_searches']),
                      'two_arm_searches':result['two_arm_searches'],'lean_audits':len(audits)}))

if __name__=='__main__':main()
