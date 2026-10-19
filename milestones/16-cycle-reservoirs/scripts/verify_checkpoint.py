"""Independent audits for merger experiments, larger base sets, and local tables."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
OLD=ROOT/'milestones/15-component-mergers'
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def adj(a,b):return (a^b).bit_count()==1
def path_check(path):
    assert len(path)==len(set(path)) and all(0<=v<512 for v in path)
    for j,v in enumerate(path):
        for i,w in enumerate(path[:j]):assert adj(v,w)==(i+1==j)


def main():
    out={'status':'PASSED','scope':'Feasible witnesses, model bookkeeping, and local-table row validity; no solver UNSAT or table-completeness certificate.',
         'mergers':{},'base_pairs':{},'dense_seeds':{},'lean_audits':{},'sha256_lf':{}}
    versions={sha(p)for p in [OLD/'scripts/merge_components.py',*sorted((OLD/'scripts/snapshots').glob('*.py'))]}
    for p in sorted((OLD/'data').glob('*.json')):
        d=json.loads(p.read_text())
        if 'target_path_edges'not in d:continue
        source=ROOT/d['source'];assert sha(source)==d['source_sha256_lf']
        assert d['script_sha256_lf']in versions
        seed=json.loads(source.read_text());frozen=set(d['frozen_vertices'])
        forbidden=frozen|{v^(1<<k)for v in frozen for k in range(9)}
        assert d['allowed_vertices']==512-len(forbidden)
        assert d['target_path_edges']==196-len(frozen)
        assert frozen<=set(seed['seed_vertices'])
        assert all(sum(adj(v,w)for w in frozen)==2 for v in frozen)
        if 'path_vertices'in d:
            path=d['path_vertices'];path_check(path)
            assert len(path)==d['target_path_edges']+1 and not set(path)&forbidden
            selected=frozen|set(path)
            assert sorted(selected)==d['seed_vertices'] and len(selected)==197
            retained=d.get('retained_path_vertices',seed['path_vertices'] if d['keep_original_path']else [])
            assert set(retained)<=set(path)
            assert all(not set(c)<=selected for c in d['retained_cuts'])
        out['mergers'][p.name]={k:d[k]for k in ('status','target_path_edges','allowed_vertices','seconds')}
    for p in sorted((HERE/'data').glob('base*.json')):
        d=json.loads(p.read_text());assert d['source_sha256_lf']==sha(HERE/'scripts/probe_base_pairs.py')
        if 'base_sets'in d:
            a,b=map(set,d['base_sets']);assert not a&b
            for vs in (a,b):
                assert len(vs)==d['size_per_set'] and all(0<=v<1<<d['n']for v in vs)
                assert all(sum(adj(v,w)for w in vs)==2 for v in vs)
                for v in vs:
                    for i in range(d['n']):
                        for j in range(i):assert not {v,v^(1<<i),v^(1<<j),v^(1<<i)^(1<<j)}<=vs
        out['base_pairs'][p.name]={k:d[k]for k in ('status','n','size_per_set','q9_product_vertices_if_feasible')}
    for p in sorted((HERE/'data').glob('seed*.json')):
        d=json.loads(p.read_text());assert d['script_sha256_lf']==sha(HERE/'scripts/build_dense_seed.py')
        assert sha(ROOT/d['base_source'])==d['base_source_sha256_lf']
        if 'seed_vertices'in d:
            path=d['path_vertices'];path_check(path);frozen=set(d['frozen_vertices'])
            assert len(path)==d['target_path_edges']+1 and not set(path)&frozen
            assert all(not adj(v,w)for v in path for w in frozen)
            assert sorted(frozen|set(path))==d['seed_vertices'] and len(d['seed_vertices'])==197
            assert all(sum(adj(v,w)for w in frozen)==2 for v in frozen)
        out['dense_seeds'][p.name]={k:d[k]for k in ('status','target_path_edges','allowed_vertices','seconds')}
    table=json.loads((HERE/'data/cell-states.json').read_text())
    assert table['port_vertices']==[7,10,16,29]
    for t in table['tables']:
        vertices=t['vertices'];assert len(vertices)==len(set(vertices))==18
        seen=set()
        for row in t['rows']:
            mask,ports,*tail=row
            assert mask not in seen;seen.add(mask)
            assert 0<=mask<1<<18 and ports==mask>>14
            vs=[v for i,v in enumerate(vertices)if mask>>i&1]
            degrees={v:sum(adj(v,w)for w in vs)for v in vs}
            base=[v for v in vertices[:14]if v in degrees]
            assert all(degrees[v]in (1,2)for v in base)
            assert all(d<=2 for d in degrees.values())
            assert tail[:4]==[degrees.get(v,0)for v in vertices[14:]]
            assert tail[4]==sum(degrees[v]==1 for v in base)<=2 and tail[5]==len(vs)
        assert len(seen)==4973
    out['cell_rows_checked']=[len(t['rows'])for t in table['tables']]
    for path,count in ((OLD/'logs/frozen-cycle-cuts.log',2),(HERE/'logs/base-pair.log',9)):
        text=path.read_text(encoding='utf-8');assert 'error:'not in text and 'sorry'not in text
        audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text);assert len(audits)==count
        for theorem,axioms in audits:
            ax={a.strip()for a in axioms.split(',')if a.strip()}
            assert ax<={'propext','Classical.choice','Quot.sound'}
            out['lean_audits'][theorem]=sorted(ax)
    for base in (OLD,HERE):
        for folder in ('scripts','lean','logs','data'):
            for p in sorted((base/folder).rglob('*')):
                if p.is_file()and '__pycache__'not in p.parts and p.name!='verification.json':
                    out['sha256_lf'][p.relative_to(ROOT).as_posix()]=sha(p)
    for relative in ('work/neighborhood_search.py','work/exact_search.py','work/check_snake.py',
                     'work/final_lean/PathStructure.lean','work/spectral/CycleExclusion.lean',
                     'milestones/14-component-construction/lean/CycleCuts.lean'):
        out['sha256_lf'][relative]=sha(ROOT/relative)
    (HERE/'data/verification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':out['status'],'merger_runs':len(out['mergers']),'dense_seed_runs':len(out['dense_seeds']),
        'cell_rows_checked':out['cell_rows_checked'],'lean_audits':len(out['lean_audits'])}))


if __name__=='__main__':main()
