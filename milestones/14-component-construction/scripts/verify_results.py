"""Audit component-search outputs, cycle cuts, proof logs, and source identity."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def main():
    versions=[HERE/'scripts/component_search.py',*sorted((HERE/'scripts/snapshots').glob('*.py'))]
    identities={sha(p):p.relative_to(ROOT).as_posix() for p in versions}
    report={'status':'PASSED','scope':'Saved feasible sets and witnesses checked independently; no UNSAT or completeness claim.',
            'runs':{},'lean_audits':{},'sha256_lf':{}}
    for p in sorted((HERE/'data').glob('*.json')):
        if p.name=='verification.json':continue
        report['sha256_lf'][p.relative_to(ROOT).as_posix()]=sha(p)
        d=json.loads(p.read_text())
        if 'rounds' not in d:
            if 'cuts_to_retain' in d:
                source=ROOT/d['source']
                assert sha(source)==d['source_sha256_lf']
                original=json.loads(source.read_text())
                solved=[r for r in original['rounds'] if 'selected_vertices' in r]
                assert d['seed_vertices']==solved[-1]['selected_vertices']
                assert d['cuts_to_retain']==[c for r in solved for c in r['added_cycle_cuts']]
                path=d['path_vertices']
                assert len(path)==len(set(path))==41 and set(path)<=set(d['seed_vertices'])
                for j,v in enumerate(path):
                    for i,w in enumerate(path[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
            continue
        assert d['source_sha256_lf'] in identities
        oldcuts=[]
        for row in d['rounds']:
            if 'selected_vertices' not in row:continue
            vs=row['selected_vertices'];selected=set(vs)
            assert len(vs)==len(selected)==d['target_edges']+1
            assert all(0<=v<1<<d['n'] for v in vs)
            adj={v:{w for w in vs if (v^w).bit_count()==1} for v in vs}
            assert all(len(a)in (1,2) for a in adj.values())
            ends={v for v in vs if len(adj[v])==1}
            assert len(ends)==2 and 0 in ends and adj[0]=={1}
            assert all(not c<=selected for c in oldcuts)
            parts=row['components']
            flat=[v for c in parts for v in c]
            assert len(flat)==len(set(flat)) and set(flat)==selected
            for c in parts:
                seen=set();todo=[c[0]]
                while todo:
                    v=todo.pop()
                    if v in seen:continue
                    seen.add(v);todo.extend(adj[v])
                assert seen==set(c)
            for cycle in row['added_cycle_cuts']:
                c=set(cycle)
                assert c and c<=selected and all(len(adj[v]&c)==2 for v in c)
                oldcuts.append(c)
        if 'witness'in d:
            path=d['witness']
            assert len(path)==len(set(path))==d['target_edges']+1
            for j,v in enumerate(path):
                for i,w in enumerate(path[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
        report['runs'][p.name]={'status':d['status'],'rounds':len(d['rounds']),
            'cycle_cuts':len(oldcuts),'source_version':identities[d['source_sha256_lf']]}
    for name in ('cycle-cuts.log','seed-certificate.log'):
        p=HERE/'logs'/name;text=p.read_text(encoding='utf-8')
        assert 'error:' not in text and 'sorry' not in text
        rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
        assert len(rows)==(3 if name=='cycle-cuts.log' else 5)
        for theorem, axioms in rows:
            ax={a.strip() for a in axioms.split(',') if a.strip()}
            assert ax <= {'propext','Classical.choice','Quot.sound'}
            report['lean_audits'][theorem]=sorted(ax)
    for folder in ('scripts','lean','logs'):
        for p in sorted((HERE/folder).rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts:
                report['sha256_lf'][p.relative_to(ROOT).as_posix()]=sha(p)
    for relative in ('work/spectral/CycleExclusion.lean','work/neighborhood_search.py','work/check_snake.py'):
        report['sha256_lf'][relative]=sha(ROOT/relative)
    (HERE/'data/verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':report['status'],'runs':report['runs'],'lean_audits':len(report['lean_audits'])},indent=2))


if __name__=='__main__':main()
