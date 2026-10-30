"""Audit completed certificate chains while retaining pending cases explicitly."""
from pathlib import Path
import ast,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window
import gen_lean_sat as gen
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records={}
for path in (HERE/'logs').glob('build-record*.json'):
    record=read(path)
    for row in record['records']:
        source=HERE/'lean'/(row['module']+'.lean')
        if row['exit_code']==0 and source.exists() and sha(source)==row['source_sha256']:
            compiled=Path(record['build'])/(row['module']+'.olean')
            if compiled.exists():records[row['module']]=row
cases=read(HERE/'data/cases.json');completed=[];pending=[]
def cnf(path):return [list(map(int,line.split()))[:-1] for line in path.read_text().splitlines() if line and not line.startswith(('p','c'))]
for c in cases:
    n=c['number'];mod=f'CycleWindow{n}';name=f'cycle{n}'
    if f'FourCount{n}' not in records:pending.append(n);continue
    sources=[p for p in (HERE/'lean').rglob('*.lean') if mod in p.as_posix() or p.stem in (f'CycleExclusion{n}',f'FourCount{n}') or (n==7218 and p.stem=='ReturningDirection') or (n==7219 and p.stem=='ReturningDirectionStrong')]
    audits=[];source_hashes={}
    for p in sources:
        module=p.relative_to(HERE/'lean').with_suffix('').as_posix();assert module in records
        text=p.read_text(encoding='utf-8-sig');assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
        source_hashes[module]=sha(p)
        logpath=HERE/'logs'/(module.replace('/','-')+'.log')
        log=logpath.read_text(encoding='utf-8') if logpath.exists() else ''
        assert 'error:' not in log and 'sorryAx' not in log
        checks=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
        checks += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
        assert len(checks)==len(re.findall(r'^#print axioms ',text,re.M))
        for theorem,axioms in checks:
            assert set(re.findall(r'[A-Za-z][\w.]*',axioms))<={'propext','Classical.choice','Quot.sound'}
            audits.append(theorem)
    assert len(audits)>=3
    meta=read(HERE/f'data/{name}.json');e=TaggedEncoding(window(c['dirs']),c['bounds'],radius=4)
    assert meta['dirs']==c['dirs'] and meta['bounds']==c['bounds']
    for cycle in meta['cycle_cuts']:
        assert gen.is_cycle_set(cycle) and set(cycle)<=e.B
        e.add([-e.var[v] for v in cycle],('cut',))
    assert e.clauses==cnf(HERE/f'certificates/{name}.full.cnf')
    rename={int(k):v for k,v in meta['original_to_new'].items()}
    core=[[(-1 if v<0 else 1)*rename[abs(v)] for v in e.clauses[j-1]] for j in meta['source_original_clause_ids']]
    assert core==cnf(HERE/f'certificates/{name}.cnf')
    text=(HERE/f'lean/LocalWindowCnf/{mod}.lean').read_text()
    raw=ast.literal_eval(text.split('def raw : List (List Nat) := ',1)[1].split('\ndef cnf',1)[0])
    assert raw==[[gen.code(v) for v in clause] for clause in core]
    assert 's VERIFIED' in (HERE/f'logs/{name}-drat-check.txt').read_text()
    export=read(HERE/f'logs/{name}-export.txt');assert export['simulated']
    completed.append(dict(case=n,dirs=c['dirs'],bounds=c['bounds'],modules=len(sources),theorem_audits=audits,hints=export['hints'],source_sha256=source_hashes))
out=dict(status='PASS_COMPLETED_CHAINS',completed_cases=[c['case'] for c in completed],pending_cases=pending,completed=completed,theorem_audits=sum(len(c['theorem_audits']) for c in completed),scope='Completed arbitrary-snake interval exclusions only. Pending cases are not theorems. Imported standard support is reused; final dependency audits restrict axioms to propext, Classical.choice and Quot.sound.')
(HERE/'data/proof-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='completed'},flush=True)
