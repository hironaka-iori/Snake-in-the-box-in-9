"""Check saved probe provenance, cycle cuts and positive-witness audit coverage."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
witness=read(HERE/'data/witness-audit.json');verified={x['probe']:x for x in witness['witnesses']}
rows=[]
for path in sorted((HERE/'data/probes').glob('*.json')):
    r=read(path);assert r['status'] in ['SAT_LOCAL_WITNESS','UNSAT_UNCERTIFIED','UNKNOWN']
    for p,h in r['source_files_sha256'].items():assert sha(ROOT/p)==h,p
    assert sha(HERE/'scripts/probe_sum.py')==r['script_sha256']
    window=[0]
    for d in r['directions']:window.append(window[-1]^(1<<d))
    ball={v for v in range(512) if min((v^c).bit_count() for c in window[1:-1])<=4}
    for cut in r['cycle_cuts']:
        selected=set(cut);assert len(selected)==len(cut)>2 and selected<=ball
        adjacent={v:{v^(1<<d) for d in range(9)}&selected for v in selected}
        assert all(len(ns)==2 for ns in adjacent.values())
        seen={cut[0]};todo=list(seen)
        while todo:
            for x in adjacent[todo.pop()]-seen:seen.add(x);todo.append(x)
        assert seen==selected
    name=path.relative_to(HERE).as_posix()
    if r['status']=='SAT_LOCAL_WITNESS':assert name in verified and sha(path)==verified[name]['sha256']
    rows.append(dict(probe=name,status=r['status'],sha256=sha(path),cuts=len(r['cycle_cuts']),seconds=r['solver_seconds']))
assert {r['probe'] for r in rows if r['status']=='SAT_LOCAL_WITNESS'}==set(verified)
out=dict(status='PASS_PROBE_PINS_CYCLE_CUTS_AND_WITNESS_COVERAGE',probes=rows,
    witness_audit_sha256=sha(HERE/'data/witness-audit.json'),script_sha256=sha(Path(__file__)),
    scope='Validates provenance, every added induced-cycle exclusion and positive-witness audit coverage. Does not independently certify any UNSAT solver answer.')
target=HERE/'data/probe-audit.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],len(rows),'probes',len(verified),'witnesses',flush=True)
