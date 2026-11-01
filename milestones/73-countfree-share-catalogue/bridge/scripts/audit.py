"""Check source-matched bridge builds and the axioms printed by Lean."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
record=read(HERE/'logs/build-record.json');provenance=read(HERE/'data/provenance.json')
assert provenance['contributor_commit']=='cd0c90fddf12170d735ee34fcc501e99c60632a6'
for row in provenance['sources']:
    assert sha(HERE/'upstream'/Path(row['path']).name)==row['sha256']
reference=read(HERE/'data/overlap-reference.json')
assert sha(HERE/'upstream/SharePacking-reference.lean')==reference['sha256']
checks=[];modules=[]
for name,folder in [('ShareCharge','upstream'),('CoreShareBudget','lean'),('FiveCentreOverlap','lean')]:
    source=HERE/f'{folder}/{name}.lean';text=source.read_text()
    row=next(r for r in reversed(record['records']) if r['module']==name)
    assert row['exit_code']==0 and row['source_sha256']==sha(source)
    assert (HERE/'build'/(name+'.olean')).exists()
    for path,h in row['dependencies'].items():assert sha(Path(path))==h
    assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
    log=(HERE/'logs'/(name+'.log')).read_text()
    assert all(bad not in log for bad in ['error:','sorryAx','failed to delete'])
    found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
    assert len(found)==len(re.findall(r'^#print axioms ',text,re.M))
    for theorem,axs in found:
        assert set(re.findall(r'[A-Za-z][\w.]*',axs))<={'propext','Classical.choice','Quot.sound'}
        checks.append(dict(theorem=theorem,axioms=re.findall(r'[A-Za-z][\w.]*',axs)))
    modules.append(dict(module=name,source_sha256=sha(source),olean_sha256=sha(HERE/'build'/(name+'.olean'))))
support=[]
for stem in ['LocalWindowShareBridge','SquareIncidence']:
    path=next(Path(p)/(stem+'.olean') for p in record['paths'] if (Path(p)/(stem+'.olean')).exists())
    support.append(dict(module=stem,olean_path=str(path),olean_sha256=sha(path)))
out=dict(status='PASS_CORE_SHARE_BUDGET',newly_checked_modules=modules,theorem_audits=checks,
    five_centre_overlap_checked=True,
    inherited_direct_support=support,contributor_commit=provenance['contributor_commit'],
    scope='Contributor share identities recovered and independently replayed with a minimal import chain. The complete coreShare path budget, generic five-centre overlap and combined whole-path charge budget are Lean-checked. Cached cube and local-window support is reused; no fresh rebuild of all inherited dependencies and no new global numerical bound are claimed.')
(HERE/'data/proof-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],'modules',len(modules),'axiom audits',len(checks),flush=True)
