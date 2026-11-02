"""Pin milestone99 and reuse its proof environment without copying objects."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/99-defined-potential-certificates'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=read(OLD/'data/environment.json')
env['paths']=[str(HERE/'build'),*env['paths']]
for p in [OLD/'data/environment.json',OLD/'data/checkpoint.json',OLD/'data/proof-summary.json']:
    env['receipts'][p.relative_to(ROOT).as_posix()]=sha(p)
for p in (OLD/'data').glob('*-audit.json'):
    r=read(p)
    if r.get('status')!='PASS_DEFINED_POTENTIAL_MODULE':continue
    name=r['module'];src=OLD/'lean'/f'{name}.lean';obj=OLD/'build'/f'{name}.olean'
    assert sha(src)==r['source_sha256'] and sha(obj)==r['olean_sha256']
    assert sha(OLD/r['log'])==r['log_sha256']
    env['receipts'][p.relative_to(ROOT).as_posix()]=sha(p)
    env['sources'][src.relative_to(ROOT).as_posix()]=sha(src)
    env['objects'][obj.relative_to(ROOT).as_posix()]=sha(obj)
env['status']='PINNED_REUSED_MILESTONE99_ENVIRONMENT'
(HERE/'data/environment.json').write_text(json.dumps(env,indent=2)+'\n')
(HERE/'.gitattributes').write_text('* -text\n')
s=(OLD/'scripts/check.py').read_text().replace('PASS_DEFINED_POTENTIAL_MODULE','PASS_PREFIX_POTENTIAL_MODULE')
s=s.replace('Only the declarations printed in this receipt are checked. A pilot or data module does not certify every defined-graph edge.', 'Only this module and its printed statements are checked. A selected context does not certify the complete graph.')
(HERE/'scripts/check.py').write_text(s)
print('PINNED',len(env['receipts']),'receipts;',len(env['sources']),'source hashes')
