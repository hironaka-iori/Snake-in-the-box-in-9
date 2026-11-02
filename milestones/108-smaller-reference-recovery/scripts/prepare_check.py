"""Use an isolated import prefix from the first Lean replay."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/107-reference-refutation-recovery'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((OLD/'data/environment-isolated.json').read_text())
env['paths']=[str(HERE/'build-isolated'),*env['paths']]
for p in [OLD/'data/environment-isolated.json',OLD/'data/proof-summary.json',OLD/'data/RecoveredReference107-audit.json']:
    env['receipts'][p.relative_to(ROOT).as_posix()]=sha(p)
env['status']='PINNED_SECOND_REFERENCE_RECOVERY_ENVIRONMENT'
(HERE/'data/environment-isolated.json').write_text(json.dumps(env,indent=2)+'\n',encoding='utf-8')
(HERE/'build-isolated').mkdir(exist_ok=True)
ports=[]
modules=['LocalWindowCnf.D012304A22623','LocalWindowSat.D012304A22623',
 'LocalWindowUnsat.D012304A22623.Data0','LocalWindowUnsat.D012304A22623.Data1',
 'LocalWindowUnsat.D012304A22623.Check1','LocalWindowUnsat.D012304A22623']
for name in modules:
    src=HERE/'lean'/(name.replace('.','/')+'.lean')
    dest=HERE/'lean/Recovered108'/src.relative_to(HERE/'lean');dest.parent.mkdir(exist_ok=True,parents=True)
    text=src.read_text(encoding='utf-8')
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.D012304A22623(?:\.[A-Za-z0-9]+)?)$',r'import Recovered108.\1',text,flags=re.M)
    dest.write_text(changed,encoding='utf-8')
    assert re.sub(r'^import Recovered108\.',r'import ',dest.read_text(),flags=re.M)==text
    ports.append(dict(original=src.relative_to(HERE).as_posix(),source_sha256=sha(src),isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest),change='Import path only; namespace and theorem content unchanged'))
(HERE/'scripts/check_isolated.py').write_bytes((OLD/'scripts/check_isolated.py').read_bytes())
plan=dict(modules=['Recovered108.'+n for n in modules]+['RecoveredReference108','RelaxedReference108','ReferenceCoverage108'],ports=ports,
 per_module_timeout_seconds=120,maximum_additional_compilers=1,full_union_checked=False)
(HERE/'data/isolated-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
print('Prepared',len(plan['modules']),'sequential modules; shared environment reused')
