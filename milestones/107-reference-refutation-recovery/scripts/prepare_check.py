"""Reuse the pinned proof environment and isolate nested recovery modules."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/105-reference-proof-closure'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((OLD/'data/environment.json').read_text())
env['paths']=[str(HERE/'build'),*env['paths']]
for p in [OLD/'data/environment.json',OLD/'data/proof-summary.json',OLD/'data/ReferenceAssembly105-audit.json']:
    env['receipts'][p.relative_to(ROOT).as_posix()]=sha(p)
env['status']='PINNED_REFERENCE_RECOVERY_ENVIRONMENT'
(HERE/'data/environment.json').write_text(json.dumps(env,indent=2)+'\n',encoding='utf-8')
text=(OLD/'scripts/check.py').read_text()
text=text.replace('PASS_REFERENCE_CLOSURE_MODULE','PASS_REFERENCE_RECOVERY_MODULE')
text=text.replace("/(module+'.lean')","/(module.replace('.','/')+'.lean')")
text=text.replace("/(name+'.lean')","/(name.replace('.','/')+'.lean')")
text=text.replace("/(name+'.olean')","/(name.replace('.','/')+'.olean')")
text=text.replace("/(name+'.'+run+'.olean')","/(name.replace('.','/')+'.'+run+'.olean')")
text=text.replace("if rp_a.exists():", "obj.parent.mkdir(parents=True,exist_ok=True)\n        if rp_a.exists():")
text=text.replace('proc.wait(timeout=300)','proc.wait(timeout=120)')
text=text.replace('Only this module and its printed statements are checked. A selected context does not certify the complete graph.',
    'Only this recovered module and its printed statements are checked. One reference entry does not discharge the complete union.')
(HERE/'scripts/check.py').write_text(text,encoding='utf-8')
modules=['LocalWindowCnf.Q012A11','LocalWindowSat.Q012A11','LocalWindowUnsat.Q012A11.Data0']
for k in range(1,8):modules.extend([f'LocalWindowUnsat.Q012A11.Data{k}',f'LocalWindowUnsat.Q012A11.Check{k}'])
modules+=['LocalWindowUnsat.Q012A11','RecoveredReference107']
(HERE/'data/check-plan.json').write_text(json.dumps(dict(modules=modules,per_module_timeout_seconds=120,
    maximum_additional_compilers=1,full_union_checked=False),indent=2)+'\n',encoding='utf-8')
print('Prepared',len(modules),'sequential modules; shared environment reused')
