"""Avoid Lean's top-level module-directory shadowing; preserve the first attempt."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
assert not (HERE/'data/check.lock').exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads((HERE/'data/check-plan.json').read_text());env=json.loads((HERE/'data/environment.json').read_text())
assert env['paths'][0]==str(HERE/'build')
env['paths'][0]=str(HERE/'build-isolated');(HERE/'build-isolated').mkdir(exist_ok=True)
(HERE/'data/environment-isolated.json').write_text(json.dumps(env,indent=2)+'\n',encoding='utf-8')
ports=[]
for name in plan['modules']:
    if name=='RecoveredReference107':continue
    src=HERE/'lean'/(name.replace('.','/')+'.lean')
    dest=HERE/'lean/Recovered107'/src.relative_to(HERE/'lean');dest.parent.mkdir(exist_ok=True,parents=True)
    text=src.read_text(encoding='utf-8')
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.Q012A11(?:\.[A-Za-z0-9]+)?)$',r'import Recovered107.\1',text,flags=re.M)
    dest.write_text(changed,encoding='utf-8')
    assert re.sub(r'^import Recovered107\.',r'import ',dest.read_text(),flags=re.M)==text
    ports.append(dict(original=src.relative_to(HERE).as_posix(),source_sha256=sha(src),
        isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest),change='Import path only; namespace and theorem content unchanged'))
wrapper=HERE/'lean/RecoveredReference107.lean';text=wrapper.read_text()
text=text.replace('import LocalWindowSat.Q012A11','import Recovered107.LocalWindowSat.Q012A11').replace('import LocalWindowUnsat.Q012A11','import Recovered107.LocalWindowUnsat.Q012A11')
wrapper.write_text(text,encoding='utf-8')
checker=(HERE/'scripts/check.py').read_text()
checker=checker.replace("HERE/'data/environment.json'","HERE/'data/environment-isolated.json'")
checker=checker.replace("HERE/'build'","HERE/'build-isolated'")
(HERE/'scripts/check_isolated.py').write_text(checker,encoding='utf-8')
modules=[('Recovered107.'+n) if n!='RecoveredReference107' else n for n in plan['modules']]
(HERE/'data/isolated-plan.json').write_text(json.dumps(dict(modules=modules,ports=ports,
    reason='The first replay checked18modules but the combined wrapper failed because new LocalWindowSat modules shadowed the shared namespace directory. Only import module paths are changed; old sources, objects, logs and environment remain preserved.'),indent=2)+'\n',encoding='utf-8')
print('Prepared isolated module prefix for',len(modules),'modules')
