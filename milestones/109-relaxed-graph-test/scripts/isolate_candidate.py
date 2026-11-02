"""Isolate the recovered candidate without changing the existing environment."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['LocalWindowCnf.D01234A1542','LocalWindowSat.D01234A1542',
 'LocalWindowUnsat.D01234A1542.Data0','LocalWindowUnsat.D01234A1542.Data1',
 'LocalWindowUnsat.D01234A1542.Check1','LocalWindowUnsat.D01234A1542']
ports=[]
for name in modules:
    src=HERE/'lean'/(name.replace('.','/')+'.lean')
    dest=HERE/'lean/Recovered109'/src.relative_to(HERE/'lean');dest.parent.mkdir(exist_ok=True,parents=True)
    text=src.read_text(encoding='utf-8')
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.D01234A1542(?:\.[A-Za-z0-9]+)?)$',r'import Recovered109.\1',text,flags=re.M)
    dest.write_text(changed,encoding='utf-8')
    assert re.sub(r'^import Recovered109\.',r'import ',dest.read_text(),flags=re.M)==text
    ports.append(dict(original=src.relative_to(HERE).as_posix(),source_sha256=sha(src),isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest)))
plan=dict(modules=['ActualRelaxed109']+['Recovered109.'+n for n in modules]+['NewRelaxed109'],ports=ports)
(HERE/'data/isolated-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
print('Prepared six candidate modules; existing environment preserved')
