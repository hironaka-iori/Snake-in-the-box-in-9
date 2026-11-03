"""Group the unchanged native proof to reduce repeated compiler startup."""
from pathlib import Path
import importlib.util,json,re,shutil,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
path=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
sp=importlib.util.spec_from_file_location('group120',path);gen=importlib.util.module_from_spec(sp);sp.loader.exec_module(gen)
gen.set_width(13,fast=True,off=2400);gen.DATA_DEF='noncomputable def';gen.GROUPED=True
out=H/'generated-grouped';assert not out.exists();out.mkdir()
for name in ['LocalWindowCnf','LocalWindowSat']:
    (out/name).mkdir();shutil.copyfile(H/'generated'/name/'Outer3333.lean',out/name/'Outer3333.lean')
stats=gen.export('outer3333',str(H/'work/outer3333'),6000,6,6,True,str(out),str(H/'data/meta'))
mods=['LocalWindowCnf.Outer3333','LocalWindowSat.Outer3333','LocalWindowUnsat.Outer3333.Data0']
for i in range(1,stats['check_modules']+1):mods+=['LocalWindowUnsat.Outer3333.Data'+str(i),'LocalWindowUnsat.Outer3333.Check'+str(i)]
mods+=['LocalWindowUnsat.Outer3333'];ports=[]
for name in mods:
    p=out/(name.replace('.','/')+'.lean');t=p.read_text();changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.Outer3333(?:\.[A-Za-z0-9]+)?)$',r'import Recovered120G.\1',t,flags=re.M)
    dest=H/'lean/Recovered120G'/p.relative_to(out);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_text(changed,encoding='utf-8')
    assert re.sub(r'^import Recovered120G\.',r'import ',changed,flags=re.M)==t
    ports.append(dict(original=p.relative_to(H).as_posix(),original_sha256=sha(p),isolated=dest.relative_to(H).as_posix(),isolated_sha256=sha(dest)))
old=R/'milestones/111-critical-count-intervals';e=json.loads((old/'data/environment-isolated.json').read_text())
env=dict(status='PINNED_OUTER_COUNT_ENVIRONMENT',paths=[str(H/'build-isolated')]+e['paths'],receipts={**e['receipts'],(old/'data/environment-isolated.json').relative_to(R).as_posix():sha(old/'data/environment-isolated.json')})
(H/'data/environment-isolated.json').write_text(json.dumps(env,indent=2)+'\n',encoding='utf-8')
checker=(old/'scripts/check_isolated.py').read_text().replace('len(others)<=2','len(others)<=1').replace('time.sleep(10)','time.sleep(2)')
(H/'scripts/check_isolated.py').write_text(checker,encoding='utf-8')
plan=dict(status='GENERATED_NOT_CHECKED',modules=['Recovered120G.'+n for n in mods]+['ActualOuter120'],ports=ports,generation=stats,original_plan_sha256=sha(H/'data/outer3333-plan.json'),generator_sha256=sha(path),script_sha256=sha(Path(__file__)),checker_sha256=sha(H/'scripts/check_isolated.py'))
(H/'data/grouped-plan.json').write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
print('Prepared',len(plan['modules']),'sequential modules;',stats['segments'],'unchanged proof segments')
