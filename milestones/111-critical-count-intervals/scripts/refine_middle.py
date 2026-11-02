"""Reduce the certificate on successively smaller native cores before Lean replay."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(path,name):
    sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
old=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts'
cg=load(old/'gen_lean_core.py','cg111r');meta=read(HERE/'data/meta/middle325.json')
full=[[int(x) for x in line.split()[:-1]] for line in (HERE/'work/middle325/middle325.cnf').read_text().splitlines() if line and not line.startswith(('c','p'))]
ids=meta['core_ids'];work=HERE/'work/middle-refined';work.mkdir(exist_ok=True)
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
attempts=[];best=None
for iteration in range(3):
    cnf=work/f'core{iteration}.cnf';raw=work/f'core{iteration}.raw.lrat';trim=work/f'core{iteration}.trim.lrat'
    assert not raw.exists()
    nv=max(abs(x) for i in ids for x in full[i-1]);cnf.write_bytes((f'p cnf {nv} {len(ids)}\n'+''.join(' '.join(map(str,full[i-1]))+' 0\n' for i in ids)).encode())
    args=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)];start=time.monotonic()
    p=subprocess.run(args,capture_output=True,text=True,timeout=60);log=HERE/'logs'/f'middle-refine{iteration}.txt';log.write_text(p.stdout+p.stderr)
    assert p.returncode==20 and 's UNSATISFIABLE' in p.stdout
    nl,nh,used=cg.trim_lrat(str(raw),str(trim),len(ids))
    attempt=dict(iteration=iteration,command=args,solver_sha256=sha(exe),input_ids=ids,cnf_sha256=sha(cnf),log_sha256=sha(log),raw_sha256=sha(raw),trim_sha256=sha(trim),
        lemmas=nl,hints=nh,used_core=len(used),seconds=time.monotonic()-start)
    attempts.append(attempt)
    if best is None or nh<best['hints']:best=attempt
    print(iteration,'clauses',len(ids),'used',len(used),'steps',nl,'hints',nh,flush=True)
    new=[ids[i-1] for i in used]
    if new==ids:break
    ids=new
(HERE/'data/middle-refinement.json').write_text(json.dumps(dict(attempts=attempts,best=best['iteration']),indent=2)+'\n')
ids=best['input_ids'];trim=work/f'core{best["iteration"]}.trim.lrat';name='middle325r';mod='Middle325R'
(work/(name+'.cnf')).write_bytes((HERE/'work/middle325/middle325.cnf').read_bytes())
def cid(i):return ids[i-1] if i<=len(ids) else len(full)+i-len(ids)
with (work/(name+'.lrat')).open('w',encoding='ascii',newline='\n') as out:
    for line in trim.read_text().splitlines():
        row=list(map(int,line.split()));z=row.index(0,1)
        out.write(' '.join(map(str,[cid(row[0]),*row[1:z],0,*map(cid,row[z+1:-1]),0]))+'\n')
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_lean_sat as sg
enc=sg.TaggedEncoding(meta['window'],[tuple(b) for b in meta['bounds']],radius=4)
for cut in read(HERE/'data/probes/middle-3-2-5.json')['cycle_cuts']:enc.add([-enc.var[v] for v in cut],('cut',))
assert full==enc.clauses
meta=dict(meta,module='LocalWindowCnf.'+mod,core_ids=ids)
md=HERE/'data/refined-meta';md.mkdir(exist_ok=True);(md/(name+'.json')).write_text(json.dumps(meta,indent=2)+'\n')
generated=HERE/'generated-refined';(generated/'LocalWindowCnf').mkdir(parents=True,exist_ok=True)
body=',\n  '.join(str([sg.code(v) for v in full[i-1]]) for i in ids)
src=f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
def window : List Nat := winOf {meta['dirs']}
def bounds : List (Nat × Nat) := {[tuple(b) for b in meta['bounds']]}
def raw : List (List Nat) := [
  {body}]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
'''
(generated/'LocalWindowCnf'/(mod+'.lean')).write_text(src,encoding='utf-8')
sg.LEAN=str(generated);sg.write_module(name,mod,meta,enc,[enc.tags[i-1] for i in ids])
lr=load(old/'gen_lean_lrat.py','lr111r');lr.set_width(13,fast=True,off=2400);lr.DATA_DEF='noncomputable def';lr.GROUPED=True
stats=lr.export(name,str(work),6000,4,4,True,str(generated),str(md))
sources={p.relative_to(generated).as_posix()[:-5].replace('/','.'):p for p in generated.rglob('*.lean')};mods=[];ports=[];remaining=set(sources)
while remaining:
    ready=sorted(m for m in remaining if not set(re.findall(r'^import ([\w.]+)$',sources[m].read_text(),re.M))&remaining)
    assert ready
    mods.extend(ready);remaining-=set(ready)
for module in mods:
    p=sources[module];txt=p.read_text();dest=HERE/'lean/Refined111'/p.relative_to(generated);dest.parent.mkdir(parents=True,exist_ok=True)
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.'+mod+r'(?:\.[A-Za-z0-9]+)?)$',r'import Refined111.\1',txt,flags=re.M)
    dest.write_text(changed,encoding='utf-8');assert re.sub(r'^import Refined111\.',r'import ',changed,flags=re.M)==txt
    ports.append(dict(original=p.relative_to(HERE).as_posix(),source_sha256=sha(p),isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest)))
out=dict(status='GENERATED_NOT_CHECKED',modules=['Refined111.'+m for m in mods],ports=ports,generation=stats,
    core_clauses=len(ids),lemmas=best['lemmas'],hints=best['hints'],lrat_sha256=sha(work/(name+'.lrat')),cnf_sha256=sha(work/(name+'.cnf')),
    script_sha256=sha(Path(__file__)),scope='Refined independent native core and regenerated grouped proof. Lean replay pending.')
(HERE/'data/refined-plan.json').write_text(json.dumps(out,indent=2)+'\n')
print('Prepared',len(mods),'modules',flush=True)
