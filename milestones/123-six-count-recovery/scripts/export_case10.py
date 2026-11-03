"""Re-export the reduced saved case10 proof and its renamed clause semantics."""
from pathlib import Path
import hashlib,importlib.util,json,re,sys,types
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/32-seven-count-four-screen'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
import gen_lean_sat as satgen
from wincert import window_from_dirs
a=read(H/'data/case10-recovery.json');meta0=read(P/'data/four10.json')
for s in a['sources']:assert sha(R/s['source'])==s['sha256']
case=a['case'];enc=satgen.TaggedEncoding(window_from_dirs(case['dirs']),[tuple(x) for x in case['bounds']],radius=4)
rename={int(k):v for k,v in meta0['original_to_new'].items()}
lit=lambda x:(1 if x>0 else -1)*rename[abs(x)]
compact=[[lit(x) for x in enc.clauses[k-1]] for k in meta0['source_original_clause_ids']]
ids=a['retained_core_ids'];mod='SixFour10';work=H/'work/four10';generated=H/'generated'
assert sha(work/'four10.cnf')==a['cnf_sha256'] and sha(work/'four10.lrat')==a['lrat_sha256']
meta=dict(module='LocalWindowCnf.'+mod,dirs=case['dirs'],window=enc.window,bounds=case['bounds'],radius=4,
    cnf_clauses=len(compact),core_ids=ids)
(H/'data/meta').mkdir();(H/'data/meta/four10.json').write_text(json.dumps(meta,indent=2)+'\n')
(generated/'LocalWindowCnf').mkdir(parents=True)
body=',\n  '.join(str([satgen.code(v) for v in compact[i-1]]) for i in ids)
source=f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
def window : List Nat := winOf {case['dirs']}
def bounds : List (Nat × Nat) := {[tuple(x) for x in case['bounds']]}
def raw : List (List Nat) := [
  {body}]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
'''
(generated/'LocalWindowCnf'/(mod+'.lean')).write_text(source,encoding='utf-8')
small=types.SimpleNamespace(nv=len(rename),meaning={rename[k]:v for k,v in enc.meaning.items()},
    ctrs=[([lit(x) for x in ls],k,kind) for ls,k,kind in enc.ctrs])
satgen.LEAN=str(generated)
satgen.write_module('four10',mod,meta,small,[enc.tags[meta0['source_original_clause_ids'][i-1]-1] for i in ids])
old=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
spec=importlib.util.spec_from_file_location('lrat123',old);lr=importlib.util.module_from_spec(spec);spec.loader.exec_module(lr)
slots=lr.plan(ids,lr.read_lrat(str(work/'four10.lrat')))[3]
bits=next(b for b in [13,14,15] if slots<(1<<b));lr.set_width(bits,fast=True,off=2400)
lr.DATA_DEF='noncomputable def';lr.GROUPED=True
stats=lr.export('four10',str(work),6000,6,6,True,str(generated),str(H/'data/meta'))
assert stats['lemmas']==a['trimmed_lemmas'] and stats['hints']==a['trimmed_hints']
mods=['LocalWindowCnf.'+mod,'LocalWindowSat.'+mod]
mods += ['LocalWindowUnsat.'+mod+'.Data'+str(i) for i in range(stats['check_modules']+1)]
mods += ['LocalWindowUnsat.'+mod+'.Check'+str(i+1) for i in range(stats['check_modules'])]
mods += ['LocalWindowUnsat.'+mod];ports=[]
for module in mods:
    p=generated/(module.replace('.','/')+'.lean');text=p.read_text()
    dest=H/'lean/Recovered123G'/p.relative_to(generated);dest.parent.mkdir(parents=True,exist_ok=True)
    isolated=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.'+mod+r'(?:\.[A-Za-z0-9]+)?)$',r'import Recovered123G.\1',text,flags=re.M)
    dest.write_text(isolated,encoding='utf-8')
    assert isolated.replace('import Recovered123G.','import ')==text
    ports.append(dict(original=p.relative_to(H).as_posix(),sha256=sha(p),isolated=dest.relative_to(H).as_posix(),isolated_sha256=sha(dest)))
out=dict(status='NATIVE_REDUCED_REPLAY_SIMULATED_LEAN_PENDING',modules=['Recovered123G.'+m for m in mods],ports=ports,
    statistics=stats,word_bits=bits,literal_offset=2400,recovery_sha256=sha(H/'data/case10-recovery.json'),
    generator=old.relative_to(R).as_posix(),generator_sha256=sha(old),script_sha256=sha(Path(__file__)),
    semantics_generator_sha256=sha(R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py'),
    scope='Every reduced RUP step simulated by exporter; all Lean replay and actual-snake conclusions still pending.')
(H/'data/case10-plan.json').write_text(json.dumps(out,indent=2)+'\n')
print('Exported',len(mods),'modules;',stats['lemmas'],'deductions;',stats['hints'],'hints;',bits,'bits',flush=True)
