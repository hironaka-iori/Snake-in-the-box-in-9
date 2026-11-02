"""Export the already reduced proof after a verified active-variable permutation."""
from pathlib import Path
import hashlib, importlib.util, json, re, subprocess, sys, time
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def load(path,name):
    sp=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod
old=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts'
cg=load(old/'gen_lean_core.py','core112')
case_name='012314-upper2-outer18'
meta=read(HERE/'data'/(case_name+'-certificate.json'))
assert meta['status']=='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING'
fullpath=HERE/'work'/case_name/'full.cnf'
assert sha(fullpath)==meta['cnf_sha256']
full=[[int(x) for x in line.split()[:-1]] for line in fullpath.read_text().splitlines() if line and not line.startswith(('c','p'))]
work=HERE/'work/sum314-refined'
work.mkdir(exist_ok=True)
ids=meta['core_ids']
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
refinement=read(HERE/'data/sum314-refinement.json')
best=refinement['attempts'][refinement['best']]
assert best['status']=='UNSAT'
ids=best['input_ids']
trim=work/f'core{best["iteration"]}.trim.lrat'
name,mod='sum3142','Sum3142'
proof_rows=[list(map(int,line.split())) for line in trim.read_text().splitlines()]
active={abs(x) for i in ids for x in full[i-1]}
for row in proof_rows:active.update(abs(x) for x in row[1:row.index(0,1)])
assert len(active)<2400
order=sorted(active)+sorted(set(range(1,meta['variables']+1))-active)
rename={v:i+1 for i,v in enumerate(order)}
assert sorted(rename.values())==list(range(1,meta['variables']+1))
def literal(v):return rename[abs(v)]*(1 if v>0 else -1)
original_full=full
full=[[literal(v) for v in c] for c in original_full]
(HERE/'data/sum-renumbering.json').write_text(json.dumps(dict(active_variables=len(active),old_to_new=rename,original_cnf_sha256=sha(fullpath),original_proof_sha256=sha(trim)),indent=2)+'\n',encoding='utf-8')
(work/(name+'.cnf')).write_bytes((f'p cnf {meta["variables"]} {len(full)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in full)).encode())
def cid(i):return ids[i-1] if i<=len(ids) else len(full)+i-len(ids)
with (work/(name+'.lrat')).open('w',encoding='ascii',newline='\n') as out:
    for line in trim.read_text().splitlines():
        row=list(map(int,line.split()));z=row.index(0,1)
        out.write(' '.join(map(str,[cid(row[0]),*map(literal,row[1:z]),0,*map(cid,row[z+1:-1]),0]))+'\n')
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_lean_sat as sg
enc=sg.TaggedEncoding(meta['window'],[tuple(b) for b in meta['bounds']],radius=4)
from itertools import combinations
lits=[]
for j in meta['positions']:
    i=j+1;v=enc.window[i];used={v^enc.window[i-1],v^enc.window[i+1]}
    lits += [-enc.var[v^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used]
lits.sort();enc.atmost(lits,meta['sum_cap'],('unproved_sum',))
assert enc.clauses==original_full
enc.clauses=full
enc.meaning={rename[k]:v for k,v in enc.meaning.items()}
enc.var={v:rename[k] for v,k in enc.var.items()}
enc.ctrs=[([literal(v) for v in ls],k,kind) for ls,k,kind in enc.ctrs]
md=HERE/'data/sum-meta';md.mkdir(exist_ok=True)
newmeta=dict(meta,module='LocalWindowCnf.'+mod,core_ids=ids,dirs=meta['directions'])
(md/(name+'.json')).write_text(json.dumps(newmeta,indent=2)+'\n',encoding='utf-8')
generated=HERE/'generated-sum-remapped'
for directory in ['LocalWindowCnf','LocalWindowSat']:(generated/directory).mkdir(parents=True,exist_ok=True)
body=',\n  '.join(str([sg.code(v) for v in full[i-1]]) for i in ids)
(generated/'LocalWindowCnf'/(mod+'.lean')).write_text(f'''import LocalWindowDirModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
def window : List Nat := winOf {meta['directions']}
def bounds : List (Nat × Nat) := {[tuple(b) for b in meta['bounds']]}
def raw : List (List Nat) := [
  {body}]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
''',encoding='utf-8')
terms=[]
for ls,k,kind in enc.ctrs:
    kt='.ends' if kind[0] in ['ends','unproved_sum'] else f'(.{kind[0]} {kind[1]})'
    terms.append(f'⟨{[sg.code(l) for l in ls]}, {k}, {kt}⟩')
tags=[enc.tags[i-1] for i in ids]
tagbody=',\n  '.join(', '.join(sg.lean_tag(t) for t in tags[i:i+8]) for i in range(0,len(tags),8))
selected=[]
for j in meta['positions']:
    lo,hi=meta['bounds'][j]
    selected.append(f'⟨{enc.window[j+1]}, {meta["directions"][j]}, {meta["directions"][j+1]}, {lo}, {hi}⟩')
src=f'''import SumCountSemantics112
import LocalWindowCnf.{mod}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.{mod}
open Snake9.LocalWindow.Tags
def meaning : MT := {sg.lean_tree_terms(enc.meaning,enc.nv)}
def ordinary : List Ctr := [{', '.join(terms[:-1])}]
def extra : Ctr := {terms[-1]}
def selected : List Centre := [{', '.join(selected)}]
def tags : List Tag := [
  {tagbody}]
theorem check :
    ckAll meaning (ordinary++[extra]) window tags raw = true ∧
    ordinary.all (ctrOK meaning (centresK window bounds)) = true ∧
    extra.lits.all (baseOK meaning) = true ∧
    extra.lits.all (negP meaning) = true ∧
    (extra.lits.map (vl meaning)).Perm (selected.flatMap corners) := by decide +kernel
theorem sat (S E : Nat → Bool)
    (ax : Axioms S E window (centresOf window bounds))
    (hsum : (selected.map fun c => absentCorners S c.v c.d₁ c.d₂).sum ≤ 18) :
    ∃ τ, cnfTrue τ cnf = true := by
  obtain ⟨hc,hcs,hbase,hneg,hperm⟩ := check
  have hcs' : ordinary.all (ctrOK meaning (centresOf window bounds)) = true := by
    simpa only [centresK_eq] using hcs
  refine ⟨tau S E meaning (ordinary++[extra]), ?_⟩
  apply SumCountSemantics112.sound_append_sum meaning ordinary extra window bounds tags raw
    hc hcs' selected hneg hperm S E
  · intro i hi
    exact List.all_eq_true.mp hbase _ (getD_mem hi)
  · exact hsum
  · exact ax
#print axioms check
#print axioms sat
end Snake9.LocalWindow.{mod}
'''
(generated/'LocalWindowSat'/(mod+'.lean')).write_text(src,encoding='utf-8')
lr=load(old/'gen_lean_lrat.py','lrat112')
lr.set_width(13,fast=True,off=2400);lr.DATA_DEF='noncomputable def';lr.GROUPED=True
stats=lr.export(name,str(work),6000,4,4,True,str(generated),str(md))
sources={p.relative_to(generated).as_posix()[:-5].replace('/','.'):p for p in generated.rglob('*.lean')}
mods=[];ports=[];remaining=set(sources)
while remaining:
    ready=sorted(m for m in remaining if not set(re.findall(r'^import ([\w.]+)$',sources[m].read_text(encoding='utf-8'),re.M))&remaining)
    assert ready;mods.extend(ready);remaining-=set(ready)
for module in mods:
    p=sources[module];txt=p.read_text(encoding='utf-8');dest=HERE/'lean/Refined112'/p.relative_to(generated)
    dest.parent.mkdir(parents=True,exist_ok=True)
    changed=re.sub(r'^import (LocalWindow(?:Cnf|Sat|Unsat)\.'+mod+r'(?:\.[A-Za-z0-9]+)?)$',r'import Refined112.\1',txt,flags=re.M)
    dest.write_text(changed,encoding='utf-8')
    assert re.sub(r'^import Refined112\.',r'import ',changed,flags=re.M)==txt
    ports.append(dict(original=p.relative_to(HERE).as_posix(),source_sha256=sha(p),isolated=dest.relative_to(HERE).as_posix(),isolated_sha256=sha(dest)))
out=dict(status='GENERATED_NOT_CHECKED',modules=['Refined112.'+m for m in mods],ports=ports,generation=stats,core_clauses=len(ids),
    lemmas=best['lemmas'],hints=best['hints'],lrat_sha256=sha(work/(name+'.lrat')),cnf_sha256=sha(work/(name+'.cnf')),
    script_sha256=sha(Path(__file__)),renumbering_sha256=sha(HERE/'data/sum-renumbering.json'),scope='Concrete sum-counter semantics and refined contradiction export. Lean replay pending.')
(HERE/'data/sum-plan.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PREPARED',len(mods),'modules',flush=True)
