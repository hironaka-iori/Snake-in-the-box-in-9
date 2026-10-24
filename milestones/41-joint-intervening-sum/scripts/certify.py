"""Extract and replay a joint-count contradiction with a separate semantic counter proof."""
from pathlib import Path
import importlib.util,itertools,json,sys,types
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('ordinary',ROOT/'milestones/38-four-position-obstruction/scripts/certify.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old);old.HERE=HERE
gen=old.gen;TaggedEncoding=old.TaggedEncoding;window=old.window
DIRS=[0,1,2,3,4,2,0,3];BOUNDS=[(0,3)]+[(0,21)]*5+[(0,3)]

def joint_literals(e,W,positions):
 return [-e.var[W[j]^(1<<a)^(1<<b)] for j in positions for a,b in itertools.combinations(range(9),2) if a not in (DIRS[j-1],DIRS[j]) and b not in (DIRS[j-1],DIRS[j])]
def term(ct):
 ls,k,kind=ct;kt='.ends' if kind[0]=='ends' else f'(.{kind[0]} {kind[1]})'
 return f'⟨[{", ".join(str(gen.code(l)) for l in ls)}], {k}, {kt}⟩'
def sat_source(name,mod,e,tags,positions,cap):
 gen.LEAN=str(HERE/'lean');gen.write_module(name,mod,dict(module='LocalWindowCnf.'+mod),e,tags)
 p=HERE/'lean/LocalWindowSat'/f'{mod}.lean';original=p.read_text(encoding='utf-8')
 s=original[:original.index('/-!')]+original[original.index('set_option'):]
 s=s.replace('import LocalWindowTags','import MultiCentreCount',1)
 s=s[:s.index('def ctrs :')]
 s+='def oldCtrs : List Ctr := [\n'+',\n'.join(term(c) for c in e.ctrs[:-1])+']\n'
 s+='def jointCtr : Ctr := '+term(e.ctrs[-1])+'\ndef ctrs := oldCtrs ++ [jointCtr]\n'
 W=window(DIRS)
 for j in positions:s+=f'def centre{j} : Centre := ⟨{W[j]}, {DIRS[j-1]}, {DIRS[j]}, 0, 21⟩\n'
 s+='def jointCentres : List Centre := ['+','.join('centre'+str(j) for j in positions)+']\n'
 s+=original[original.index('def tags :'):original.index('theorem check :')]
 s+='def jointSum (S : Nat → Bool) : Nat := '+ ' + '.join(f'absentCorners S centre{j}.v centre{j}.d₁ centre{j}.d₂' for j in positions)+'\n'
 s+=f'''
theorem old_check : oldCtrs.all (ctrOK meaning (centresK window bounds)) = true := by decide +kernel
theorem clause_check : ckAll meaning ctrs window tags raw = true := by decide +kernel
theorem primitive_check : jointCtr.lits.all (baseOK meaning) = true := by decide +kernel
theorem negative_check : jointCtr.lits.all (negP meaning) = true := by decide +kernel
theorem corner_check : jointCtr.lits.map (vl meaning) = jointCentres.flatMap corners := by decide +kernel

theorem joint_good (S E : Nat → Bool) (h : jointSum S ≤ {cap}) :
    JointTags.Good S E meaning jointCtr := by
  refine ⟨primitive_check, ?_⟩
  have hc := JointTags.multi_centre_count (S := S) (E := E)
    jointCtr.lits jointCentres negative_check corner_check
  change jointCtr.lits.countP (lv (base S E meaning)) ≤ {cap}
  rw [hc]
  simpa [jointCentres, jointSum] using h

theorem sat (S E : Nat → Bool) (ax : Axioms S E window (centresOf window bounds))
    (h : jointSum S ≤ {cap}) : ∃ τ, cnfTrue τ cnf = true := by
  have axK : Axioms S E window (centresK window bounds) := by
    rw [← centresK_eq]; exact ax
  have hv : JointTags.Valid S E meaning ctrs := by
    apply JointTags.valid_append old_check ?_ axK
    intro ct hc
    have he : ct = jointCtr := by simpa using hc
    subst ct
    exact joint_good S E h
  exact ⟨tau S E meaning ctrs,
    JointTags.sound meaning ctrs window (centresK window bounds) tags raw clause_check S E hv axK⟩
#print axioms sat
end Snake9.LocalWindow.{mod}
'''
 p.write_text(s,encoding='utf-8')

def build(i,positions,cap,source):
 for d in ['data','logs','certificates','lean/LocalWindowCnf','lean/LocalWindowSat','build']:(HERE/d).mkdir(parents=True,exist_ok=True)
 name=f'sum{i}';mod=f'JointIntervening{i}';prefix=HERE/'certificates'/name;W=window(DIRS)
 e=TaggedEncoding(W,BOUNDS,radius=4);lits=joint_literals(e,W,positions)
 e.atmost(lits,cap,('ends',))
 prior=json.loads((ROOT/'milestones/40-intervening-counts/data'/source).read_text())
 assert prior['status']=='UNSAT' and prior['joint']==[positions,cap]
 for cc in prior['cycle_cuts']:
  assert gen.is_cycle_set(cc) and set(cc)<=e.B
  e.add([-e.var[v] for v in cc],('cut',))
 old.writecnf(prefix.with_suffix('.full.cnf'),e.nv,e.clauses)
 old.run([old.LEANBIN/'cadical.exe','-q','--no-binary',prefix.with_suffix('.full.cnf'),prefix.with_suffix('.drat')],name+'-cadical.txt',20)
 report=old.run([ROOT/'work/share-wheels/drat-trim.exe',prefix.with_suffix('.full.cnf'),prefix.with_suffix('.drat'),'-c',prefix.with_suffix('.core.cnf')],name+'-drat-check.txt');assert 's VERIFIED' in report
 rawcore=old.readcnf(prefix.with_suffix('.core.cnf'));lookup={tuple(sorted(c)):j for j,c in enumerate(e.clauses)}
 ids=[lookup[tuple(sorted(c))] for c in rawcore];clauses=[e.clauses[j] for j in ids]
 used=sorted({abs(v) for c in clauses for v in c});ordering=used+sorted(e.meaning.keys()-set(used));rename={v:j+1 for j,v in enumerate(ordering)}
 lit=lambda v:(1 if v>0 else -1)*rename[abs(v)]
 compact=[[lit(v) for v in c] for c in clauses];old.writecnf(prefix.with_suffix('.cnf'),len(used),compact)
 raw='[\n'+',\n'.join('['+','.join(str(gen.code(v)) for v in c)+']' for c in compact)+'\n]'
 s=f'import LocalWindowModel\nset_option maxRecDepth 100000\nnamespace Snake9.LocalWindow.{mod}\n'
 s+=f'def window : List Nat := {W}\ndef bounds : List (Nat × Nat) := ['+','.join(f'({lo},{hi})' for lo,hi in BOUNDS)+']\n'
 s+='def raw : List (List Nat) := '+raw+f'\ndef cnf : List (List Int) := raw.map (·.map decodeLit)\nend Snake9.LocalWindow.{mod}\n'
 (HERE/'lean/LocalWindowCnf'/f'{mod}.lean').write_text(s,encoding='utf-8')
 small=types.SimpleNamespace(nv=len(ordering),meaning={rename[k]:v for k,v in e.meaning.items()},ctrs=[([lit(x) for x in ls],k,kind) for ls,k,kind in e.ctrs])
 sat_source(name,mod,small,[e.tags[j] for j in ids],positions,cap)
 meta=dict(module='LocalWindowCnf.'+mod,core_ids=list(range(1,len(compact)+1)),source_original_clause_ids=[j+1 for j in ids],active_variables=len(used),original_to_new=rename,dirs=DIRS,bounds=BOUNDS,positions=positions,joint_cap=cap,cycle_cuts=prior['cycle_cuts'],source_probe=source)
 (HERE/'data'/f'{name}.json').write_text(json.dumps(meta,indent=2)+'\n')
 old.run([old.LEANBIN/'cadical.exe','-q','--lrat','--no-binary',prefix.with_suffix('.cnf'),prefix.with_suffix('.lrat')],name+'-lrat-cadical.txt',20)
 import gen_lean_lrat as lr
 slots=lr.plan(meta['core_ids'],lr.read_lrat(str(prefix.with_suffix('.lrat'))))[3]
 bits=next(b for b in range(13,20) if slots<(1<<b));off=next(v for v in [2400,3000,4000,5000,6000] if v>len(used))
 report=old.run([sys.executable,'-X','utf8',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py','--work',HERE/'certificates','--data',HERE/'data','--out',HERE/'lean','--fast','--check','--noncomputable-data','--wbits',bits,'--off',off,name],name+'-export.txt')
 print(name,len(compact),'clauses',len(used),'variables',json.loads(report)['hints'],'hints',flush=True)

if __name__=='__main__':build(411,[3,6],11,'two-middle-sum-11.json')
