"""Joint-sum certificate generation. Numerical claims await Lean replay."""
import argparse,importlib.util,json,subprocess,sys,time,types
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/30-coarse-count-correction/scripts'))
from independent import joint_literals,BOUNDS
sys.path.insert(0,str(ROOT/'milestones/29-overlapping-share-windows/scripts'))
from joint import TaggedEncoding,window,candidates,Cadical153,census
import gen_lean_sat as gen
spec=importlib.util.spec_from_file_location('prior_verify',ROOT/'milestones/28-direct-share-certificates/scripts/verify.py')
prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
LEANBIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')

def run(cmd,log,expected=0):
    p=subprocess.run(list(map(str,cmd)),capture_output=True,text=True,encoding='utf-8',timeout=300)
    (HERE/'logs'/log).write_text(p.stdout+p.stderr,encoding='utf-8')
    assert p.returncode==expected,(cmd,p.returncode,p.stdout[-1000:],p.stderr[-1000:])
    return p.stdout
def readcnf(p):return [list(map(int,l.split()))[:-1] for l in p.read_text().splitlines() if l.strip() and not l.startswith(('p','c'))]
def writecnf(p,n,clauses):p.write_text(f'p cnf {n} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
def term(ct):
    ls,k,kind=ct;kt='.ends' if kind[0]=='ends' else f'(.{kind[0]} {kind[1]})'
    return f'⟨[{", ".join(str(gen.code(l)) for l in ls)}], {k}, {kt}⟩'

def sat_source(i,cap,mod,enc,tags):
    gen.LEAN=str(HERE/'lean');gen.write_module(f'sum{i}',mod,dict(module='LocalWindowCnf.'+mod),enc,tags)
    p=HERE/'lean/LocalWindowSat'/f'{mod}.lean';s=p.read_text(encoding='utf-8')
    s=s[:s.index('/-!')]+s[s.index('set_option'):]
    s=s.replace('import LocalWindowTags','import JointCountTags',1)
    start=s.index('def ctrs :');end=s.index('def tags :',start)
    W=window(candidates()[i]['dirs']);ds=candidates()[i]['dirs']
    cs=[f'⟨{W[j]}, {ds[j-1]}, {ds[j]}, 6, 21⟩' for j in [1,4,7]]
    s=s[:start]+'def oldCtrs : List Ctr := [\n'+',\n'.join(term(c) for c in enc.ctrs[:-1])+']\n'
    s+='def jointCtr : Ctr := '+term(enc.ctrs[-1])+'\ndef ctrs := oldCtrs ++ [jointCtr]\n'
    for name,c in zip(['centreA','centreB','centreC'],cs):s+=f'def {name} : Centre := {c}\n'
    # Recover the tag table from the unchanged generated source.
    original=p.read_text(encoding='utf-8');s+=original[original.index('def tags :'):original.index('theorem check :')]
    s+=f'''def jointSum (S : Nat → Bool) : Nat :=
  absentCorners S centreA.v centreA.d₁ centreA.d₂ +
  absentCorners S centreB.v centreB.d₁ centreB.d₂ +
  absentCorners S centreC.v centreC.d₁ centreC.d₂

theorem old_check : oldCtrs.all (ctrOK meaning (centresK window bounds)) = true := by decide +kernel
theorem clause_check : ckAll meaning ctrs window tags raw = true := by decide +kernel
theorem primitive_check : jointCtr.lits.all (baseOK meaning) = true := by decide +kernel
theorem negative_check : jointCtr.lits.all (negP meaning) = true := by decide +kernel
theorem corner_check : jointCtr.lits.map (vl meaning) =
    corners centreA ++ corners centreB ++ corners centreC := by decide +kernel

theorem joint_good (S E : Nat → Bool) (h : jointSum S ≤ {cap}) :
    JointTags.Good S E meaning jointCtr := by
  refine ⟨primitive_check, ?_⟩
  have hc := JointTags.three_centre_count (S := S) (E := E)
    jointCtr.lits centreA centreB centreC negative_check corner_check
  change jointCtr.lits.countP (lv (base S E meaning)) ≤ {cap}
  rw [hc]
  exact h

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

def build(i,cap):
    for d in ['certificates','data','logs','lean/LocalWindowCnf','lean/LocalWindowSat']:(HERE/d).mkdir(parents=True,exist_ok=True)
    ds=candidates()[i]['dirs'];W=window(ds);enc=TaggedEncoding(W,BOUNDS,radius=4)
    enc.atmost(joint_literals(enc,W),cap,('ends',)) # Dummy kind; semantic joint_good supplies this bound.
    cuts=set();cut_sources=[]
    for p in sorted((ROOT/'milestones/30-coarse-count-correction/data').glob('*.json')):
        if not p.name.startswith(('excess-','independent-')):continue
        row=json.loads(p.read_text())
        for cc in row['cycle_cuts']:
            prior.check_cut(cc);key=tuple(sorted(cc))
            if key not in cuts and set(cc)<=enc.B:
                cuts.add(key);enc.add([-enc.var[v] for v in key],('cut',));cut_sources.append(p.name)
    t=time.monotonic();status='UNKNOWN'
    with Cadical153(bootstrap_with=enc.clauses) as solver:
        while time.monotonic()-t<120:
            solver.conf_budget(10000);ok=solver.solve_limited()
            if ok is None:continue
            if not ok:status='UNSAT';break
            m=solver.get_model();S={v for v in enc.ball if m[enc.var[v]-1]>0};ccs=census(S,9,W[1:-1])['cycles']
            if not ccs:status='SAT';break
            for cc in ccs:
                prior.check_cut(cc);key=tuple(sorted(cc));assert key not in cuts
                cuts.add(key);cl=[-enc.var[v] for v in key];solver.add_clause(cl);enc.add(cl,('cut',))
    (HERE/f'data/search-{i}.json').write_text(json.dumps(dict(case=i,cap=cap,status=status,seconds=time.monotonic()-t,cycle_cuts=sorted(cuts),seed_cut_sources=cut_sources),indent=2)+'\n')
    print('search',i,cap,status,'cuts',len(cuts),flush=True);assert status=='UNSAT'
    name=f'sum{i}';mod=f'JointSum{i}';prefix=HERE/'certificates'/name
    full=prefix.with_suffix('.full.cnf');drat=prefix.with_suffix('.drat');core=prefix.with_suffix('.core.cnf')
    writecnf(full,enc.nv,enc.clauses)
    run([LEANBIN/'cadical.exe','-q','--no-binary',full,drat],name+'-cadical.txt',20)
    report=run([ROOT/'work/share-wheels/drat-trim.exe',full,drat,'-c',core],name+'-drat-check.txt');assert 's VERIFIED' in report
    rawcore=readcnf(core);lookup={tuple(sorted(c)):j for j,c in enumerate(enc.clauses)}
    ids=[lookup[tuple(sorted(c))] for c in rawcore];clauses=[enc.clauses[j] for j in ids]
    used=sorted({abs(v) for c in clauses for v in c});ordering=used+sorted(enc.meaning.keys()-set(used));rename={v:j+1 for j,v in enumerate(ordering)}
    lit=lambda v:(1 if v>0 else -1)*rename[abs(v)]
    compact=[[lit(v) for v in c] for c in clauses];writecnf(prefix.with_suffix('.cnf'),len(used),compact)
    raw='[\n'+',\n'.join('['+','.join(str(gen.code(v)) for v in c)+']' for c in compact)+'\n]'
    src=f'import LocalWindowModel\nset_option maxRecDepth 100000\nnamespace Snake9.LocalWindow.{mod}\n'
    src+=f'def window : List Nat := {W}\ndef bounds : List (Nat × Nat) := ['+','.join(f'({lo},{hi})' for lo,hi in BOUNDS)+']\n'
    src+='def raw : List (List Nat) := '+raw+f'\ndef cnf : List (List Int) := raw.map (·.map decodeLit)\nend Snake9.LocalWindow.{mod}\n'
    (HERE/'lean/LocalWindowCnf'/f'{mod}.lean').write_text(src,encoding='utf-8')
    small=types.SimpleNamespace(nv=len(ordering),meaning={rename[k]:v for k,v in enc.meaning.items()},ctrs=[([lit(x) for x in ls],k,kind) for ls,k,kind in enc.ctrs])
    sat_source(i,cap,mod,small,[enc.tags[j] for j in ids])
    meta=dict(module='LocalWindowCnf.'+mod,core_ids=list(range(1,len(compact)+1)),source_original_clause_ids=[j+1 for j in ids],active_variables=len(used),original_to_new=rename,dirs=ds,bounds=BOUNDS,joint_cap=cap,cycle_cuts=sorted(cuts))
    (HERE/'data'/f'{name}.json').write_text(json.dumps(meta,indent=2)+'\n')
    run([LEANBIN/'cadical.exe','-q','--lrat','--no-binary',prefix.with_suffix('.cnf'),prefix.with_suffix('.lrat')],name+'-lrat-cadical.txt',20)
    off=next(v for v in [2400,3000,4000,5000,6000] if v>len(used))
    report=run([sys.executable,'-X','utf8',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py','--work',HERE/'certificates','--data',HERE/'data','--out',HERE/'lean','--fast','--check','--off',off,name],name+'-export.txt')
    print(name,len(compact),'clauses;',len(used),'variables;',report.strip(),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--case',type=int);a=ap.parse_args()
    for i,cap in [(3,27),(2,28)]:
        if a.case is None or a.case==i:build(i,cap)
