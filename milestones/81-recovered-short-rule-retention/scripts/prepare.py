"""Pin the exact forty-rule inputs, reuse closed certificates and emit dispatch."""
from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for folder in ['data','lean','build/support']:(HERE/folder).mkdir(parents=True,exist_ok=True)
folders=['47-critical-singleton-patterns','48-low-count-compatibility','49-six-direction-pair-catalogue','50-three-count-return']
rules=[];pool={};audits={}
for folder in folders:
    old=ROOT/'milestones'/folder;record=read(old/'logs/build-record.json');build=Path(record['build'])
    verification=read(old/'data/verification.json');assert verification['status']=='PASS'
    audits[(old/'data/verification.json').relative_to(ROOT).as_posix()]=sha(old/'data/verification.json')
    records={r['module']:r for r in record['records'] if r['exit_code']==0}
    for rel,digest in verification['sources_sha256'].items():
        source=old/'lean'/rel;assert sha(source)==digest,source
        name=Path(rel).with_suffix('').as_posix();obj=build/(name+'.olean')
        if name in records and records[name]['source_sha256']==digest and obj.exists():
            if name in pool:assert sha(pool[name][0])==digest,name
            else:pool[name]=(source,obj)
    if folder.startswith('50'):
        rows=[dict(number=501,dirs=[0,1,2,3,4,0],positions=[1,4,5],kind='sum',cap=12)]
    else:rows=read(old/'data/cases.json')
    for row in rows:
        r=dict(number=row['number'],dirs=row['dirs'],source=folder)
        if folder.startswith('47'):r.update(kind='caps',caps=[(row['position'],1)])
        elif row['kind']=='sum':r.update(kind='sum',positions=row['positions'],cap=row['cap'])
        else:r.update(kind='caps',caps=list(zip(row['positions'],row['caps'])))
        if r['kind']=='caps':r['bounds']=row['bounds']
        rules.append(r)
assert len(rules)==40
roots=[('SumWindow' if r['kind']=='sum' else 'CycleExclusion')+str(r['number']) for r in rules]
overlay=HERE/'build/support';todo=roots[:];modules={};external=set()
while todo:
    name=todo.pop()
    if name in modules:continue
    source,obj=pool[name];dest=overlay/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    if not dest.exists() or sha(dest)!=sha(obj):shutil.copyfile(obj,dest)
    modules[name]=dict(source=str(source),source_sha256=sha(source),object=str(dest),object_sha256=sha(dest),origin=str(obj))
    for line in source.read_text(encoding='utf-8-sig').splitlines():
        if line.startswith('import '):
            for token in line.split()[1:]:
                dep=token.replace('.','/')
                if dep in pool:todo.append(dep)
                else:external.add(dep)
import runpy
runpy.run_path(str(HERE/'scripts/copy_joint_support.py'))
(HERE/'data/normalized-rules.json').write_text(json.dumps(rules,indent=2)+'\n')
(HERE/'data/short-support.json').write_text(json.dumps(dict(status='PINNED_SHORT_RULE_SUPPORT',overlay=str(overlay),
    roots=roots,modules=modules,external_imports=sorted(external),extra_paths=[],prior_audit_sha256=audits,
    scope='Closed local certificate objects reused with successful source-matched records; inherited support is not rebuilt.'),indent=2)+'\n')
lst=lambda xs:'['+','.join(map(str,xs))+']'
pairs=lambda xs:'['+','.join(f'({a},{b})' for a,b in xs)+']'
caps=[r for r in rules if r['kind']=='caps'];sums=[r for r in rules if r['kind']=='sum']
header=['','namespace Snake9.ShortRules81','open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow','open Snake9.Guards79','set_option maxHeartbeats 2000000','']
src=['import GuardTransfer']+[f"import CycleExclusion{r['number']}" for r in caps]+header
for r in caps:
    n=r['number'];d=lst(r['dirs']);cs=pairs(r['caps']);bs=pairs(r['bounds']);L=len(r['dirs'])
    src += [f'theorem safe{n} : rawSafe {d} (.caps {cs}) := by',
        f'  apply caps_from_refuted {d} {cs} {bs} (by decide) CycleWindow{n}.refuted',
        '  intro i hi',f'  change i < {L-1} at hi','  interval_cases i <;> simp','']
src += ['def capRules : List (List Nat × CountTest) := [',
    ',\n'.join(f"({lst(r['dirs'])}, .caps {pairs(r['caps'])})" for r in caps),']','',
    'theorem cap_catalogue : ∀ rule ∈ capRules, rawSafe rule.1 rule.2 ∧',
    '    smallCaps rule.2 ∧ internalPositions rule.2 rule.1.length := by',
    '  intro rule h','  simp only [capRules, List.mem_cons, List.not_mem_nil, or_false] at h',
    '  rcases h with '+' | '.join(['rfl']*len(caps))]
for r in caps:
    src += [f"  · exact ⟨safe{r['number']}, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩"]
src+=['']+[f"#print axioms safe{r['number']}" for r in caps]+['#print axioms cap_catalogue','end Snake9.ShortRules81','']
(HERE/'lean/CapCatalogue.lean').write_text('\n'.join(src))
src=['import GuardTransfer']+[f"import SumWindow{r['number']}" for r in sums]+header
for r in sums:
    n=r['number'];d=lst(r['dirs']);ps=lst(r['positions']);L=len(r['dirs']);cap=r['cap']
    src += [f'theorem safe{n} : rawSafe {d} (.sum {ps} {cap}) := by',
        '  intro m p r hr hshape hbad',f'  change r+{L} ≤ m at hr',
        f'  change canon (dsOf p r {L}) = {d} at hshape',
        f'  obtain ⟨P,hP⟩ := canonical_permutation p r {L} hr',
        f'  have hlo := JointIntervening{n}.sum_in_snake p P r hr (by',
        '    intro j hj','    have h := hP j hj','    rw [hshape] at h','    exact h)',
        f'  change ({ps}.map (fun j => coreAlpha p (r+j))).sum ≤ {cap} at hbad',
        '  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hbad',
        '  omega','']
src += ['def sumRules : List (List Nat × CountTest) := [',
    ',\n'.join(f"({lst(r['dirs'])}, .sum {lst(r['positions'])} {r['cap']})" for r in sums),']','',
    'theorem sum_catalogue : ∀ rule ∈ sumRules, rawSafe rule.1 rule.2 ∧',
    '    smallCaps rule.2 ∧ internalPositions rule.2 rule.1.length := by',
    '  intro rule h','  simp only [sumRules, List.mem_cons, List.not_mem_nil, or_false] at h',
    '  rcases h with '+' | '.join(['rfl']*len(sums))]
for r in sums:src += [f"  · exact ⟨safe{r['number']}, trivial, by simp [internalPositions, CountTest.positions]⟩"]
src+=['']+[f"#print axioms safe{r['number']}" for r in sums]+['#print axioms sum_catalogue','end Snake9.ShortRules81','']
(HERE/'lean/SumCatalogue.lean').write_text('\n'.join(src))
print('Prepared',len(caps),'cap rules,',len(sums),'sum rules;',len(modules),'pinned support objects; three support sources to check')
