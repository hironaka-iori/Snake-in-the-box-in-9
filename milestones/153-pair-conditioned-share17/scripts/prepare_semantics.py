"""Prepare exact critical-context clause interpretations; do not launch Lean."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=H/'critical/work/critical17'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),p
    p.write_text(s,encoding='utf-8',newline='\n')
def change(s,a,b):
    assert s.count(a)==1,(a,s.count(a));return s.replace(a,b)
enc=read(P/'encoding.json');checked=read(P/'native-replay.json')
assert checked['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
assert (checked['core_clauses'],checked['deductions'],checked['hints'])==(11869,30305,1754767)
for name,key in [('core.cnf','core_sha256'),('core-ids.json','core_ids_sha256'),('trimmed.lrat','trimmed_sha256')]:assert sha(P/name)==checked[key]
variables=set();count=0
with (P/'trimmed.lrat').open(encoding='ascii') as f:
    for line in f:
        xs=list(map(int,line.split(' 0 ',1)[0].split()));variables.update(abs(x) for x in xs[1:]);count+=1
assert count==30305
write(H/'data/proof-variables.json',json.dumps(sorted(variables))+'\n')
meta=dict(enc,status='PASS_COMPLETE_NATIVE_RUP_REPLAY',core_sha256=sha(P/'core.cnf'),cycle_cuts=[],
          native_replay_source='critical/work/critical17/native-replay.json',native_replay_sha256=sha(P/'native-replay.json'))
write(H/'data/native-reference.json',json.dumps(meta,indent=2)+'\n')
template=R/'milestones/150-actual-pair-share/scripts/generated_prepare150.py'
s=template.read_text(encoding='utf-8').replace('150','153')
s=change(s,"HERE/'work/countfree16/original.cnf'","HERE/'critical/work/critical17/input.cnf'")
s=change(s,"HERE/'work/highpair16/core.cnf'","HERE/'critical/work/critical17/core.cnf'")
s=change(s,"HERE/'work/highpair16/core-ids.json'","HERE/'critical/work/critical17/core-ids.json'")
s=change(s,"TaggedShare(meta['directions'],meta['bounds'],15)","TaggedShare(meta['directions'],meta['bounds'],16)")
s=change(s,'def cap : Nat := 15','def cap : Nat := 16')
generator=H/'scripts/generated_prepare153.py';write(generator,s)
exec(compile(s,str(generator),'exec'),{'__file__':str(generator),'__name__':'prepare153'})
summary=read(H/'data/share153.json');assert summary['source_original_clause_ids']==read(P/'core-ids.json')
assert summary['clauses']==11869 and summary['shards']==93
n=summary['shards']
body='import Share153.Structure\n'+''.join(f'import Share153.Shard{i:02d}\n' for i in range(n))
body+='''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow153
open Snake9.LocalWindow.Tags
theorem interpreted_core153 (S E : Nat → Bool)
    (ax : AxiomsS S E window (centresOf window bounds) resolution cap) :
    cnfTrue (tauS S E meaning smeaning resolution ctrs tots) cnf = true := by
  rw [centresK_eq] at ax
'''
for i in range(n):
    body+=f'''  have h{i} : raw{i}.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard{i} counts_ok totals_ok ax)
'''
body+='  simp only [cnf, cnfTrue, List.all_map, raw, List.all_append, Bool.and_eq_true,\n'
body+='    List.all_nil, and_true, and_assoc]\n'
body+='  exact ⟨'+', '.join(f'h{i}' for i in range(n))+'⟩\n'
body+='''#print axioms interpreted_core153
theorem local_share17_of_core_unsat153 (h : Unsat cnf) :
    RefutedShare window bounds resolution cap :=
  refutedShare_of_sat (fun S E ax => ⟨_, interpreted_core153 S E ax⟩) h
#print axioms local_share17_of_core_unsat153
end Snake9.LocalWindow.ShareWindow153
'''
write(H/'lean/Share153/Semantics153.lean',body)
order=['LocalWindowCnf.ShareWindow153','Share153.Data','Share153.Structure']+[f'Share153.Shard{i:02d}' for i in range(n)]+['Share153.Semantics153']
rows=[]
for module in order:
    p=H/'lean'/(module.replace('.','/')+'.lean')
    rows.append(dict(module=module,path=p.relative_to(H).as_posix(),bytes=p.stat().st_size,sha256=sha(p)))
plan=dict(status='PREPARED_CRITICAL_CONTEXT_SEMANTICS_UNCHECKED',module_order=order,artifacts=rows,
    framework_modules=order,checked=False,core_clauses=11869,exact_count_bounds=enc['bounds'],cap=16,
    active_variables=summary['active_variables'],semantic_variables=summary['semantic_variables'],
    source_files_sha256={str(p):sha(p) for p in [Path(__file__),template,generator,H/'data/share153.json',P/'native-replay.json',P/'input.cnf',P/'core.cnf',P/'core-ids.json',H/'data/proof-variables.json']},
    scope='The exact count-conditioned core and local implication are generated. No new Lean module has been compiled. Coordinate/reversal adapter and complete contradiction replay remain separate.')
write(H/'data/semantic-source-plan.json',json.dumps(plan,indent=2)+'\n')
print(json.dumps({k:plan[k] for k in ['status','checked','core_clauses','active_variables','semantic_variables']}))
