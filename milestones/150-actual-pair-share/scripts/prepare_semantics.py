"""Interpret the retained core using only the original count-free cap15 model."""
from pathlib import Path
import gzip,hashlib,json,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/148-actual-snake-share-transfer'
Q=R/'milestones/147-countfree-clause-semantics'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),p
    p.write_text(s,encoding='utf-8',newline='\n')
def change(s,a,b):
    assert a in s,a;return s.replace(a,b)
start=time.monotonic()
proofhome=H/'work/highpair16';checked=read(proofhome/'native-replay.json')
assert checked['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY' and checked['actual_pair_clauses_used']==0
assert checked['core_clauses']==13655 and checked['deductions']==58182
for name,key in [('core.cnf','core_sha256'),('core-ids.json','core_ids_sha256'),('trimmed.lrat','trimmed_sha256')]:
    assert sha(proofhome/name)==checked[key]
old=R/'milestones/72-four-count-proof-closure/critical-current'
historical=read(old/'data/pysat1-cap15-certificate.json')
raw=gzip.decompress((old/'certificates/pysat1-cap15.cnf.gz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==historical['cnf_sha256']
original=H/'work/countfree16/original.cnf';original.parent.mkdir(exist_ok=False);original.write_bytes(raw)
clauses=[[int(x) for x in l.split()[:-1]] for l in raw.decode().splitlines() if l and l[0] not in 'pc']
ids=read(proofhome/'core-ids.json');assert max(ids)<=len(clauses)==92640
core=[[int(x) for x in l.split()[:-1]] for l in (proofhome/'core.cnf').read_text().splitlines() if l and l[0] not in 'pc']
assert core==[clauses[i-1] for i in ids]
variables=set();count=0
with (proofhome/'trimmed.lrat').open(encoding='ascii') as f:
    for line in f:
        values=list(map(int,line.split(' 0 ',1)[0].split()))
        variables.update(abs(v) for v in values[1:]);count+=1
assert count==58182
write(H/'data/proof-variables.json',json.dumps(sorted(variables))+'\n')
meta=dict(historical,status='PASS_COMPLETE_NATIVE_RUP_REPLAY',core_sha256=sha(proofhome/'core.cnf'),
    native_replay_source='work/highpair16/native-replay.json',native_replay_sha256=sha(proofhome/'native-replay.json'),
    historical_metadata_sha256=sha(old/'data/pysat1-cap15-certificate.json'),
    actual_pair_condition_used=False)
write(H/'data/native-reference.json',json.dumps(meta,indent=2)+'\n')
template=R/'milestones/146-initial-tree-and-paper/scripts/generated_prepare_012301.py'
s=template.read_text(encoding='utf-8').replace('146','150')
s=change(s,"meta['status']=='NATIVE_DRAT_VERIFIED'","meta['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'")
s=change(s,"ROOT/'milestones/72-four-count-proof-closure/critical-current/build/pysat3-cap15.cnf'","HERE/'work/countfree16/original.cnf'")
s=change(s,"ROOT/'milestones/145-countfree-012301/work/conversion-long/core.cnf'","HERE/'work/highpair16/core.cnf'")
s=change(s,"ROOT/'milestones/145-countfree-012301/work/conversion-long/core-ids.json'","HERE/'work/highpair16/core-ids.json'")
s=change(s,"body='import Port98CombinedCatalogue\\n'","body='import LocalWindowShareModel\\n'")
s=change(s,"body='import Port98CombinedCatalogue\\nimport LocalWindowCnf.ShareWindow150\\n'", "body='import LocalWindowTagsPacked\\nimport LocalWindowTagsSharePacked\\nimport LocalWindowCnf.ShareWindow150\\n'")
generator=H/'scripts/generated_prepare150.py';write(generator,s)
exec(compile(s,str(generator),'exec'),{'__file__':str(generator),'__name__':'prepare150'})
summary=read(H/'data/share150.json');assert summary['source_original_clause_ids']==ids
assert summary['clauses']==13655 and summary['shards']==107
# Compose the checked chunks while keeping their literal bodies opaque.
n=summary['shards'];m='Share150.Semantics150'
s='import Share150.Structure\n'+''.join(f'import Share150.Shard{i:02d}\n' for i in range(n))
s+='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
s+='namespace Snake9.LocalWindow.ShareWindow150\nopen Snake9.LocalWindow.Tags\n'
s+='''theorem interpreted_core150 (S E : Nat → Bool)
    (ax : AxiomsS S E window (centresOf window bounds) resolution cap) :
    cnfTrue (tauS S E meaning smeaning resolution ctrs tots) cnf = true := by
  rw [centresK_eq] at ax
'''
for i in range(n):
    s+=f'''  have h{i} : raw{i}.all (fun cl => clauseTrue
      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=
    List.all_eq_true.mpr (sound_allS shard{i} counts_ok totals_ok ax)
'''
s+='  simp only [cnf, cnfTrue, List.all_map, raw, List.all_append, Bool.and_eq_true,\n'
s+='    List.all_nil, and_true, and_assoc]\n'
s+='  exact ⟨'+', '.join(f'h{i}' for i in range(n))+'⟩\n'
s+='''#print axioms interpreted_core150
theorem local_share16_of_core_unsat150 (h : Unsat cnf) :
    RefutedShare window bounds resolution cap :=
  refutedShare_of_sat (fun S E ax => ⟨_, interpreted_core150 S E ax⟩) h
#print axioms local_share16_of_core_unsat150
end Snake9.LocalWindow.ShareWindow150
'''
write(H/'lean/Share150/Semantics150.lean',s)
wrapper='''import CanonicalShareAdapter
import Share150.Semantics150

namespace Snake9.ShareTransfer150
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73

theorem share16_of_core_unsat
    (hunsat : Unsat ShareWindow150.cnf)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2] ∨
      canon (dsOf p r 6).reverse = [0,1,2,0,3,2]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have href : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15 := by
    simpa only [ShareWindow150.window, ShareWindow150.bounds,
      ShareWindow150.resolution, ShareWindow150.cap, winOf, broadBounds] using
      ShareWindow150.local_share16_of_core_unsat150 hunsat
  exact share_bound_of_either_canonical_match p r [0,1,2,0,3,2] hr hshape href

#print axioms share16_of_core_unsat
end Snake9.ShareTransfer150
'''
write(H/'lean/ShareFromCore150.lean',wrapper)
order=['LocalWindowCnf.ShareWindow150','Share150.Data','Share150.Structure']+[f'Share150.Shard{i:02d}' for i in range(n)]+[m,'ShareFromCore150']
rows=[]
for mod in order:
    p=H/'lean'/(mod.replace('.','/')+'.lean');rows.append(dict(module=mod,path=p.relative_to(H).as_posix(),sha256=sha(p)))
oldplan=read(P/'data/transfer-plan-v4.json')
plan=dict(status='PREPARED_COUNTFREE_CORE_SEMANTICS_AND_CONDITIONAL_TRANSFER',
    module_order=order,framework_modules=order,inherited_modules={},artifacts=rows,
    external_library_search_paths=oldplan['external_library_search_paths'],external_pins=oldplan['external_pins'],
    source_files_sha256={str(p):sha(p) for p in [Path(__file__),template,generator,proofhome/'core.cnf',proofhome/'core-ids.json',proofhome/'trimmed.lrat',original,H/'data/proof-variables.json']},
    base_input_clauses=len(clauses),core_clauses=len(core),deductions=count,proof_variables=len(variables),
    actual_pair_premise_used=False,original_cycle_cuts=[],
    scope='Prepared only. Reuse pinned147 generic models and148 coordinate/reversal helpers. New clause checks, conditional actual-snake transfer and complete Lean replay remain separate.',seconds=time.monotonic()-start)
write(H/'data/semantic-plan.json',json.dumps(plan,indent=2)+'\n')
body=(P/'scripts/check_module_v4.py').read_text(encoding='utf-8').replace('transfer-plan-v4.json','semantic-plan.json')
body=change(body,"[build,Q/'build']+external","[build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build']+external")
body=change(body,"[build,Q/'build',B.parent/'lib/lean']+external","[build,R/'milestones/148-actual-snake-share-transfer/build',Q/'build',B.parent/'lib/lean']+external")
body=change(body,"if not rp.exists():rp=Q/'data'/(name+'-audit.json')", "if not rp.exists():rp=R/'milestones/148-actual-snake-share-transfer/data'/(name+'-audit.json')\n    if not rp.exists():rp=Q/'data'/(name+'-audit.json')")
body=change(body,'Thirteen project helpers are freshly checked; one historical automaton data object is reused with exact source/object/log and direct dependency matching.147 semantics are reused with their exact accepted receipts.', 'Generic clause models are reused from147 and coordinate/reversal helpers from148 with pinned receipts. The148 closure includes one historically compiled data object. The new150 clauses and conditional transfer are freshly checked; the core contradiction remains separate.')
write(H/'scripts/check_module.py',body)
body=(P/'scripts/run_transfer_v4.py').read_text(encoding='utf-8')
body=body.replace('transfer-plan-v4.json','semantic-plan.json').replace('PREPARED_TRANSFER_WITH_GENERIC_DIRECTION_CORE',plan['status'])
body=body.replace('check_module_v4.py','check_module.py').replace('transfer-v4','semantic').replace('PASS_BOUNDED_TRANSFER_PREFIX','PASS_BOUNDED_SEMANTIC_PREFIX').replace('PASS_COMPLETE_CONDITIONAL_TRANSFER_CHAIN','PASS_COMPLETE_CORE_SEMANTICS_AND_CONDITIONAL_TRANSFER')
write(H/'scripts/run_semantics.py',body)
body=(P/'scripts/serialize_transfer_v4.py').read_text(encoding='utf-8').replace('148','150')
body=body.replace('serialization-v4-','serialization-').replace('transfer-v4-batch.lock','semantic-batch.lock').replace('run_transfer_v4.py','run_semantics.py')
write(H/'scripts/serialize_semantics.py',body)
print(json.dumps(dict(status=plan['status'],modules=len(order),clauses=len(core),proof_variables=len(variables),seconds=plan['seconds'])))
