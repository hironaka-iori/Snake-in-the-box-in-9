"""Repack only the first 256-hint segment under a direct preorder initialization."""
from pathlib import Path
import hashlib,importlib.util,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
gp=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
sp=importlib.util.spec_from_file_location('probe144',gp);lr=importlib.util.module_from_spec(sp);sp.loader.exec_module(lr)
plan=read(H/'data/proof-plan-base.json');meta=read(H/'data/share144.json')
proof=H/'certificates/share144.lrat';lemmas=lr.read_lrat(str(proof))
assert len(lemmas)==145215 and sum(len(h) for _,_,h in lemmas)==14710881
allocation=lr.plan(meta['core_ids'],lemmas);inputs,steps,last,nslots=allocation
height=nslots.bit_length();pre=lr.preorder_keys(height)
assert len(inputs)==len(set(inputs))==13224
key={slot:pre[i] for i,slot in enumerate(inputs)}
remaining=sorted(set(range(1,nslots+1))-set(inputs))
key.update({slot:pre[len(inputs)+i] for i,slot in enumerate(remaining)})
assert len(key)==nslots and len(set(key.values()))==nslots
lr.set_width(14,True,4000);lr.OFF=8192
raw=lr.read_cnf_core(str(H/'certificates/share144.cnf'),meta['core_ids'])
db={k:1|(1<<8192) for k in pre}
for slot,clause in zip(inputs,raw):db[key[slot]]=lr.cmask(clause)
nums=[];hintcount=0
for slot,clause,hints in steps:
 x=lr.pack([key[slot]]+[lr.bit(l)+1 for l in clause]+[0]+[key[h] for h in hints]+[0])
 assert lr.sim_rup(db,x)
 lr.sim_ins(db,x);nums.append(x);hintcount+=len(hints)
 if hintcount>=256:break
target=H/'experiments/lean/RawInitSmall144.lean';assert not target.exists()
source='''import RawInit144
import LocalWindowCnf.ShareWindow144

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.RawInitSmall144
open Snake9.LratFast144
open Snake9.LocalWindow.ShareWindow144 (raw)
noncomputable def start := (Snake9.RawInit144.rawPre 14 0 raw).1
noncomputable def proof : List Nat := [
'''+',\n'.join('  nat_lit 0x'+format(x,'x') for x in nums)+'''
]
theorem first_segment : check start proof = true := by
  decide +kernel
end Snake9.RawInitSmall144
#print axioms Snake9.RawInitSmall144.first_segment
'''
target.write_text(source,encoding='utf-8',newline='\n')
out=dict(status='PREPARED_AND_PREFIX_SIMULATED_LEAN_PENDING',hints=hintcount,deductions=len(nums),slots=nslots,height=height,
 key_bijection=True,input_order_preserved=True,source_sha256=sha(target),
 source_files_sha256={str(p):sha(p) for p in [Path(__file__),gp,proof,H/'data/proof-plan-base.json',H/'data/share144.json',H/'experiments/lean/RawInit144.lean']},
 scope='Only the first segment is simulated and prepared. No complete local theorem or upper bound.')
(H/'experiments/data/raw-init-small.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','hints','deductions','slots']}))
