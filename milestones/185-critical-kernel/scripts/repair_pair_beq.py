from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel')
p=H/'lean/Share185Proof39.lean'
s=p.read_text().replace('    rw [this, (List.isPerm_iff.mp hm).countP_eq]',"""    have heq : (instBEqProd : BEq (Nat × Nat)) = instBEqOfDecidableEq := by
      apply congrArg BEq.mk
      funext a b
      exact Bool.beq_eq_decide_eq a b
    rw [heq] at hm
    rw [this, (List.isPerm_iff.mp hm).countP_eq]""")
p.write_text(s,newline='\n')
order=json.loads((H/'data/current-order.json').read_text())
d=hashlib.sha256(p.read_bytes()).hexdigest()
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 q=H/'data'/(name+'-execution.json');j=json.loads(q.read_text(encoding='utf-8-sig'));j['source_sha256']['Share185Proof39']=d
 q.write_text(json.dumps(j,indent=2)+'\n')
(H/'scripts/repair_pair_beq.py').write_bytes(Path(__file__).read_bytes())

