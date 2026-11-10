from pathlib import Path
import json,subprocess,hashlib,re
R=Path('E:/Snake-in-a-box');H=R/'milestones/187-clause-interpretation';read=lambda p:json.loads(p.read_text())
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
commit=subprocess.check_output(git+['rev-parse','e7b21e0c'],cwd=R,text=True).strip()
paths=['handoff/README.md','milestones/33-233-lean/README.md','milestones/33-233-lean/FLOORS.md','milestones/33-233-lean/CERT-PROGRESS.md','work/spectral/stronger/Floors233Main.lean','work/spectral/stronger/AggregateDirection6SConditional.lean','outputs/floors233-linux.log','outputs/aggregate-233-conditional-chain-linux.log','milestones/28-combined-identities/lean/CombinedShareToy.lean','milestones/31-233-cost/data/keys233_best.json.gz']
saved={}
for p in paths:
 raw=subprocess.check_output(git+['show',commit+':'+p],cwd=R);dest=H/'contributors'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw)
 saved[p]={'sha256':hashlib.sha256(raw).hexdigest(),'git_blob':subprocess.check_output(git+['rev-parse',commit+':'+p],cwd=R,text=True).strip()}
(H/'data/contributor-snapshot.json').write_text(json.dumps({'commit':commit,'branch':'research/unconditional-241','files':saved,'independent_local_rebuild':False},indent=2)+'\n')
src=(H/'contributors/milestones/28-combined-identities/lean/CombinedShareToy.lean').read_text()
assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b|#eval|run_cmd',src)
src='import Std\n'+src.replace('namespace Combined\n','namespace Combined187\n').replace('end Combined\n','end Combined187\n').replace('Combined.combined_bound','Combined187.combined_bound').replace('Combined.m_le_233','Combined187.m_le_233')
(H/'lean/Combined187.lean').write_text(src,encoding='utf-8',newline='\n')
src='''import Combined187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Combined187

theorem rsum_const (q n : Nat) : rsum (fun _ => q) n = q*n := by
  induction n with
  | zero => simp [rsum]
  | succ n ih => simp only [rsum,ih,Nat.mul_succ]

theorem boundary_twenty_two (A : Nat → Nat) (m : Nat)
    (h0 : 4 ≤ A 0) (hm : 4 ≤ A m)
    (h6 : 14 ≤ A 1 + A 2 + A 3 + A 4 + A 5 + A 6) :
    22 ≤ rsum A 7 + A m := by
  simp only [rsum]
  omega

theorem budget_with_share_slack (m q L : Nat) (A sh sym S5 : Nat → Nat)
    (hm : 7 ≤ m)
    (hS5 : ∀ n, n < m-7 → S5 n ≤ sh (n+3)+sh (n+4)+sh (n+5)+sh (n+6)+sh (n+7)+q)
    (hsym : ∀ j, sym j ≤ A j)
    (hb : 22 ≤ rsum A 7 + A m)
    (hid : rsum (fun k => 24*A k+sh k) (m+1)+840*(m+1)+L ≤ 221136) :
    rsum (fun n => 120*sym (n+7)+S5 n) (m-7)+4200*m+5*L ≤ 1098840+q*(m-7) := by
  have hw : rsum S5 (m-7) ≤ 5*rsum sh (m+1)+q*(m-7) := by
    have h := rsum_mono S5 _ (m-7) hS5
    rw [rsum_add,rsum_const] at h
    have h2 := window5 sh (m-7)
    rw [show m-7+8=m+1 by omega] at h2
    omega
  have ha : rsum (fun n => sym (n+7)) (m-7) ≤ rsum (fun n => A (n+7)) (m-7) :=
    rsum_mono _ _ _ (fun k _ => hsym (k+7))
  have hs := rsum_shift A 7 (m-7)
  rw [show m-7+7=m by omega] at hs
  have he : rsum A (m+1)=rsum A m+A m := rfl
  rw [rsum_add,rsum_mul] at hid
  rw [rsum_add,rsum_mul]
  omega

theorem four_point_slack (m W L : Nat) (hm : 7 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+4*(m-7))
    (ht : 520*(m-7) ≤ W+1023) :
    4716*m+5*L ≤ 1103475 ∧ m ≤ 233 := by omega

theorem five_point_slack (m W L : Nat) (hm : 7 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (ht : 520*(m-7) ≤ W+784) :
    4715*m+5*L ≤ 1103229 ∧ m ≤ 233 := by omega

theorem encoded_range_five_point_obstruction :
    520*(234-7) ≤ 117017+1023 ∧
    117017+4200*234 ≤ 1098840+5*(234-7) := by decide +kernel

theorem exact_range_six_point_obstruction :
    520*(234-7) ≤ 117256+784 ∧
    117256+4200*234 ≤ 1098840+6*(234-7) := by decide +kernel

#print axioms rsum_const
#print axioms boundary_twenty_two
#print axioms budget_with_share_slack
#print axioms four_point_slack
#print axioms five_point_slack
#print axioms encoded_range_five_point_obstruction
#print axioms exact_range_six_point_obstruction
end Combined187
'''
(H/'lean/BoundarySlack187.lean').write_text(src,encoding='utf-8',newline='\n')
order=['Combined187','BoundarySlack187'];base=read(H/'data/Share187.Compose-execution.json')
base['new_module_order']+=order
for n in order:base['source_sha256'][n]=hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest()
for n in order:(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/boundary-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/prepare_boundary.py').write_bytes(Path(__file__).read_bytes())
print('Saved contributor snapshot and new boundary/slack deductions; not yet Lean-checked.')
