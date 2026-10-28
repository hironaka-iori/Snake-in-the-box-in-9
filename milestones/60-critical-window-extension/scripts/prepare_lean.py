from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
probe=json.loads((HERE/'data/probe.json').read_text());records=probe['records']
for start in [0,10]:
    text=['import GenericWindow','namespace Snake9.LocalWindow.CriticalExtension60',
          'open ForcedShare58 ExtendedShare59','set_option maxHeartbeats 0','set_option maxRecDepth 100000']
    for i,r in enumerate(records[start:start+10],start):
        text.append(f'''
namespace T{i:02d}
def W : List Nat := {r['vertices']}
def ds : List Nat := {r['directions']}
def D : List Nat := {r['forced_absent']}
def C : List Nat := {r['centres']}
def mask : Nat := {sum(1<<x for x in r['forced_absent'])}
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : {r['geometric_lower']} ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    {r['geometric_lower']} ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:={r['geometric_lower']}) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T{i:02d}
''')
    text.append('end Snake9.LocalWindow.CriticalExtension60')
    (HERE/'lean'/f'TenBatch{start//10}.lean').write_text('\n'.join(text),encoding='utf-8')
def canon(ds):
    labels={};return tuple(labels.setdefault(x,len(labels)) for x in ds)
controls=[];text=['import GenericWindow','namespace Snake9.LocalWindow.CriticalExtension60',
                 'set_option maxHeartbeats 0','set_option maxRecDepth 100000']
for i in [14,15,16]:
    r=records[i];nxt=records[(i+1)%20]
    candidates=[r['directions']+[d] for d in range(min(9,max(r['directions'])+2)) if canon(r['directions'][1:]+[d])==tuple(nxt['directions'])]
    assert len(candidates)==1;ds=candidates[0];W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    controls.append(dict(phase=i,directions=ds,vertices=W))
    text.append(f'''
namespace F{i}
def W : List Nat := {W}
def ds : List Nat := {ds}
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2 ≤ cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F{i}
''')
text.append('end Snake9.LocalWindow.CriticalExtension60')
(HERE/'lean/ValidityControls.lean').write_text('\n'.join(text),encoding='utf-8')
(HERE/'data/validity-controls.json').write_text(json.dumps(controls,indent=2)+'\n')
weights=[records[i]['weight'] for i in probe['chosen']]
(HERE/'lean/CycleArithmetic.lean').write_text(f'''import Mathlib.Tactic
namespace Snake9.CriticalArithmetic60
theorem cycle_weight : ({weights} : List Nat).sum = 9912 := by decide +kernel
theorem insufficient (mu rho : ℚ) (hm : mu≤2478/5) (hr : 0≤rho) :
    235*(4200+mu) ≤ 1099560+9*mu+rho := by linarith
theorem generic_budget (n m G W : ℤ)
    (hg : G+840*(m+1)≤221136) (hw : W+120*(n+6)≤5*G) :
    W+4200*m≤1100760-120*n := by linarith
theorem generic_potential (n m p d W R : ℤ) (hd : 0≤d)
    (hb : W+4200*m≤1100760-120*n)
    (hp : p*(m-(n-1))≤d*W+R) :
    (p+4200*d)*m≤(1100760-120*n)*d+(n-1)*p+R := by
  have := mul_le_mul_of_nonneg_left hb hd
  nlinarith
#print axioms cycle_weight
#print axioms insufficient
#print axioms generic_budget
#print axioms generic_potential
end Snake9.CriticalArithmetic60
''')
print('Generated twenty share instances and three validity controls')
