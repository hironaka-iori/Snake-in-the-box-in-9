import ContextAssignmentData
import LookupTableCheck

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Retained87 Snake9.Direction77 Snake9.GraphWalk78

/-- This bounded test uses the checked numeric source table, not canonical words. -/
def sourceCompatibleB (di q : Nat) : Bool :=
  q == 0 || recordedCompatible.getD q 0 == sourceIds.getD di 0

def Assigned (di q : Nat) : Prop :=
  let cls := chosenClass di q
  cls < 127 ∧ (di,q) ∈ recordedClassKeys cls ∧
    savedBlockClass (75*di+q) = some cls ∧
    savedRootForBlock (75*di+q) = some (recordedClassRoot cls)

instance (di q : Nat) : Decidable (Assigned di q) := by
  unfold Assigned
  infer_instance

def assignmentAt (di q : Nat) : Bool :=
  if sourceCompatibleB di q then decide (Assigned di q) else true

def assignmentCheck : Bool :=
  (List.range 505).all fun di => (List.range 75).all fun q => assignmentAt di q

/-- The input direction bound is retained to justify decoding its table index.
The target-compatibility conjunct remains in numericKeep but is not needed here. -/
theorem numeric_keep_source (q di code : Nat) (hd : di < 505)
    (hk : numericKeep q di code = true) :
    q < 75 ∧ code < 46656 ∧ sourceCompatibleB di q = true := by
  have hr : rangeCompatibilityKeep (extensions.getD di []) q code = true :=
    (Bool.and_eq_true_iff.mp hk).1
  simp only [rangeCompatibilityKeep,direction_index_getD di hd,
    Bool.and_eq_true_iff,decide_eq_true_eq,Bool.or_eq_true_iff,beq_iff_eq] at hr
  refine ⟨hr.1,hr.2.2.1,?_⟩
  simpa only [sourceCompatibleB,Bool.or_eq_true_iff,beq_iff_eq,
    (recorded_maps_exact di hd).1] using hr.2.2.2.1

theorem assigned_of_check (hcheck : assignmentCheck = true) (di q : Nat)
    (hd : di < 505) (hq : q < 75) (hs : sourceCompatibleB di q = true) :
    Assigned di q := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp hcheck di (List.mem_range.mpr hd))
    q (List.mem_range.mpr hq)
  simpa only [assignmentAt,hs,↓reduceIte,decide_eq_true_eq] using h

/-- The family is an explicit premise; this definition does not assert that the
127 concrete class certificates have all been completed. -/
def ClassMembershipFamily (g : Diagram) : Prop :=
  ∀ cls, cls < 127 → ∀ di q code,
    (di,q) ∈ recordedClassKeys cls → q < 75 → code < 46656 →
    numericKeep q di code = true →
    diagramEval g (recordedClassRoot cls) (digits code) = true

theorem numeric_membership_of_assignment (g : Diagram)
    (hfamily : ClassMembershipFamily g) (hcheck : assignmentCheck = true)
    (q di code : Nat) (hd : di < 505) (hk : numericKeep q di code = true) :
    Assigned di q ∧ diagramEval g (recordedClassRoot (chosenClass di q)) (digits code) = true := by
  obtain ⟨hq,hc,hs⟩ := numeric_keep_source q di code hd hk
  have ha := assigned_of_check hcheck di q hd hq hs
  exact ⟨ha,hfamily (chosenClass di q) ha.1 di q code ha.2.1 hq hc hk⟩

#print axioms numeric_keep_source
#print axioms assigned_of_check
#print axioms numeric_membership_of_assignment
end Snake9.Batch92
