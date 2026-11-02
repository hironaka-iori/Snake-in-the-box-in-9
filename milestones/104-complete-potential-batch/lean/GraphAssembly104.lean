import PotentialChecker99

/-! Assemble the original graph checker from certificates for saved blocks.
Missing contexts are discharged by the existing semantic theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.GraphAssembly104
open Snake9.PotentialChecker99 Snake9.Batch92

theorem graphCheck_of_saved_blocks (w : Nat → Nat → Nat → Nat)
    (P : Nat) (π : Nat → Nat)
    (hblocks : ∀ entry ∈ savedBlockClasses,
      contextCheck w P π (entry.1/75) (entry.1%75) = true) :
    graphCheck w P π = true := by
  unfold graphCheck
  apply List.all_eq_true.mpr
  intro di _
  apply List.all_eq_true.mpr
  intro q hq
  have hq75 : q < 75 := List.mem_range.mp hq
  cases hfind : savedBlockClasses.find? (fun item => item.1 == 75*di+q) with
  | none =>
      apply contextCheck_missing w P π di q
      simp only [savedBlockClass, hfind, Option.map_none']
  | some entry =>
      have hmem : entry ∈ savedBlockClasses := List.mem_of_find?_eq_some hfind
      have hmatch : (entry.1 == 75*di+q) = true :=
        List.find?_some (p := fun item : Nat × Nat => item.1 == 75*di+q) hfind
      have hkey : entry.1 = 75*di+q := by
        simpa only [beq_iff_eq] using hmatch
      have hdi : entry.1/75 = di := by omega
      have hq' : entry.1%75 = q := by omega
      simpa only [hdi, hq'] using hblocks entry hmem

#print axioms graphCheck_of_saved_blocks
end Snake9.GraphAssembly104
