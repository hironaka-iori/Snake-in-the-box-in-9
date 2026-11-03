import LratFast144

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.RawInit144

open Snake9.LocalWindow
open Snake9.Lrat144 (Tree TreeTrue rawMask rawMask_true)
open Snake9.LratFast144 (perf perf_true)

noncomputable def rawPre : Nat → Nat → List (List Nat) → Tree × List (List Nat)
  | 0, _, cs => (.nil, cs)
  | d + 1, b, [] => (perf (d + 1) b, [])
  | d + 1, b, c :: cs =>
    let left := rawPre d b cs
    let right := rawPre d (b + 2 ^ d) left.2
    (.node (b + 2 ^ d) (rawMask c) left.1 right.1, right.2)

theorem rawPre_true (τ : Nat → Bool) : ∀ d b raw,
    (raw.map (·.map decodeLit)).all (clauseTrue τ) = true →
    TreeTrue τ (rawPre d b raw).1 ∧
      ((rawPre d b raw).2.map (·.map decodeLit)).all (clauseTrue τ) = true := by
  intro d
  induction d with
  | zero =>
    intro b raw h
    exact ⟨.nil, h⟩
  | succ d ih =>
    intro b raw h
    cases raw with
    | nil => exact ⟨perf_true τ (d + 1) b, rfl⟩
    | cons c cs =>
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h
      have left := ih b cs h.2
      have right := ih (b + 2 ^ d) (rawPre d b cs).2 left.2
      exact ⟨.node (rawMask_true τ c h.1) left.1 right.1, right.2⟩

theorem start_true (τ : Nat → Bool) {raw : List (List Nat)} {h : Nat}
    (hr : cnfTrue τ (raw.map (·.map decodeLit)) = true) :
    TreeTrue τ (rawPre h 0 raw).1 :=
  (rawPre_true τ h 0 raw hr).1

end Snake9.RawInit144

#print axioms Snake9.RawInit144.rawPre_true
#print axioms Snake9.RawInit144.start_true
