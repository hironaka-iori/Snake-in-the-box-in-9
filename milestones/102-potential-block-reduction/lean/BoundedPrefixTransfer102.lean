import PrefixChecker100

/-! Transfer a small prefix test whose equality to the original potential
inequality is available only on accepted, bounded count codes. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.BoundedPrefixTransfer102
open Snake9.PrefixChecker100 Snake9.PotentialChecker99
open Snake9.DefinedGraph92 Snake9.Certificate88 Snake9.Batch92 Snake9.GraphWalk78

theorem contextCheck_of_bounded_prefix (test : Nat → Bool)
    (w : Nat → Nat → Nat → Nat) (P : Nat) (π : Nat → Nat)
    (di q cls : Nat)
    (hblock : savedBlockClass (75*di+q) = some cls)
    (hcheck : checkPrefix test 6 0 (recordedClassRoot cls) = true)
    (heq : ∀ code, code < 46656 →
      diagramKeep retainedDiagram di q code = true →
      test code =
        decide (P+π (edgeTarget q di code) ≤
          w q di code+π (edgeSource q di code))) :
    contextCheck w P π di q = true := by
  unfold contextCheck
  apply (checkInterval_iff (edgeCheck w P π di q) 0 46656).mpr
  intro code _ hc
  have hcode : code < 46656 := by omega
  cases hkeep : diagramKeep retainedDiagram di q code with
  | false =>
      simp [edgeCheck, hkeep]
  | true =>
      have htest := accepted_code_of_prefix_check test di q cls
        hblock hcheck code hcode hkeep
      have hineq : decide (P+π (edgeTarget q di code) ≤
          w q di code+π (edgeSource q di code)) = true := by
        rw [← heq code hcode hkeep]
        exact htest
      simpa [edgeCheck, hkeep] using hineq

#print axioms contextCheck_of_bounded_prefix
end Snake9.BoundedPrefixTransfer102
