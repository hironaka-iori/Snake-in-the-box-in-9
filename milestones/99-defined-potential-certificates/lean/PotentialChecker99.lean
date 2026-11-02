import PotentialAssembly98
import BalancedLookup

/-! Context and interval potential checks. Soundness uses generated_row_iff
without evaluating generatedRows. Concrete checks are separate obligations. -/
namespace Snake9.PotentialChecker99
open Snake9.GraphWalk78 Snake9.Weights98 Snake9.DefinedGraph92
open Snake9.Assembly87 Snake9.Enumeration87 Snake9.Certificate88 Snake9.Batch92
set_option maxHeartbeats 2000000

/-- Check precisely the half-open interval [start,start+count). -/
def checkInterval (test : Nat → Bool) (start count : Nat) : Bool :=
  (List.range count).all fun i => test (start+i)

theorem checkInterval_iff (test : Nat → Bool) (start count : Nat) :
    checkInterval test start count = true ↔
      ∀ code, start ≤ code → code < start+count → test code = true := by
  unfold checkInterval
  constructor
  · intro h code hlo hhi
    have hi : code-start < count := by omega
    have htest := List.all_eq_true.mp h (code-start) (List.mem_range.mpr hi)
    have he : start+(code-start)=code := by omega
    simpa only [he] using htest
  · intro h
    apply List.all_eq_true.mpr
    intro i hi
    have hic : i < count := List.mem_range.mp hi
    exact h (start+i) (by omega) (by omega)

/-- Join adjacent intervals without reevaluating either finite check. -/
theorem checkInterval_join (test : Nat → Bool) (start left right : Nat)
    (hl : checkInterval test start left = true)
    (hr : checkInterval test (start+left) right = true) :
    checkInterval test start (left+right) = true := by
  apply (checkInterval_iff test start (left+right)).mpr
  intro code hlo hhi
  by_cases hleft : code < start+left
  · exact (checkInterval_iff test start left).mp hl code hlo hleft
  · exact (checkInterval_iff test (start+left) right).mp hr code
      (by omega) (by omega)

/-- An optimized Boolean test may replace the original on the checked
interval. In particular, its keep predicate may use an equal fast lookup. -/
theorem checkInterval_transfer (fast original : Nat → Bool) (start count : Nat)
    (heq : ∀ code, start ≤ code → code < start+count →
      fast code = original code)
    (hfast : checkInterval fast start count = true) :
    checkInterval original start count = true := by
  apply (checkInterval_iff original start count).mpr
  intro code hlo hhi
  rw [← heq code hlo hhi]
  exact (checkInterval_iff fast start count).mp hfast code hlo hhi

theorem checkInterval_of_chunks (test : Nat → Bool) (width chunks : Nat)
    (hchunks : ∀ j < chunks, checkInterval test (j*width) width = true) :
    checkInterval test 0 (chunks*width) = true := by
  revert hchunks
  induction chunks with
  | zero =>
    intro _
    simp [checkInterval]
  | succ n ih =>
    intro hchunks
    have hfirst := ih (fun j hj => hchunks j (by omega))
    have hlast := hchunks n (Nat.lt_succ_self n)
    have hjoin := checkInterval_join test 0 (n*width) width hfirst
      (by simpa only [Nat.zero_add] using hlast)
    simpa only [Nat.succ_mul] using hjoin

/-- Weight arguments are (history,direction,code), matching Weights98. -/
def edgeCheck (w : Nat → Nat → Nat → Nat) (P : Nat) (π : Nat → Nat)
    (di q code : Nat) : Bool :=
  if diagramKeep retainedDiagram di q code then
    decide (P+π (edgeTarget q di code) ≤ w q di code+π (edgeSource q di code))
  else true

def contextCheck (w : Nat → Nat → Nat → Nat) (P : Nat) (π : Nat → Nat)
    (di q : Nat) : Bool :=
  checkInterval (edgeCheck w P π di q) 0 46656

/-- Complete executable specification. Concrete proofs should assemble
separate contexts and chunks rather than reduce this whole Boolean at once. -/
def graphCheck (w : Nat → Nat → Nat → Nat) (P : Nat) (π : Nat → Nat) : Bool :=
  (List.range 505).all fun di =>
    (List.range 75).all fun q => contextCheck w P π di q

theorem edgeCheck_sound (w : Nat → Nat → Nat → Nat) (P : Nat) (π : Nat → Nat)
    (di q code : Nat) (hcheck : edgeCheck w P π di q code = true)
    (hkeep : diagramKeep retainedDiagram di q code = true) :
    P+π (edgeTarget q di code) ≤ w q di code+π (edgeSource q di code) := by
  simpa [edgeCheck, hkeep] using hcheck

theorem contextCheck_sound (w : Nat → Nat → Nat → Nat) (P : Nat) (π : Nat → Nat)
    (di q code : Nat) (hcheck : contextCheck w P π di q = true)
    (hcode : code < 46656)
    (hkeep : diagramKeep retainedDiagram di q code = true) :
    P+π (edgeTarget q di code) ≤ w q di code+π (edgeSource q di code) := by
  have hinterval : checkInterval (edgeCheck w P π di q) 0 46656 = true := hcheck
  have htest := (checkInterval_iff (edgeCheck w P π di q) 0 46656).mp
    hinterval code (Nat.zero_le _) (by omega)
  exact edgeCheck_sound w P π di q code htest hkeep

/-- For example,216 chunks of216 codes cover a context. -/
theorem contextCheck_of_chunks (w : Nat → Nat → Nat → Nat)
    (P : Nat) (π : Nat → Nat) (di q width chunks : Nat)
    (hsize : chunks*width = 46656)
    (hchunks : ∀ j < chunks,
      checkInterval (edgeCheck w P π di q) (j*width) width = true) :
    contextCheck w P π di q = true := by
  unfold contextCheck
  rw [← hsize]
  exact checkInterval_of_chunks (edgeCheck w P π di q) width chunks hchunks

/-- Missing blocks need no code-by-code certificate. -/
theorem contextCheck_missing (w : Nat → Nat → Nat → Nat)
    (P : Nat) (π : Nat → Nat) (di q : Nat)
    (hmissing : savedBlockClass (75*di+q) = none) :
    contextCheck w P π di q = true := by
  unfold contextCheck
  apply (checkInterval_iff (edgeCheck w P π di q) 0 46656).mpr
  intro code _ _
  simp [edgeCheck, diagramKeep, hmissing]

/-- Obtain the exact98 row premise from bounded context certificates. -/
theorem row_potential_of_context_checks (w : Nat → Nat → Nat → Nat)
    (P : Nat) (π : Nat → Nat)
    (hcontexts : ∀ di < 505, ∀ q < 75, contextCheck w P π di q = true) :
    ∀ row ∈ (rows retainedDiagram).toList,
      P+π (rowTarget row) ≤ w row.2.1 row.1 row.2.2+π (rowSource row) := by
  intro row hrow
  rcases row with ⟨di, q, code⟩
  have hgenerated : (di,q,code) ∈ generatedRows (diagramKeep retainedDiagram) := by
    simpa only [rows, List.toList_toArray] using hrow
  obtain ⟨hd, hq, hc, hkeep⟩ :=
    (generated_row_iff (diagramKeep retainedDiagram) di q code).mp hgenerated
  change P+π (edgeTarget q di code) ≤ w q di code+π (edgeSource q di code)
  exact contextCheck_sound w P π di q code (hcontexts di hd q hq) hc hkeep

theorem graphCheck_sound (w : Nat → Nat → Nat → Nat) (P : Nat) (π : Nat → Nat)
    (hcheck : graphCheck w P π = true) :
    ∀ row ∈ (rows retainedDiagram).toList,
      P+π (rowTarget row) ≤ w row.2.1 row.1 row.2.2+π (rowSource row) := by
  apply row_potential_of_context_checks w P π
  intro di hd q hq
  unfold graphCheck at hcheck
  exact List.all_eq_true.mp
    (List.all_eq_true.mp hcheck di (List.mem_range.mpr hd))
    q (List.mem_range.mpr hq)

theorem weight_potential_of_context_checks (floor : Nat → Nat)
    (P : Nat) (π : Nat → Nat)
    (hcontexts : ∀ di < 505, ∀ q < 75,
      contextCheck (weight floor) P π di q = true) :
    ∀ row ∈ (rows retainedDiagram).toList,
      P+π (rowTarget row) ≤
        weight floor row.2.1 row.1 row.2.2+π (rowSource row) :=
  row_potential_of_context_checks (weight floor) P π hcontexts

/-- A clipped raw function meets the range premise without a finite scan. -/
theorem min_potential_range (R : Nat) (raw : Nat → Nat) :
    ∀ s < 1601856, min R (raw s) ≤ R := by
  intro s _
  exact Nat.min_le_left R (raw s)

#print axioms checkInterval_iff
#print axioms checkInterval_join
#print axioms checkInterval_transfer
#print axioms checkInterval_of_chunks
#print axioms edgeCheck_sound
#print axioms contextCheck_sound
#print axioms contextCheck_of_chunks
#print axioms contextCheck_missing
#print axioms row_potential_of_context_checks
#print axioms graphCheck_sound
#print axioms weight_potential_of_context_checks
#print axioms min_potential_range
end Snake9.PotentialChecker99
