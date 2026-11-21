import CubeBridge3
/-! Provenance of a clause of `cubeCnfQ`: a tag (family code and parameters) from which the clause is
regenerated, with a proof that every clause so generated is in `cubeCnfQ`.  A certificate then checks
`core.all (fun p => genQ c L A k p.1 == some p.2)` instead of walking the whole generated CNF. -/
namespace Dim8Lift.Prov
open Dim8Lift.Cnf Dim8Lift.Cube

/-- the counter blocks of `famCnt`: block 0 (endpoints), 1 (unselected), 2 + q (subcube q) -/
def blk (c L k b : Nat) : Nat × Nat × List Int :=
  if b = 0 then (cbase, 2 * c, endLits)
  else if b = 1 then (cbase + 512 * (2 * c), 256 - L, unselLits)
  else (cbase + 512 * (2 * c) + 256 * (256 - L) + (b - 2) * 256 * k, k, (subcubes.getD (b - 2) []).map fun u => pos (sV u))

/-- clause of `atMost base k xs` by kind (0..6) and indices (`i0`, `j0` as in the definition) -/
def amClause (base k : Nat) (xs : List Int) (kind i0 j0 : Nat) : List Int :=
  let x := fun i => xs.getD (i - 1) 0
  let i := i0 + 2
  match kind with
  | 0 => [negLit (x 1), pos (reg base k 1 1)]
  | 1 => [neg (reg base k 1 (j0 + 2))]
  | 2 => [negLit (x i), pos (reg base k i 1)]
  | 3 => [neg (reg base k (i - 1) 1), pos (reg base k i 1)]
  | 4 => [negLit (x i), neg (reg base k (i - 1) k)]
  | 5 => [negLit (x i), neg (reg base k (i - 1) (j0 + 2 - 1)), pos (reg base k i (j0 + 2))]
  | _ => [neg (reg base k (i - 1) (j0 + 2)), pos (reg base k i (j0 + 2))]

def amValid (k n kind i0 j0 : Nat) : Bool :=
  decide (1 ≤ n) && match kind with
  | 0 => true
  | 1 => decide (j0 < k - 1)
  | 2 | 3 | 4 => decide (i0 < n - 1)
  | 5 | 6 => decide (i0 < n - 1) && decide (j0 < k - 1)
  | _ => false

theorem am_mem (base k : Nat) (xs : List Int) (kind i0 j0 : Nat) (h : amValid k xs.length kind i0 j0 = true) :
    amClause base k xs kind i0 j0 ∈ atMost base k xs := by
  have hne : xs ≠ [] := by
    intro e; subst e; simp [amValid] at h
  unfold atMost; rw [if_neg hne]
  simp only [amValid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, h⟩ := h
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.mem_flatMap]
  match kind, h with
  | 0, _ => left; left; rfl
  | 1, h => left; right; exact ⟨j0, by simpa using h, rfl⟩
  | 2, h => right; exact ⟨i0, by simpa using h, by left; rfl⟩
  | 3, h => right; exact ⟨i0, by simpa using h, by right; left; rfl⟩
  | 4, h => right; exact ⟨i0, by simpa using h, by right; right; left; rfl⟩
  | 5, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    right; exact ⟨i0, h.1, by right; right; right; exact ⟨j0, h.2, by simp [amClause]⟩⟩
  | 6, h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    right; exact ⟨i0, h.1, by right; right; right; exact ⟨j0, h.2, by simp [amClause]⟩⟩
  | n + 7, h => simp at h

def genQ (c L A k : Nat) : List Nat → Option (List Int)
  | [0, u] => if u < 64 then some (if A.testBit u then [pos (sV u)] else [neg (sV u)]) else none
  | [1, u, a, b, d] => if u < 256 ∧ a < b ∧ b < d ∧ d < 8 then
      some [neg (sV u), neg (sV (fx u a)), neg (sV (fx u b)), neg (sV (fx u d))] else none
  | [2, u, j0] => if u < 256 ∧ j0 < 63 then some [neg (oV u (j0 + 2)), pos (oV u (j0 + 1))] else none
  | [3, u] => if u < 256 then some (neg (twoV u) :: (List.range 8).map fun i => pos (qV u i)) else none
  | [4, u, i] => if u < 256 ∧ i < 8 then some [neg (qV u i), pos (sV (fx u i))] else none
  | [5, u, i] => if u < 256 ∧ i < 8 then some [neg (qV u i), pos (oV u 1)] else none
  | [6, u, i] => if u < 256 ∧ i < 8 then some [neg (qV u i), neg (oV (fx u i) 64)] else none
  | [7, u, i, j0] => if u < 256 ∧ i < 8 ∧ j0 < 63 then
      some [neg (qV u i), neg (oV (fx u i) (j0 + 1)), pos (oV u (j0 + 2))] else none
  | [8, u, a, b, r] => if u < 256 ∧ a < b ∧ b < 8 ∧ r < 4 then some ((defPair u a b).getD r []) else none
  | [9, u] => if u < 256 then some (defTwo u) else none
  | [10, u, a] => if u < 256 ∧ a < 8 then some (defAny1 u a) else none
  | [11, u] => if u < 256 then some (defAny u) else none
  | [12, u, r] => if u < 256 ∧ r < 6 then some ((defE u).getD r []) else none
  | [13, u, a, b] => if u < 256 ∧ a < b ∧ b < 8 ∧ (u.testBit a || u.testBit b) = false then
      some [neg (sV u), neg (sV (fx u a)), neg (sV (fx (fx u a) b)), neg (sV (fx u b))] else none
  | [14, b, kind, i0, j0] =>
      if b < 2 + subcubes.length ∧ amValid (blk c L k b).2.1 (blk c L k b).2.2.length kind i0 j0 = true then
        some (amClause (blk c L k b).1 (blk c L k b).2.1 (blk c L k b).2.2 kind i0 j0) else none
  | _ => none

theorem getD_mem {l : List (List Int)} {r : Nat} (h : r < l.length) : l.getD r [] ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem m_fix {A u : Nat} (hu : u < 64) : (if A.testBit u then [pos (sV u)] else [neg (sV u)]) ∈ famFix A :=
  List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩
theorem m_deg {u a b d : Nat} (hu : u < 256) (h1 : a < b) (h2 : b < d) (h3 : d < 8) :
    [neg (sV u), neg (sV (fx u a)), neg (sV (fx u b)), neg (sV (fx u d))] ∈ famDeg :=
  List.mem_flatMap.mpr ⟨u, mem_R256.mpr hu, List.mem_map.mpr ⟨(a, b, d), mem_triples8.mpr ⟨h1, h2, h3⟩, rfl⟩⟩
theorem m_lvl {u : Nat} {cl : List Int} (hu : u < 256) (h : cl ∈ lvlQU u) : cl ∈ famLvlQ :=
  List.mem_flatMap.mpr ⟨u, mem_R256.mpr hu, h⟩
theorem m_def {u : Nat} {cl : List Int} (hu : u < 256) (h : cl ∈ defU u) : cl ∈ famDef :=
  List.mem_flatMap.mpr ⟨u, mem_R256.mpr hu, h⟩
theorem m_q {u i : Nat} {cl : List Int} (hi : i < 8)
    (h : cl ∈ [neg (qV u i), pos (sV (fx u i))] :: [neg (qV u i), pos (oV u 1)] ::
      [neg (qV u i), neg (oV (fx u i) 64)] ::
      (List.range 63).map fun j0 => [neg (qV u i), neg (oV (fx u i) (j0 + 1)), pos (oV u (j0 + 2))]) : cl ∈ lvlQU u := by
  unfold lvlQU; apply List.mem_append_right; apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, h⟩

theorem genQ_mem {c L A k : Nat} {t : List Nat} {cl : List Int} (h : genQ c L A k t = some cl) :
    cl ∈ cubeCnfQ c L A k := by
  unfold cubeCnfQ
  simp only [List.mem_append]
  unfold genQ at h
  split at h
  next u =>
    split at h
    · simp only [Option.some.injEq] at h; subst h; left; left; left; left; left; exact m_fix (by assumption)
    · simp at h
  next u a b d =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; left; left; right; exact m_deg hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · simp at h
  next u j0 =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; left; right; apply m_lvl hc.1; unfold lvlQU lvlMono
      apply List.mem_append_left; exact List.mem_map.mpr ⟨j0, List.mem_range.mpr hc.2, rfl⟩
    · simp at h
  next u =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; left; right; apply m_lvl hc; unfold lvlQU
      apply List.mem_append_right; exact List.mem_cons_self
    · simp at h
  next u i =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; left; right; exact m_lvl hc.1 (m_q hc.2 (by simp))
    · simp at h
  next u i =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; left; right; exact m_lvl hc.1 (m_q hc.2 (by simp))
    · simp at h
  next u i =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; left; right; exact m_lvl hc.1 (m_q hc.2 (by simp))
    · simp at h
  next u i j0 =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; left; right; refine m_lvl hc.1 (m_q hc.2.1 ?_)
      simp only [List.mem_cons, List.mem_map, List.mem_range]
      right; right; right; exact ⟨j0, hc.2.2, rfl⟩
    · simp at h
  next u a b r =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; right; apply m_def hc.1; unfold defU
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨(a, b), mem_pairs8.mpr ⟨hc.2.1, hc.2.2.1⟩,
        getD_mem (by simp [defPair]; exact hc.2.2.2)⟩
    · simp at h
  next u =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; right; apply m_def hc; unfold defU
      apply List.mem_append_left; apply List.mem_append_right; exact List.mem_cons_self
    · simp at h
  next u a =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; right; apply m_def hc.1; unfold defU
      apply List.mem_append_left; apply List.mem_append_right; apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨a, List.mem_range.mpr hc.2, rfl⟩
    · simp at h
  next u =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; right; apply m_def hc; unfold defU
      apply List.mem_append_right; exact List.mem_cons_self
    · simp at h
  next u r =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; left; right; apply m_def hc.1; unfold defU
      apply List.mem_append_right; apply List.mem_cons_of_mem
      exact getD_mem (by simp [defE]; exact hc.2)
    · simp at h
  next u a b =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      left; right; unfold famC4
      refine List.mem_flatMap.mpr ⟨u, mem_R256.mpr hc.1, List.mem_filterMap.mpr ⟨(a, b), mem_pairs8.mpr ⟨hc.2.1, hc.2.2.1⟩, ?_⟩⟩
      simp only [hc.2.2.2]; rfl
    · simp at h
  next b kind i0 j0 =>
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      right
      have hm := am_mem (blk c L k b).1 (blk c L k b).2.1 (blk c L k b).2.2 kind i0 j0 hc.2
      unfold famCnt
      unfold blk at hm ⊢
      by_cases h0 : b = 0
      · simp only [h0, if_true] at hm ⊢; exact List.mem_append_left _ (List.mem_append_left _ hm)
      · by_cases h1 : b = 1
        · simp only [h1, if_true, show (1 : Nat) ≠ 0 from by decide, if_false] at hm ⊢
          exact List.mem_append_left _ (List.mem_append_right _ hm)
        · simp only [h0, h1, if_false] at hm ⊢
          apply List.mem_append_right
          exact List.mem_flatMap.mpr ⟨b - 2, List.mem_range.mpr (by omega), hm⟩
    · simp at h
  next => simp at h

/-- `core`: pairs (tag, clause in `decodeLit` code) -/
def coreOk (c L A k : Nat) (core : List (List Nat × List Nat)) : Bool :=
  core.all fun p => genQ c L A k p.1 == some (p.2.map Snake9.LocalWindow.decodeLit)

theorem coreOk_append (c L A k : Nat) (a b : List (List Nat × List Nat)) :
    coreOk c L A k (a ++ b) = (coreOk c L A k a && coreOk c L A k b) := by
  simp [coreOk, List.all_append]

theorem unsat_of_prov {c L A k : Nat} (core : List (List Nat × List Nat)) (h : coreOk c L A k core = true)
    (hU : Snake9.LocalWindow.Unsat (core.map fun p => p.2.map Snake9.LocalWindow.decodeLit)) :
    Snake9.LocalWindow.Unsat (cubeCnfQ c L A k) := by
  intro τ
  cases hf : Snake9.LocalWindow.cnfTrue τ (cubeCnfQ c L A k)
  · rfl
  · exfalso
    have hc : Snake9.LocalWindow.cnfTrue τ (core.map fun p => p.2.map Snake9.LocalWindow.decodeLit) = true := by
      unfold Snake9.LocalWindow.cnfTrue at *
      rw [List.all_eq_true] at *
      intro cl hcl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcl
      have := List.all_eq_true.mp h p hp
      simp only [beq_iff_eq] at this
      exact hf _ (genQ_mem this)
    rw [hU τ] at hc; exact absurd hc (by simp)

/-- all tags (for the exporter) -/
def allTags (c L k : Nat) : List (List Nat) :=
  (List.range 64).map (fun u => [0, u]) ++
  (List.range 256).flatMap (fun u =>
    (triples8.map fun (a, b, d) => [1, u, a, b, d]) ++ (List.range 63).map (fun j => [2, u, j]) ++ [[3, u]] ++
    (List.range 8).flatMap (fun i => [[4, u, i], [5, u, i], [6, u, i]] ++ (List.range 63).map fun j => [7, u, i, j]) ++
    (pairs8.flatMap fun (a, b) => (List.range 4).map fun r => [8, u, a, b, r]) ++ [[9, u]] ++
    (List.range 8).map (fun a => [10, u, a]) ++ [[11, u]] ++ (List.range 6).map (fun r => [12, u, r]) ++
    (pairs8.map fun (a, b) => [13, u, a, b])) ++
  (List.range (2 + subcubes.length)).flatMap (fun b =>
    let n := (blk c L k b).2.2.length; let kk := (blk c L k b).2.1
    [14, b, 0, 0, 0] :: (List.range (kk - 1)).map (fun j => [14, b, 1, 0, j]) ++
    (List.range (n - 1)).flatMap (fun i => [[14, b, 2, i, 0], [14, b, 3, i, 0], [14, b, 4, i, 0]] ++
      (List.range (kk - 1)).flatMap fun j => [[14, b, 5, i, j], [14, b, 6, i, j]]))

end Dim8Lift.Prov

#print axioms Dim8Lift.Prov.unsat_of_prov
