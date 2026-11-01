import AggregateWindowConditional
import LocalWindowBridge

/-!
# The bounds 242 and 241 from the 22 local window certificates

`LocalWindowBridge` (core) shows that the 22 certificate statements `AllRefuted`
exclude the certified count patterns of `coreAlpha`, the singleton count computed on
natural numbers.  This module identifies `coreAlpha` with `localAlpha` and discharges
the premises of `upper_242_of_certified_windows` and `upper_241_of_certified_windows`.
The only remaining hypothesis is `AllRefuted`, which the certificate modules
`LocalWindowCnf.*` prove.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate LocalWindow
noncomputable section

theorem inPath_iff_sel {m : Nat} (p : Snake m) (v : Vertex) :
    InPath p v ↔ sel p (fun w => w) v.val = true := by
  rw [sel_iff]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i.val, by omega, ?_⟩
    show vx p i.val = (p.vertex i).val
    simp [vx, i.isLt]
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨i, by omega⟩, Fin.ext ?_⟩
    have h' : vx p i = v.val := h
    simpa [vx, show i < m + 1 by omega] using h'

theorem flip_val (a : Coord) (v : Vertex) : (flip a v).val = v.val ^^^ 2 ^ a.val := rfl

/-- `localAlpha` is the core singleton count `coreAlpha`. -/
theorem localAlpha_eq_coreAlpha {m : Nat} (p : Snake m) (k : Nat) (hk : k < m + 1) :
    localAlpha p ⟨k, hk⟩ = coreAlpha p k := by
  have hx : InPath p (p.vertex ⟨k, hk⟩) := ⟨_, rfl⟩
  have hc : vx p k = (p.vertex ⟨k, hk⟩).val := by simp [vx, hk]
  have hterm : ∀ ab : AxisPair, SquareIncidence.singleton p ab (p.vertex ⟨k, hk⟩) =
      if singPred (sel p (fun w => w)) (p.vertex ⟨k, hk⟩).val (ab.val.1.val, ab.val.2.val) = true
      then 1 else 0 := by
    intro ab
    unfold SquareIncidence.singleton singPred
    simp only [inPath_iff_sel, flip_val, Nat.one_shiftLeft]
    simp only [inPath_iff_sel] at hx
    cases h1 : sel p (fun w => w) ((p.vertex ⟨k, hk⟩).val ^^^ 2 ^ ab.val.1.val) <;>
    cases h2 : sel p (fun w => w) ((p.vertex ⟨k, hk⟩).val ^^^ 2 ^ ab.val.2.val) <;>
    cases h3 : sel p (fun w => w)
      ((p.vertex ⟨k, hk⟩).val ^^^ 2 ^ ab.val.1.val ^^^ 2 ^ ab.val.2.val) <;>
    simp [hx]
  unfold localAlpha coreAlpha singCount
  rw [Finset.sum_congr rfl (fun ab _ => hterm ab), Finset.sum_boole, hc, Nat.cast_id,
    ← List.toFinset_card_of_nodup ((freePairs_nodup 9 (by omega) 9 (by omega)).filter _)]
  apply Finset.card_bij (fun ab _ => (ab.val.1.val, ab.val.2.val))
  · intro ab hab
    rw [Finset.mem_filter] at hab
    rw [List.mem_toFinset, List.mem_filter, mem_freePairs]
    exact ⟨⟨ab.2, ab.val.2.isLt, by omega, by omega, by omega, by omega⟩, hab.2⟩
  · intro a₁ _ a₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  · intro b hb
    obtain ⟨u, w⟩ := b
    rw [List.mem_toFinset, List.mem_filter, mem_freePairs] at hb
    obtain ⟨⟨h1, h2, -⟩, h3⟩ := hb
    refine ⟨⟨(⟨u, by omega⟩, ⟨w, h2⟩), h1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h3⟩

/-- At an internal vertex, `localAlpha` is the absent-corner count over the coordinate
pairs avoiding the two path directions. -/
theorem localAlpha_eq_absentCorners {m : Nat} (p : Snake m) (k : Nat) (h0 : 0 < k) (hm : k < m) :
    localAlpha p ⟨k, by omega⟩ =
      absentCorners (sel p (fun v => v)) (vx p k) (dir p (k - 1)) (dir p k) := by
  rw [localAlpha_eq_coreAlpha, absentCorners_eq_coreAlpha p h0 hm]

theorem certified_windows_of_refuted (h : AllRefuted) {m : Nat} (p : Snake m) :
    ∀ r : Nat, ∀ hr : r + 4 ≤ m,
      ¬Certified (localAlpha p ⟨r + 1, by omega⟩) (localAlpha p ⟨r + 2, by omega⟩)
        (localAlpha p ⟨r + 3, by omega⟩) := by
  intro r hr hc
  rw [localAlpha_eq_coreAlpha, localAlpha_eq_coreAlpha, localAlpha_eq_coreAlpha] at hc
  exact no_certified_window_core h p r hr hc

theorem quad_windows_of_refuted (h : AllRefuted) {m : Nat} (p : Snake m) :
    ∀ r : Nat, ∀ hr : r + 5 ≤ m,
      ¬QuadExcluded (localAlpha p ⟨r + 1, by omega⟩) (localAlpha p ⟨r + 2, by omega⟩)
        (localAlpha p ⟨r + 3, by omega⟩) (localAlpha p ⟨r + 4, by omega⟩) := by
  intro r hr hc
  rw [localAlpha_eq_coreAlpha, localAlpha_eq_coreAlpha, localAlpha_eq_coreAlpha,
    localAlpha_eq_coreAlpha] at hc
  exact no_quad_window_core h p r hr hc

/-- A snake in Q9 has at most 242 edges, given the 22 local window certificates. -/
theorem upper_242_of_refuted (h : AllRefuted) {m : Nat} (p : Snake m) : m ≤ 242 :=
  upper_242_of_certified_windows p (certified_windows_of_refuted h p)

/-- A snake in Q9 has at most 241 edges, given the 22 local window certificates. -/
theorem upper_241_of_refuted (h : AllRefuted) {m : Nat} (p : Snake m) : m ≤ 241 :=
  upper_241_of_certified_windows p (certified_windows_of_refuted h p) (quad_windows_of_refuted h p)

#print axioms localAlpha_eq_coreAlpha
#print axioms upper_242_of_refuted
#print axioms upper_241_of_refuted
end
end Snake9
