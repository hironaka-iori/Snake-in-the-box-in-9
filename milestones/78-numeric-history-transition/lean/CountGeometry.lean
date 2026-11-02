import AggregateSingletonBound
import LocalWindowDirBridge
namespace Snake9.CountGeometry78
open SquareIncidence Finset Classical LocalWindow
noncomputable section
set_option maxHeartbeats 1000000
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


theorem core_count_positive {m : Nat} (p : Snake m) (k : Nat) (hk : k < m+1) :
    1 ≤ coreAlpha p k := by
  rw [← localAlpha_eq_coreAlpha p k hk]
  exact localAlpha_positive p _

def truncatedCount {m : Nat} (p : Snake m) (k : Nat) : Nat :=
  min 6 (coreAlpha p k)

theorem truncatedCount_range {m : Nat} (p : Snake m) (k : Nat) (hk : k < m+1) :
    1 ≤ truncatedCount p k ∧ truncatedCount p k ≤ 6 := by
  have h := core_count_positive p k hk
  unfold truncatedCount
  omega

#print axioms inPath_iff_sel
#print axioms flip_val
#print axioms localAlpha_eq_coreAlpha
#print axioms core_count_positive
#print axioms truncatedCount_range
end
end Snake9.CountGeometry78
