import EmptyShareBound
import ParallelShareBridge

/-! Exact identification of the executable parallel share with the global
finite-sum quantity used by the weighted incidence bound. -/
namespace Snake9.ParallelShareIdentification
open SquareIncidence LocalWindow Finset Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem inPath_iff_core {m : Nat} (p : Snake m) (v : Vertex) :
    InPath p v ↔ sel p (fun w => w) v.val = true := by
  rw [sel_iff]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i.val, by omega, ?_⟩
    simp [vx, i.isLt]
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨i, by omega⟩, Fin.ext ?_⟩
    simpa [vx, show i < m + 1 by omega] using h

theorem flip_val (a : Coord) (v : Vertex) : (flip a v).val = v.val ^^^ 2 ^ a.val := rfl

theorem selected_eq_bit {m : Nat} (p : Snake m) (v : Vertex) :
    selected p v = selectedBit (sel p (fun w => w) v.val) := by
  unfold selected selectedBit
  rw [inPath_iff_core]
  cases h : sel p (fun w => w) v.val <;> simp [h]

theorem count_eq {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    sqCount p ab v = parallelCount (sel p (fun w => w)) v.val (ab.val.1.val, ab.val.2.val) := by
  simp only [sqCount, parallelCount, selected_eq_bit, flip_val]

theorem empty_eq {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    empty p ab v = if emptyPred (sel p (fun w => w)) v.val (ab.val.1.val, ab.val.2.val)
      then 1 else 0 := by
  unfold empty
  simp only [inPath_iff_core, flip_val]
  cases h0 : sel p (fun w => w) v.val <;>
  cases h1 : sel p (fun w => w) (v.val ^^^ 2 ^ ab.val.1.val) <;>
  cases h2 : sel p (fun w => w) (v.val ^^^ 2 ^ ab.val.2.val) <;>
  cases h3 : sel p (fun w => w) (v.val ^^^ 2 ^ ab.val.1.val ^^^ 2 ^ ab.val.2.val) <;>
  simp [emptyPred_iff, h0, h1, h2, h3]

theorem term_eq {m : Nat} (p : Snake m) (k : Coord) (ab : AxisPair) (v : Vertex) :
    shareTerm p k ab v =
      parallelTerm (sel p (fun w => w)) v.val k.val (ab.val.1.val, ab.val.2.val) := by
  have hk : offAxis k ab ↔ k.val ≠ ab.val.1.val ∧ k.val ≠ ab.val.2.val := by
    simp [offAxis, Fin.ext_iff]
  by_cases ho : offAxis k ab
  · obtain ⟨h1, h2⟩ := hk.mp ho
    by_cases he : emptyPred (sel p (fun w => w)) (v.val ^^^ 2 ^ k.val)
        (ab.val.1.val, ab.val.2.val) = true
    all_goals simp [shareTerm, parallelTerm, empty_eq, count_eq, flip_val,
      shareWeight, parallelWeight, ho, h1, h2, he]
  · have hn : ¬ (k.val ≠ ab.val.1.val ∧ k.val ≠ ab.val.2.val) := fun h => ho (hk.mpr h)
    simp only [shareTerm, ho, if_false, parallelTerm, Prod.fst, Prod.snd]
    split <;> simp_all

theorem sum_axes (f : Nat × Nat → Nat) :
    (∑ ab : AxisPair, f (ab.val.1.val, ab.val.2.val)) = ((freePairs 9 9).map f).sum := by
  rw [← List.sum_toFinset f (freePairs_nodup 9 (by omega) 9 (by omega))]
  apply Finset.sum_bij (fun ab _ => (ab.val.1.val, ab.val.2.val))
  · intro ab _
    rw [List.mem_toFinset, mem_freePairs]
    exact ⟨ab.2, ab.val.2.isLt, by omega, by omega, by omega, by omega⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  · intro ab hab
    obtain ⟨a, b⟩ := ab
    rw [List.mem_toFinset, mem_freePairs] at hab
    exact ⟨⟨(⟨a, by omega⟩, ⟨b, hab.2.1⟩), hab.1⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

theorem sum_coords (f : Nat → Nat) :
    (∑ k : Coord, f k.val) = ((List.range 9).map f).sum := by
  rw [← Finset.sum_range]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
    Multiset.map_coe, Multiset.sum_coe]

/-- The two independently defined parallel-share quantities are exactly equal,
at every vertex of every snake, including endpoints. -/
theorem vertexShare_eq {m : Nat} (p : Snake m) (v : Vertex) :
    vertexShare p v = parallelShare (sel p (fun w => w)) v.val := by
  unfold vertexShare parallelShare
  simp only [term_eq]
  simp_rw [sum_axes]
  exact sum_coords (fun k => ((freePairs 9 9).map
    (fun ab => parallelTerm (sel p (fun w => w)) v.val k ab)).sum)

theorem share_eq_core {m : Nat} (p : Snake m) (k : Fin (m + 1)) :
    share p k = coreParallelShare p k.val := by
  unfold share coreParallelShare
  rw [vertexShare_eq]
  simp [vx, k.isLt]

#print axioms vertexShare_eq
#print axioms share_eq_core
end
end Snake9.ParallelShareIdentification
