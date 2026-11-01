import ShareCharge
import LocalWindowShareBridge

/-!
The coordinate and square-count identifications below are extracted from the
contributor's ShareBridge.lean and AggregateWindowUnconditional.lean. Exact source
commit and hashes are in ../data/provenance.json. The independent namespace avoids
collisions with the contributor's full aggregate module.
-/
namespace Snake9.CountFreeBridge
open SquareIncidence Finset Classical LocalWindow
noncomputable section
set_option maxHeartbeats 1600000
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

/-! ## Sums over `Fin n`, `Finset.range n` and `List.range n` -/

theorem sum_range_eq_list_sum (f : Nat → Nat) (n : Nat) :
    (∑ k ∈ Finset.range n, f k) = ((List.range n).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

theorem sum_fin_eq_list_sum (f : Nat → Nat) (n : Nat) :
    (∑ k : Fin n, f k.val) = ((List.range n).map f).sum := by
  rw [← Finset.sum_range, sum_range_eq_list_sum]

/-- `Σ_x sel(x)·f(x) = Σ_i f(p.vertex i)` (as `selected_total`, `totalSingleton_eq_path_sum`). -/
theorem sum_selected_mul {m : Nat} (p : Snake m) (f : Vertex → Nat) :
    (∑ x, selected p x * f x) = ∑ i : Fin (m + 1), f (p.vertex i) := by
  let s : Finset Vertex := Finset.univ.image p.vertex
  have hs : ∀ v, selected p v * f v = if v ∈ s then f v else 0 := by
    intro v
    have hv : InPath p v ↔ v ∈ s := by simp [s, InPath]
    unfold selected
    rw [hv]
    split <;> simp
  simp only [hs]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image]
  intro i _ j _ h
  exact p.distinct i j h

/-! ## Empty squares and selected neighbours -/

/-- `emptyAt` is the core `emptyCount` in the identity frame. -/
theorem emptyAt_eq_emptyCount {m : Nat} (p : Snake m) (q : Vertex) :
    emptyAt p q = emptyCount (sel p (fun w => w)) q.val := by
  have hterm : ∀ ab : AxisPair, empty p ab q =
      if emptyPred (sel p (fun w => w)) q.val (ab.val.1.val, ab.val.2.val) = true
      then 1 else 0 := by
    intro ab
    unfold empty
    simp only [inPath_iff_sel, flip_val]
    cases h0 : sel p (fun w => w) q.val <;>
    cases h1 : sel p (fun w => w) (q.val ^^^ 2 ^ ab.val.1.val) <;>
    cases h2 : sel p (fun w => w) (q.val ^^^ 2 ^ ab.val.2.val) <;>
    cases h3 : sel p (fun w => w) (q.val ^^^ 2 ^ ab.val.1.val ^^^ 2 ^ ab.val.2.val) <;>
    simp [emptyPred_iff, h0, h1, h2, h3]
  unfold emptyAt emptyCount
  rw [Finset.sum_congr rfl (fun ab _ => hterm ab), Finset.sum_boole, Nat.cast_id,
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

/-- `selDeg` is the core selected-neighbour count `cnt S (nbrs ·)`. -/
theorem selDeg_eq_cnt {m : Nat} (p : Snake m) (q : Vertex) :
    selDeg p q = cnt (sel p (fun w => w)) (nbrs q.val) := by
  rw [cnt_nbrs_eq]
  unfold selDeg selected
  simp only [inPath_iff_sel, flip_val]
  rw [Finset.sum_boole, Nat.cast_id, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨k.isLt, hk.2⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    rw [List.mem_toFinset, List.mem_filter, List.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩, rfl⟩

/-! ## The share identification -/

/-- The global share `shareN` of the snake's `k`-th vertex is the core `coreShare`. -/
theorem shareN_eq_coreShare {m : Nat} (M : Nat) (p : Snake m) (k : Nat) (hk : k < m + 1) :
    shareN M p (p.vertex ⟨k, hk⟩) = coreShare M p k := by
  have hc : vx p k = (p.vertex ⟨k, hk⟩).val := by simp [vx, hk]
  rw [coreShare_eq_sum, hc]
  unfold shareN
  simp only [emptyAt_eq_emptyCount, selDeg_eq_cnt, flip_val]
  exact sum_fin_eq_list_sum (fun j => M * emptyCount (sel p fun w => w)
    ((p.vertex ⟨k, hk⟩).val ^^^ 2 ^ j) / cnt (sel p fun w => w)
    (nbrs ((p.vertex ⟨k, hk⟩).val ^^^ 2 ^ j))) 9


theorem core_share_path_sum {m : Nat} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * shareN M p x) =
      ((List.range (m+1)).map fun k => coreShare M p k).sum := by
  rw [sum_selected_mul]
  calc
    (∑ i : Fin (m+1), shareN M p (p.vertex i)) =
        ∑ i : Fin (m+1), coreShare M p i.val := by
      apply Finset.sum_congr rfl
      intro i _
      exact shareN_eq_coreShare M p i.val i.isLt
    _ = _ := sum_fin_eq_list_sum (coreShare M p) (m+1)

/-- The global empty-square budget in exactly the core representation used by
the local share certificates. The anchored count counts each empty square four times. -/
theorem core_share_total_le {m : Nat} (M : Nat) (p : Snake m) :
    ((List.range (m+1)).map fun k => coreShare M p k).sum ≤
      M * totalEmptyAnchored p := by
  rw [← core_share_path_sum]
  exact share_total_le M p

theorem core_share_charge_le {m : Nat} (M : Nat) (p : Snake m) (hm : 1 ≤ m) :
    2*M*totalSingleton p + ((List.range (m+1)).map fun k => coreShare M p k).sum
      + 70*M*(m+1) ≤ 18428*M := by
  have hs := core_share_total_le M p
  have hi := Nat.mul_le_mul_left M (incidence_bound_with_empty p hm)
  calc
    _ ≤ 2*M*totalSingleton p + M*totalEmptyAnchored p + 70*M*(m+1) :=
      Nat.add_le_add_right (Nat.add_le_add_left hs _) _
    _ = M*(totalEmptyAnchored p + 2*totalSingleton p + 70*(m+1)) := by ring
    _ ≤ 18428*M := by simpa [Nat.mul_comm] using hi

theorem core_share12_charge_le {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    24*totalSingleton p + ((List.range (m+1)).map fun k => coreShare 12 p k).sum
      + 840*(m+1) ≤ 221136 := by
  simpa using core_share_charge_le 12 p hm

#print axioms emptyAt_eq_emptyCount
#print axioms selDeg_eq_cnt
#print axioms shareN_eq_coreShare
#print axioms core_share_path_sum
#print axioms core_share_total_le
#print axioms core_share_charge_le
#print axioms core_share12_charge_le
end
end Snake9.CountFreeBridge
