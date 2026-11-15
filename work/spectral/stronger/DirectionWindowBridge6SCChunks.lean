/-
Chunked covers for the 6SC chain (milestone 35, `milestones/35-231-lean/README.md`).

Core Lean only.  The kernel cost of `shareRowOK T ks c t0` and `ctxRowOK bits row ks c t0` is the
number of nonzero fields times the length of `ks` (`keyLevel` scans the whole list).  With the 231
plan (2,004 share keys, up to 193 key fields per row) one row declaration against the whole key
list ran out of memory.  This module lets each row `(c, t0)` be checked against its own chunk of
the keys:

* `keyLevel_ge_of_mem`, `keyLevel_mono`: `keyLevel` is monotone under inclusion of key lists;
* `shareRowOK_mono`, `shareCover_chunks`: `ShareCover T chunks.flatten` from one zero check and,
  per listed shape and first count, a chunk index;
* `ctxCover_chunks`: the same for `CtxCover` (whose statement already allows a sublist per row),
  with a chunk per shape and first count instead of `ctxCover_rows`'s chunk per shape.
-/
import DirectionWindowBridge6SC

namespace Snake9.DirectionWindow6SC
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow6 Snake9.DirectionWindow6S

theorem keyLevel_ge_of_mem (c t : List Nat) :
    ∀ (ks : List (List Nat × List Nat × Nat)) (k : List Nat × List Nat × Nat), k ∈ ks →
      k.1 = c → k.2.1 = t → k.2.2 + 1 ≤ keyLevel c t ks
  | [], k, hk, _, _ => absurd hk List.not_mem_nil
  | k' :: ks, k, hk, h1, h2 => by
    show k.2.2 + 1 ≤ cond (k'.1 == c && k'.2.1 == t) (max (k'.2.2 + 1) (keyLevel c t ks)) (keyLevel c t ks)
    rcases List.mem_cons.1 hk with rfl | hk
    · have e : (k.1 == c && k.2.1 == t) = true := by simp [h1, h2]
      rw [e]
      exact Nat.le_max_left _ _
    · have ih := keyLevel_ge_of_mem c t ks k hk h1 h2
      cases (k'.1 == c && k'.2.1 == t)
      · exact ih
      · exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem keyLevel_mono (c t : List Nat) (ks : List (List Nat × List Nat × Nat)) :
    ∀ (ks' : List (List Nat × List Nat × Nat)), (∀ k ∈ ks', k ∈ ks) → keyLevel c t ks' ≤ keyLevel c t ks
  | [], _ => Nat.zero_le _
  | k :: ks', h => by
    have ih := keyLevel_mono c t ks ks' (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    show cond (k.1 == c && k.2.1 == t) (max (k.2.2 + 1) (keyLevel c t ks')) (keyLevel c t ks') ≤
      keyLevel c t ks
    cases hk : (k.1 == c && k.2.1 == t)
    · exact ih
    · simp only [Bool.and_eq_true, beq_iff_eq] at hk
      exact Nat.max_le.2 ⟨keyLevel_ge_of_mem c t ks k (h k List.mem_cons_self) hk.1 hk.2, ih⟩

theorem shareRowOK_mono {T : Tables6S} {ks ks' : List (List Nat × List Nat × Nat)}
    (hsub : ∀ k ∈ ks', k ∈ ks) {c : List Nat} {t0 : Nat} (h : shareRowOK T ks' c t0 = true) :
    shareRowOK T ks c t0 = true := by
  unfold shareRowOK at h ⊢
  refine allSym_of_forall _ (fun t1 h1 h1' => allSym_of_forall _ (fun t2 h2 h2' =>
    allSym_of_forall _ (fun t3 h3 h3' => allSym_of_forall _ (fun t4 h4 h4' => ?_))))
  have := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ h t1 h1 h1') t2 h2 h2') t3 h3 h3')
    t4 h4 h4'
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this ⊢
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr (Nat.le_trans h (keyLevel_mono _ _ ks ks' hsub))

/-- `ShareCover` from one kernel evaluation (rows outside `shapes` are zero) and, per listed shape
and first count, one declaration against one chunk of the keys. -/
theorem shareCover_chunks {T : Tables6S} {chunks : List (List (List Nat × List Nat × Nat))}
    (shapes : List (List Nat)) (hz : allRGS 6 0 (zeroOutsideS T shapes) = true)
    (hr : ∀ c ∈ shapes, ∀ t0, 1 ≤ t0 → t0 ≤ 6 → ∃ i, shareRowOK T (chunks.getD i []) c t0 = true) :
    ShareCover T chunks.flatten := by
  intro c hc hl t0 h1 h6
  have h := allRGS_spec 6 0 _ hz c hl hc
  unfold zeroOutsideS at h
  rcases Bool.or_eq_true_iff.1 h with h0 | hm
  · exact shareRowOK_of_zero T _ c t0 (by simpa using allSym_spec _ h0 t0 h1 h6)
  · obtain ⟨i, hi⟩ := hr c (of_decide_eq_true hm) t0 h1 h6
    exact shareRowOK_mono (fun k hk => mem_flatten_getD' hk) hi

/-- `CtxCover` from one kernel evaluation and, per listed shape and first count, one declaration
against one chunk of the keys. -/
theorem ctxCover_chunks {n bits : Nat} {rowf : List Nat → Nat → Nat} {chunks : List (List CtxKey)}
    (shapes : List (List Nat)) (hz : allRGS n 0 (zeroOutsideC rowf shapes) = true)
    (hr : ∀ c ∈ shapes, ∀ t0, 1 ≤ t0 → t0 ≤ 6 → ∃ i, ctxRowOK bits (rowf c) (chunks.getD i []) c t0 = true) :
    CtxCover n bits rowf chunks.flatten := by
  intro c hc hl t0 h1 h6
  have h := allRGS_spec n 0 _ hz c hl hc
  unfold zeroOutsideC at h
  rcases Bool.or_eq_true_iff.1 h with h0 | hm
  · exact ⟨[], fun _ hk => absurd hk List.not_mem_nil,
      ctxRowOK_of_zero bits _ [] c t0 (by simpa using allSym_spec _ h0 t0 h1 h6)⟩
  · obtain ⟨i, hi⟩ := hr c (of_decide_eq_true hm) t0 h1 h6
    exact ⟨chunks.getD i [], fun _ hk => mem_flatten_getD' hk, hi⟩

end Snake9.DirectionWindow6SC

#print axioms Snake9.DirectionWindow6SC.keyLevel_mono
#print axioms Snake9.DirectionWindow6SC.shareCover_chunks
#print axioms Snake9.DirectionWindow6SC.ctxCover_chunks
