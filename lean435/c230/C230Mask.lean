module

@[expose] public section

/-!
# Bit masks of key boxes (milestone 37, the K7 cover)

Chain-independent part of the cover lemma of the K7 route. A table row of the K7 chain is a big
number whose set bits are excluded (shape, symbols) entries. The cover check of a row is one kernel
evaluation of `rowCheck`: every set bit of the row is a bit of the mask of the key boxes.

* `symOK s b`: the symbol `s` (`symK 8` of a count, so `1 .. 7` exactly or `8` for `8 .. 21`) lies in
  the count interval `b`, i.e. every count with symbol `s` lies in `b`. `boxOK t b` for symbol lists.
* `boxPts b`: all symbol lists of the box `b` (each entry `1 .. 8`); `keyPts qp K`: their positions.
* `ptsMask lb d lo ps`: the bit set of the positions `ps - lo`, built by halving the position range
  (`d` levels, leaf blocks of `2 ^ lb` bits): kernel cost about (size of the row) x `d`.
* `rowCheck_spec`: a set bit of a checked row is the position of a symbol list of some key box.
-/

namespace Snake9.C230

/-! ## Symbol boxes -/

/-- Symbol `s` lies in the count interval `b` (symbols `1 .. 7` are exact counts, `8` is `8 .. 21`). -/
def symOK (s : Nat) (b : Nat × Nat) : Bool :=
  (decide (1 ≤ s) && decide (s ≤ 7) && decide (b.1 ≤ s) && decide (s ≤ b.2)) ||
  (decide (s = 8) && decide (b.1 ≤ 8) && decide (21 ≤ b.2))

/-- Every symbol of `t` lies in the interval at its position (and the lengths agree). -/
def boxOK : List Nat → List (Nat × Nat) → Bool
  | [], [] => true
  | s :: t, b :: bs => symOK s b && boxOK t bs
  | _, _ => false

theorem symOK_range {s : Nat} {b : Nat × Nat} (h : symOK s b = true) : 1 ≤ s ∧ s ≤ 8 := by
  unfold symOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem boxOK_length : ∀ (t : List Nat) (bs : List (Nat × Nat)), boxOK t bs = true → t.length = bs.length
  | [], [], _ => rfl
  | _ :: t, _ :: bs, h => by
    simp only [boxOK, Bool.and_eq_true] at h
    simp [boxOK_length t bs h.2]
  | [], _ :: _, h => by simp [boxOK] at h
  | _ :: _, [], h => by simp [boxOK] at h

theorem boxOK_range : ∀ (t : List Nat) (bs : List (Nat × Nat)), boxOK t bs = true →
    ∀ x ∈ t, 1 ≤ x ∧ x ≤ 8
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | _ :: t, _ :: bs, h, x, hx => by
    simp only [boxOK, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact symOK_range h.1
    · exact boxOK_range t bs h.2 x hx
  | _ :: _, [], h, _, _ => by simp [boxOK] at h

theorem boxOK_getD : ∀ (t : List Nat) (bs : List (Nat × Nat)), boxOK t bs = true →
    ∀ i, i < t.length → symOK (t.getD i 0) (bs.getD i (0, 21)) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: t, _ :: bs, h, i, hi => by
    simp only [boxOK, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simp only [List.getD_cons_succ]
      exact boxOK_getD t bs h.2 i (by simp at hi; omega)
  | _ :: _, [], h, _, _ => by simp [boxOK] at h

/-- The symbols of an interval. -/
def allowed (b : Nat × Nat) : List Nat := (List.range 9).filter (fun s => symOK s b)

/-- All symbol lists of a box. -/
def boxPts : List (Nat × Nat) → List (List Nat)
  | [] => [[]]
  | b :: bs => (allowed b).flatMap (fun s => (boxPts bs).map (s :: ·))

theorem boxOK_of_mem : ∀ (bs : List (Nat × Nat)) (t : List Nat), t ∈ boxPts bs → boxOK t bs = true
  | [], t, h => by
    simp only [boxPts, List.mem_singleton] at h
    subst h; rfl
  | b :: bs, t, h => by
    simp only [boxPts, List.mem_flatMap, List.mem_map] at h
    obtain ⟨s, hs, u, hu, rfl⟩ := h
    simp only [allowed, List.mem_filter] at hs
    simp only [boxOK, Bool.and_eq_true]
    exact ⟨hs.2, boxOK_of_mem bs u hu⟩

/-- Positions (under `qp`) of all symbol lists of all boxes of `K`. -/
def keyPts (qp : List Nat → Nat) (K : List (List (Nat × Nat))) : List Nat :=
  K.flatMap (fun b => (boxPts b).map qp)

theorem mem_keyPts {qp : List Nat → Nat} {K : List (List (Nat × Nat))} {x : Nat} (h : x ∈ keyPts qp K) :
    ∃ b ∈ K, ∃ t, boxOK t b = true ∧ qp t = x := by
  simp only [keyPts, List.mem_flatMap, List.mem_map] at h
  obtain ⟨b, hb, t, ht, rfl⟩ := h
  exact ⟨b, hb, t, boxOK_of_mem b t ht, rfl⟩

/-! ## Masks of position lists -/

/-- Leaf block: the bits `q - lo` of the positions `q`. -/
def leafMask (lo : Nat) (ps : List Nat) : Nat := ps.foldl (fun acc q => acc ||| (1 <<< (q - lo))) 0

/-- The bits `q - lo` of the positions, by halving the range `[lo, lo + 2 ^ (lb + d))`. -/
def ptsMask (lb : Nat) : Nat → Nat → List Nat → Nat
  | 0, lo, ps => leafMask lo ps
  | d + 1, lo, ps =>
    ptsMask lb d lo (ps.filter (fun q => decide (q < lo + 2 ^ (lb + d)))) |||
      (ptsMask lb d (lo + 2 ^ (lb + d)) (ps.filter (fun q => decide (lo + 2 ^ (lb + d) ≤ q))) <<< (2 ^ (lb + d)))

theorem testBit_foldl (lo : Nat) : ∀ (ps : List Nat) (acc j : Nat),
    (ps.foldl (fun acc q => acc ||| (1 <<< (q - lo))) acc).testBit j = true →
      acc.testBit j = true ∨ ∃ q ∈ ps, q - lo = j
  | [], acc, j, h => Or.inl h
  | q :: ps, acc, j, h => by
    rcases testBit_foldl lo ps _ j h with h | ⟨q', hq', e⟩
    · rw [Nat.testBit_or] at h
      rcases Bool.or_eq_true_iff.1 h with h | h
      · exact Or.inl h
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h
        exact Or.inr ⟨q, List.mem_cons_self, of_decide_eq_true h⟩
    · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', e⟩

theorem testBit_leafMask {lo : Nat} {ps : List Nat} (hlo : ∀ q ∈ ps, lo ≤ q) {j : Nat}
    (h : (leafMask lo ps).testBit j = true) : lo + j ∈ ps := by
  rcases testBit_foldl lo ps 0 j h with h | ⟨q, hq, e⟩
  · simp at h
  · have := hlo q hq
    rw [show lo + j = q by omega]
    exact hq

theorem testBit_ptsMask (lb : Nat) : ∀ (d lo : Nat) (ps : List Nat), (∀ q ∈ ps, lo ≤ q) → ∀ j,
    (ptsMask lb d lo ps).testBit j = true → lo + j ∈ ps
  | 0, lo, ps, hlo, j, h => testBit_leafMask hlo h
  | d + 1, lo, ps, hlo, j, h => by
    simp only [ptsMask] at h
    rw [Nat.testBit_or] at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · have := testBit_ptsMask lb d lo _ (fun q hq => hlo q (List.mem_filter.1 hq).1) j h
      exact (List.mem_filter.1 this).1
    · rw [Nat.testBit_shiftLeft] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have := testBit_ptsMask lb d (lo + 2 ^ (lb + d)) _
        (fun q hq => by simpa using (List.mem_filter.1 hq).2) _ h.2
      have e : lo + 2 ^ (lb + d) + (j - 2 ^ (lb + d)) = lo + j := by omega
      rw [e] at this
      exact (List.mem_filter.1 this).1

/-! ## The row check -/

/-- Every key of `K` has `n` intervals, and every set bit of the row `R` is a bit of the mask of the
key boxes (positions `qp`, mask with `d` halving levels). -/
def rowCheck (qp : List Nat → Nat) (n d : Nat) (R : Nat) (K : List (List (Nat × Nat))) : Bool :=
  K.all (fun b => b.length == n) &&
    ((R ||| ptsMask 13 d 0 (keyPts qp K)) == ptsMask 13 d 0 (keyPts qp K))

theorem rowCheck_spec {qp : List Nat → Nat} {n d R : Nat} {K : List (List (Nat × Nat))}
    (h : rowCheck qp n d R K = true) {q : Nat} (hq : R.testBit q = true) :
    ∃ b ∈ K, b.length = n ∧ ∃ t, boxOK t b = true ∧ qp t = q := by
  simp only [rowCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, heq⟩ := h
  have hm : (ptsMask 13 d 0 (keyPts qp K)).testBit q = true := by
    rw [← heq, Nat.testBit_or, hq, Bool.true_or]
  have := testBit_ptsMask 13 d 0 _ (fun _ _ => Nat.zero_le _) q hm
  rw [Nat.zero_add] at this
  obtain ⟨b, hb, t, ht, e⟩ := mem_keyPts this
  exact ⟨b, hb, hlen b hb, t, ht, e⟩

end Snake9.C230
