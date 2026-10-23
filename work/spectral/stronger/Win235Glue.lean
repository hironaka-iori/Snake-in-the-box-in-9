import Win235Norm
import WindowAutomatonK6R3WData
import AggregateSingletonBound
/-!
# From refuted shapes to the window premises of `upper_235_of_direction_windowsK6R3W`

The premise for windows of `n` centres (`n + 1` edge directions `ds`, lumped counts `syms`) is
`wforbK6R3W ds syms = false`.  The table depends on `ds` only through `canon ds` and
`canon ds.reverse` (`wforbK6R3W_canon`).

* `rgsOK n listed`: every restricted growth string of length `n + 1` (every possible `canon ds`)
  is listed or has empty forward and reverse tables;
* `allSyms n (tabP E c)` (per listed shape `c`): every symbol tuple `1..6` flagged for `c` is
  covered (`covL`, the lumped symbol `6` by a range `[≤ 6, ≥ 21]`) by a range tuple of the
  refuted shape `canon c` read forwards, or of `canon c.reverse` read backwards;
* `no_win`: with `∀ e ∈ E, ShapeRefuted e.c e.L` the flagged window cannot occur: the snake (or
  the reversed snake) is moved by a cube automorphism onto the canonical window
  (`norm_canon`, `revS`), keeping all counts.
-/
namespace S235
open Snake9 Snake9.WindowAutomaton

/-! ### Ranges and symbols -/

def cov1 (r : Nat × Nat) (s : Nat) : Bool :=
  if s = 6 then decide (r.1 ≤ 6) && decide (21 ≤ r.2) else decide (r.1 ≤ s) && decide (s ≤ r.2)

theorem cov1_sym {lo hi a : Nat} (h : cov1 (lo, hi) (sym a) = true) : InR lo hi a := by
  unfold cov1 at h; unfold InR
  by_cases ha : a ≤ 5
  · have hs : sym a = a := by unfold sym; split <;> omega
    rw [hs] at h
    simp only [show a ≠ 6 by omega, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · have hs : sym a = 6 := by unfold sym; split <;> omega
    rw [hs] at h
    simp only [if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    omega

def covL : List (Nat × Nat) → List Nat → Bool
  | [], ss => ss.isEmpty
  | r :: rs, ss => match ss with
    | [] => false
    | s :: ss => cov1 r s && covL rs ss

theorem covL_spec : ∀ (rs : List (Nat × Nat)) (ss : List Nat), covL rs ss = true →
    rs.length = ss.length ∧ ∀ i < rs.length, cov1 (rs.getD i (0, 0)) (ss.getD i 0) = true
  | [], [], _ => ⟨rfl, fun i h => absurd h (by simp)⟩
  | [], _ :: _, h => by simp [covL] at h
  | _ :: _, [], h => by simp [covL] at h
  | r :: rs, s :: ss, h => by
    simp only [covL, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := covL_spec rs ss h.2
    refine ⟨by simp [h1], fun i hi => ?_⟩
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using h2 i (by simp at hi; omega)

structure Entry where
  c : List Nat
  L : List (List (Nat × Nat))

def covS (E : List Entry) (c syms : List Nat) : Bool :=
  E.any fun e => e.c == c && e.L.any fun rs => covL rs syms

def allSyms : Nat → (List Nat → Bool) → Bool
  | 0, p => p []
  | n + 1, p => allBelow 6 fun a => allSyms n fun l => p ((a + 1) :: l)

theorem allSyms_spec : ∀ (n : Nat) (p : List Nat → Bool), allSyms n p = true →
    ∀ l : List Nat, l.length = n → (∀ s ∈ l, 1 ≤ s ∧ s ≤ 6) → p l = true
  | 0, p, h, [], _, _ => h
  | 0, _, _, _ :: _, hl, _ => by simp at hl
  | _ + 1, _, _, [], hl, _ => by simp at hl
  | n + 1, p, h, s :: l, hl, hs => by
    have h1 := hs s List.mem_cons_self
    have h2 := allBelow_spec 6 _ h (s - 1) (by omega)
    have h3 := allSyms_spec n _ h2 l (by simpa using hl) (fun t ht => hs t (List.mem_cons_of_mem _ ht))
    simpa [show s - 1 + 1 = s by omega] using h3

def tabP (E : List Entry) (c syms : List Nat) : Bool :=
  !wforbK6R3W c syms || covS E (canon c) syms || covS E (canon c.reverse) syms.reverse

/-- Every flagged symbol tuple (entries `1..6`) of `c` is covered. -/
def TabOK (E : List Entry) (n : Nat) (c : List Nat) : Prop :=
  ∀ syms : List Nat, syms.length = n → (∀ s ∈ syms, 1 ≤ s ∧ s ≤ 6) → tabP E c syms = true

/-- Every canonical direction list of length `n + 1` is listed, or neither it nor its reversal
is a window shape of the table (index `34` = no shape, empty tables `sfwd_big`, `srev_big`). -/
def rgsOK (n : Nat) (listed : List (List Nat)) : Bool :=
  allRGS (n + 1) 0 fun c => (decide (34 ≤ wshK6R3W c) && decide (34 ≤ wshK6R3W c.reverse)) ||
    listed.contains c

theorem sfwd_big (n w : Nat) (h : 34 ≤ w) : sfwdK6R3W n w = 0 := by
  unfold sfwdK6R3W
  simp only [show w ≠ 0 by omega, show w ≠ 1 by omega, show w ≠ 2 by omega, show w ≠ 3 by omega, show w ≠ 4 by omega, show w ≠ 5 by omega, show w ≠ 6 by omega, show w ≠ 7 by omega, show w ≠ 8 by omega, show w ≠ 9 by omega, show w ≠ 10 by omega, show w ≠ 11 by omega, show w ≠ 12 by omega, show w ≠ 13 by omega, show w ≠ 14 by omega, show w ≠ 15 by omega, show w ≠ 16 by omega, show w ≠ 17 by omega, show w ≠ 18 by omega, show w ≠ 19 by omega, show w ≠ 20 by omega, show w ≠ 21 by omega, show w ≠ 22 by omega, show w ≠ 23 by omega, show w ≠ 24 by omega, show w ≠ 25 by omega, show w ≠ 26 by omega, show w ≠ 27 by omega, show w ≠ 28 by omega, show w ≠ 29 by omega, show w ≠ 30 by omega, show w ≠ 31 by omega, show w ≠ 32 by omega, show w ≠ 33 by omega, if_false, ite_self]

theorem srev_big (n w : Nat) (h : 34 ≤ w) : srevK6R3W n w = 0 := by
  unfold srevK6R3W
  simp only [show w ≠ 0 by omega, show w ≠ 1 by omega, show w ≠ 2 by omega, show w ≠ 3 by omega, show w ≠ 4 by omega, show w ≠ 5 by omega, show w ≠ 6 by omega, show w ≠ 7 by omega, show w ≠ 8 by omega, show w ≠ 9 by omega, show w ≠ 10 by omega, show w ≠ 11 by omega, show w ≠ 12 by omega, show w ≠ 13 by omega, show w ≠ 14 by omega, show w ≠ 15 by omega, show w ≠ 16 by omega, show w ≠ 17 by omega, show w ≠ 18 by omega, show w ≠ 19 by omega, show w ≠ 20 by omega, show w ≠ 21 by omega, show w ≠ 22 by omega, show w ≠ 23 by omega, show w ≠ 24 by omega, show w ≠ 25 by omega, show w ≠ 26 by omega, show w ≠ 27 by omega, show w ≠ 28 by omega, show w ≠ 29 by omega, show w ≠ 30 by omega, show w ≠ 31 by omega, show w ≠ 32 by omega, show w ≠ 33 by omega, if_false, ite_self]

theorem tabOK_cons {n : Nat} {E : List Entry} {c : List Nat} {l : List (List Nat)}
    (h : TabOK E n c) (t : ∀ x ∈ l, TabOK E n x) : ∀ x ∈ c :: l, TabOK E n x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact t x hx

theorem entry_cons {e : Entry} {l : List Entry} (h : ShapeRefuted e.c e.L)
    (t : ∀ x ∈ l, ShapeRefuted x.c x.L) : ∀ x ∈ e :: l, ShapeRefuted x.c x.L := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact t x hx

/-! ### Invariance under relabelling -/

theorem canon_idem (ds : List Nat) : canon (canon ds) = canon ds := by
  have h := canon_canon_take ds ds.length
  rwa [List.take_of_length_le (by rw [length_canon]), List.take_of_length_le (le_refl _)] at h

theorem canon_rev (ds : List Nat) : canon (canon ds).reverse = canon ds.reverse := by
  have h := canon_canon_drop_reverse ds 0
  simpa using h

theorem wforbK6R3W_canon (ds syms : List Nat) : wforbK6R3W (canon ds) syms = wforbK6R3W ds syms := by
  unfold wforbK6R3W wshK6R3W
  rw [canon_idem, canon_rev]


theorem tabOK_of_allSyms {E : List Entry} {n : Nat} {c : List Nat} (h : allSyms n (tabP E c) = true) :
    TabOK E n c := allSyms_spec n _ h

theorem cover {n : Nat} {E : List Entry} {listed : List (List Nat)} (hR : rgsOK n listed = true)
    (hS : ∀ c ∈ listed, TabOK E n c) (ds syms : List Nat) (hl : ds.length = n + 1)
    (hsl : syms.length = n) (hs : ∀ s ∈ syms, 1 ≤ s ∧ s ≤ 6) (hw : wforbK6R3W ds syms = true) :
    covS E (canon ds) syms = true ∨ covS E (canon ds.reverse) syms.reverse = true := by
  have hr := allRGS_spec (n + 1) 0 _ hR (canon ds) (by rw [length_canon, hl]) (canon_isRGS ds)
  rw [← wforbK6R3W_canon] at hw
  rcases Bool.or_eq_true _ _ ▸ hr with hz | hc
  · exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
    unfold wforbK6R3W at hw
    rw [hsl, blk, sfwd_big _ _ hz.1, srev_big _ _ hz.2, Nat.zero_or, Nat.zero_testBit] at hw
    exact Bool.false_ne_true hw
  · have ht := hS _ (List.contains_iff_mem.mp hc) syms hsl hs
    unfold tabP at ht
    rw [hw, canon_idem, canon_rev] at ht
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at ht
    exact ht

theorem covS_spec {E : List Entry} {c syms : List Nat} (h : covS E c syms = true) :
    ∃ e ∈ E, e.c = c ∧ ∃ rs ∈ e.L, covL rs syms = true := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  exact ⟨e, he, h.1, h.2⟩

/-! ### Coverage in pieces

For `n ≥ 4` centres the symbol tuples are split by a prefix `pre` (`k` symbols); the table bits of
the tuples with that prefix lie in one window of `8 · 6^(n-k)` bits (`pos3_prefix`), which is cut
out once (`pieceT`) so that the kernel tests bits of a small number. -/

theorem code_acc : ∀ (l : List Nat) (acc : Nat), codeK6R3W l acc = acc * 6 ^ l.length + codeK6R3W l 0
  | [], acc => by simp [codeK6R3W]
  | s :: l, acc => by
    simp only [codeK6R3W, List.length_cons]
    rw [code_acc l (acc * 6 + (s - 1)), code_acc l (0 * 6 + (s - 1)), Nat.pow_succ]
    ring

theorem code_append (pre l : List Nat) :
    codeK6R3W (pre ++ l) 0 = codeK6R3W pre 0 * 6 ^ l.length + codeK6R3W l 0 := by
  induction pre generalizing l with
  | nil => simp [codeK6R3W]
  | cons s pre ih =>
    simp only [List.cons_append, codeK6R3W, Nat.zero_mul, Nat.zero_add]
    rw [code_acc (pre ++ l), code_acc pre (s - 1), List.length_append, Nat.pow_add, ih]
    ring

theorem code_lt : ∀ (l : List Nat), (∀ s ∈ l, 1 ≤ s ∧ s ≤ 6) → codeK6R3W l 0 < 6 ^ l.length
  | [], _ => by simp [codeK6R3W]
  | s :: l, h => by
    have h1 := h s List.mem_cons_self
    have h2 := code_lt l (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [codeK6R3W, Nat.zero_mul, Nat.zero_add, List.length_cons]
    rw [code_acc, Nat.pow_succ]
    have : (s - 1) * 6 ^ l.length + codeK6R3W l 0 < ((s - 1) + 1) * 6 ^ l.length := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    calc (s - 1) * 6 ^ l.length + codeK6R3W l 0 < ((s - 1) + 1) * 6 ^ l.length := this
      _ ≤ 6 * 6 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ = 6 ^ l.length * 6 := Nat.mul_comm _ _

theorem pos3_prefix (P t r : Nat) (hr : r < 216 * t) : pos3 (P * (216 * t) + r) = P * (216 * t) + pos3 r := by
  unfold pos3
  have e : P * (216 * t) = 216 * (P * t) := by rw [Nat.mul_left_comm]
  rw [e]
  generalize P * t = Q
  omega

theorem pos3_lt (r B : Nat) (hB : B % 216 = 0) (hr : r < B) : pos3 r < B := by
  unfold pos3; omega

def pieceT (E : List Entry) (n : Nat) (c pre : List Nat) : Nat :=
  (blk (sfwdK6R3W n (wshK6R3W c)) (srevK6R3W n (wshK6R3W c.reverse)) >>>
    (8 * (codeK6R3W pre 0 * 6 ^ (n - pre.length)))) &&& (2 ^ (8 * 6 ^ (n - pre.length)) - 1)

def pieceOK (E : List Entry) (n : Nat) (c pre : List Nat) : Bool :=
  let T := pieceT E n c pre
  allSyms (n - pre.length) fun l => !T.testBit (8 * pos3 (codeK6R3W l 0) + 7) ||
    covS E (canon c) (pre ++ l) || covS E (canon c.reverse) (pre ++ l).reverse

theorem pieceOK_sound {E : List Entry} {n : Nat} {c pre : List Nat} (h : pieceOK E n c pre = true)
    (hk : pre.length + 3 ≤ n) (hpre : ∀ s ∈ pre, 1 ≤ s ∧ s ≤ 6) (l : List Nat)
    (hl : l.length = n - pre.length) (hs : ∀ s ∈ l, 1 ≤ s ∧ s ≤ 6) : tabP E c (pre ++ l) = true := by
  have h1 := allSyms_spec _ _ h l hl hs
  simp only at h1
  unfold tabP
  have hB : 6 ^ (n - pre.length) % 216 = 0 := by
    obtain ⟨t, ht⟩ : ∃ t, n - pre.length = t + 3 := ⟨n - pre.length - 3, by omega⟩
    rw [ht, Nat.pow_add]; simp [Nat.mul_mod_left]
  obtain ⟨t, htB⟩ : ∃ t, 6 ^ (n - pre.length) = 216 * t := ⟨6 ^ (n - pre.length) / 216, by omega⟩
  have hcl := code_lt l hs
  rw [hl] at hcl
  have hw : wforbK6R3W c (pre ++ l) = (pieceT E n c pre).testBit (8 * pos3 (codeK6R3W l 0) + 7) := by
    unfold wforbK6R3W pieceT
    rw [List.length_append, hl, show pre.length + (n - pre.length) = n by omega,
      testBit_win _ _ _ _ (by have := pos3_lt _ _ hB hcl; omega), code_append, hl, htB,
      pos3_prefix _ _ _ (by rw [← htB]; exact hcl)]
    congr 1; rw [← htB]; ring
  rw [hw]; exact h1

def prefixes : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range 6).flatMap fun a => (prefixes k).map fun l => (a + 1) :: l

theorem mem_prefixes : ∀ (k : Nat) (l : List Nat), l.length = k → (∀ s ∈ l, 1 ≤ s ∧ s ≤ 6) → l ∈ prefixes k
  | 0, [], _, _ => by simp [prefixes]
  | 0, _ :: _, hl, _ => by simp at hl
  | _ + 1, [], hl, _ => by simp at hl
  | k + 1, s :: l, hl, hs => by
    have h1 := hs s List.mem_cons_self
    have h2 := mem_prefixes k l (by simpa using hl) (fun t ht => hs t (List.mem_cons_of_mem _ ht))
    simp only [prefixes, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨s - 1, by omega, l, h2, by rw [show s - 1 + 1 = s by omega]⟩

theorem tabOK_of_pieces {E : List Entry} {n k : Nat} {c : List Nat} (hk : k + 3 ≤ n)
    (h : ∀ pre ∈ prefixes k, pieceOK E n c pre = true) : TabOK E n c := by
  intro syms hl hs
  have e := List.take_append_drop k syms
  rw [← e]
  have hlt : (syms.take k).length = k := by simp; omega
  have hpre : ∀ s ∈ syms.take k, 1 ≤ s ∧ s ≤ 6 := fun s hm => hs s (List.mem_of_mem_take hm)
  exact pieceOK_sound (h _ (mem_prefixes k _ hlt hpre)) (by omega) hpre _
    (by simp [hlt]; omega) (fun s hm => hs s (List.mem_of_mem_drop hm))

theorem pieces_cons {E : List Entry} {n : Nat} {c pre : List Nat} {l : List (List Nat)}
    (h : pieceOK E n c pre = true) (t : ∀ x ∈ l, pieceOK E n c x = true) :
    ∀ x ∈ pre :: l, pieceOK E n c x = true := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact t x hx

/-! ### No flagged window -/

noncomputable def symsAt {m : Nat} (p : Snake m) (j n : Nat) : List Nat :=
  (List.range n).map fun i => sym (countSeq p (j + 1 + i))

theorem symsAt_length {m : Nat} (p : Snake m) (j n : Nat) : (symsAt p j n).length = n := by
  simp [symsAt]

theorem symsAt_getD {m : Nat} (p : Snake m) (j n i : Nat) (hi : i < n) :
    (symsAt p j n).getD i 0 = sym (countSeq p (j + 1 + i)) := by
  simp [symsAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem getD_reverse (l : List Nat) (i : Nat) (hi : i < l.length) :
    l.reverse.getD i 0 = l.getD (l.length - 1 - i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some, List.getElem_reverse]

theorem countSeq_pos {m : Nat} (p : Snake m) (k : Nat) (hk : k ≤ m) : 1 ≤ countSeq p k := by
  rw [countSeq_eq p k (by omega)]; exact Snake9.SquareIncidence.localAlpha_positive p _

theorem no_win {n : Nat} {E : List Entry} {listed : List (List Nat)}
    (hE : ∀ e ∈ E, ShapeRefuted e.c e.L) (hR : rgsOK n listed = true)
    (hS : ∀ c ∈ listed, TabOK E n c) {m : Nat} (p : Snake m) (j : Nat)
    (hj : j + n + 1 ≤ m) : wforbK6R3W (dl p j (n + 1)) (symsAt p j n) = false := by
  cases hw : wforbK6R3W (dl p j (n + 1)) (symsAt p j n) with
  | false => rfl
  | true =>
  exfalso
  have hs : ∀ s ∈ symsAt p j n, 1 ≤ s ∧ s ≤ 6 := by
    intro s hsm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hsm
    have hi' := List.mem_range.mp hi
    refine ⟨?_, sym_le_six _⟩
    have := countSeq_pos p (j + 1 + i) (by omega)
    unfold sym; split <;> omega
  rcases cover hR hS _ _ (dl_length p j _) (symsAt_length p j n) hs hw with hc | hc
  · obtain ⟨e, he, hec, rs, hrs, hcov⟩ := covS_spec hc
    obtain ⟨hlen, hcv⟩ := covL_spec rs _ hcov
    rw [symsAt_length] at hlen
    obtain ⟨q, hv, hcs⟩ := norm_canon p j (n + 1) (by omega)
    refine hE e he rs hrs q j (by rw [hec, length_canon, dl_length]; omega) (by rw [hec, length_canon, dl_length]; exact hv) ?_
    intro i hi
    have h1 := hcv i hi
    rw [symsAt_getD p j n i (by omega)] at h1
    rw [hcs, show j + i + 1 = j + 1 + i by omega]
    exact cov1_sym h1
  · obtain ⟨e, he, hec, rs, hrs, hcov⟩ := covS_spec hc
    obtain ⟨hlen, hcv⟩ := covL_spec rs _ hcov
    rw [List.length_reverse, symsAt_length] at hlen
    have hd := dl_revS p j (n + 1) (by omega)
    obtain ⟨q, hv, hcs⟩ := norm_canon (revS p) (m - (j + (n + 1))) (n + 1) (by omega)
    rw [hd] at hv
    refine hE e he rs hrs q (m - (j + (n + 1))) (by rw [hec, length_canon, List.length_reverse, dl_length]; omega)
      (by rw [hec, length_canon, List.length_reverse, dl_length]; exact hv) ?_
    intro i hi
    have h1 := hcv i hi
    rw [getD_reverse _ i (by rw [symsAt_length]; omega), symsAt_length,
      symsAt_getD p j n _ (by omega)] at h1
    rw [hcs, countSeq_revS p _ (by omega), show m - (m - (j + (n + 1)) + i + 1) = j + 1 + (n - 1 - i) by omega]
    exact cov1_sym h1

end S235
