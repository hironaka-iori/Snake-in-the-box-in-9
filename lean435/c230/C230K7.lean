module

public import C230Mask
public import C230Cover
public import WindowAutomatonK7R34C7W16Data
public import DirectionWindowBridge

@[expose] public section

/-!
# The window premises of the K7 chain from interval certificates (milestone 37)

The chain `K7R34C7W16` (milestone 10 of the relaxed-keller line, ported to 4.35) takes the premises
`hw2 .. hw7`: no window of a snake is excluded by `wforbK7R34C7W16`. Here they are proved from a table
`T` of keys `(shape, [bounds, ...])` whose certificates `Refuted (winOf shape) bounds` are given
(`AllTab T`), and from per-shape kernel checks (`GoodT T s`, generated):

* `wforbK7R34C7W16 s syms` tests bit `qpos syms` of the forward row `sfwd c (wsh s)` or of the reverse
  row `srev c (wsh s.reverse)` (`wforb_eq`). A checked row (`C230Mask.rowCheck`) has every set bit at
  the position of a symbol list of a key box: of a key of shape `s` (forward), or of a key of shape
  `canon s.reverse` read backwards (`qposR`).
* `window_refute`: a snake window whose canonical shape and lumped counts lie in a key box contradicts
  the key's certificate (`C230Cover.refuted_dir_iv`, relabelling by first occurrence as in
  `DirectionWindow.window_refute`); the reverse case is the same statement for `revSnake`.
* `no_forb`: no window of 3 .. 8 directions is excluded, given the shapes of every canonical induced
  window of that length (`ShapesCover`) and `GoodT` on each of them.
-/

namespace Snake9.C230
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

/-! ## Positions in a table row -/

/-- The bit of a symbol list in a K7 table row (forward reading). -/
def qpos (t : List Nat) : Nat := 16 * posK7R34C7W16 (codeK7R34C7W16 t 0) + 15

/-- The bit of a reversed symbol list (rows of reversed shapes). -/
def qposR (t : List Nat) : Nat := qpos t.reverse

def Digits (t : List Nat) : Prop := ∀ x ∈ t, 1 ≤ x ∧ x ≤ 8

theorem code_acc : ∀ (l : List Nat) (acc : Nat),
    codeK7R34C7W16 l acc = acc * 8 ^ l.length + codeK7R34C7W16 l 0
  | [], acc => by simp [codeK7R34C7W16]
  | s :: l, acc => by
    simp only [codeK7R34C7W16]
    rw [code_acc l (acc * 8 + (s - 1)), code_acc l (0 * 8 + (s - 1))]
    simp only [List.length_cons, Nat.pow_succ, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc,
      Nat.add_assoc]
    rw [Nat.mul_comm 8 (8 ^ l.length)]

theorem code_lt : ∀ (l : List Nat), Digits l → codeK7R34C7W16 l 0 < 8 ^ l.length
  | [], _ => by simp [codeK7R34C7W16]
  | s :: l, h => by
    have hs := h s List.mem_cons_self
    have ih := code_lt l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [codeK7R34C7W16]
    rw [code_acc]
    simp only [Nat.zero_mul, Nat.zero_add, List.length_cons, Nat.pow_succ]
    have : (s - 1) * 8 ^ l.length + codeK7R34C7W16 l 0 < (s - 1) * 8 ^ l.length + 8 ^ l.length := by omega
    have h7 : (s - 1) * 8 ^ l.length + 8 ^ l.length ≤ 8 ^ l.length * 8 := by
      rw [show (s - 1) * 8 ^ l.length + 8 ^ l.length = (s - 1 + 1) * 8 ^ l.length by rw [Nat.add_mul, Nat.one_mul],
        Nat.mul_comm (8 ^ l.length)]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem code_inj : ∀ (l l' : List Nat), l.length = l'.length → Digits l → Digits l' →
    codeK7R34C7W16 l 0 = codeK7R34C7W16 l' 0 → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | a :: l, b :: l', hl, hd, hd', he => by
    have ha := hd a List.mem_cons_self
    have hb := hd' b List.mem_cons_self
    have hdl : Digits l := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    have hdl' : Digits l' := fun x hx => hd' x (List.mem_cons_of_mem _ hx)
    have hl1 : l.length = l'.length := by simpa using hl
    simp only [codeK7R34C7W16] at he
    rw [code_acc l, code_acc l', ← hl1] at he
    simp only [Nat.zero_mul, Nat.zero_add] at he
    have h1 := code_lt l hdl
    have h2 := code_lt l' hdl'
    rw [← hl1] at h2
    have hP : 0 < 8 ^ l.length := Nat.pos_pow_of_pos _ (by decide)
    have e1 : ((a - 1) * 8 ^ l.length + codeK7R34C7W16 l 0) / 8 ^ l.length = a - 1 := by
      rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt h1, Nat.add_zero]
    have e2 : ((b - 1) * 8 ^ l.length + codeK7R34C7W16 l' 0) / 8 ^ l.length = b - 1 := by
      rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt h2, Nat.add_zero]
    have hab : a = b := by rw [he] at e1; omega
    subst hab
    have hrest : codeK7R34C7W16 l 0 = codeK7R34C7W16 l' 0 := by omega
    rw [code_inj l l' hl1 hdl hdl' hrest]

theorem pos_inj {z z' : Nat} (h : posK7R34C7W16 z = posK7R34C7W16 z') : z = z' := by
  unfold posK7R34C7W16 at h
  omega

theorem qpos_inj {t u : List Nat} (hl : t.length = u.length) (ht : Digits t) (hu : Digits u)
    (h : qpos t = qpos u) : t = u := by
  unfold qpos at h
  exact code_inj t u hl ht hu (pos_inj (by omega))

theorem digits_of_boxOK {t : List Nat} {b : List (Nat × Nat)} (h : boxOK t b = true) : Digits t :=
  boxOK_range t b h

/-! ## Rows -/

/-- A checked forward row: a set bit at a symbol list of `n` symbols lies in a key box. -/
theorem fwd_hit {n d R : Nat} {K : List (List (Nat × Nat))} (h : rowCheck qpos n d R K = true)
    {syms : List Nat} (hl : syms.length = n) (hd : Digits syms) (hb : R.testBit (qpos syms) = true) :
    ∃ b ∈ K, boxOK syms b = true := by
  obtain ⟨b, hbK, hbl, t, ht, e⟩ := rowCheck_spec h hb
  have htl : t.length = n := (boxOK_length t b ht).trans hbl
  have := qpos_inj (htl.trans hl.symm) (digits_of_boxOK ht) hd e
  subst this
  exact ⟨b, hbK, ht⟩

/-- A checked reverse row: a set bit at a symbol list lies in a key box, read backwards. -/
theorem rev_hit {n d R : Nat} {K : List (List (Nat × Nat))} (h : rowCheck qposR n d R K = true)
    {syms : List Nat} (hl : syms.length = n) (hd : Digits syms) (hb : R.testBit (qpos syms) = true) :
    ∃ b ∈ K, boxOK syms.reverse b = true := by
  obtain ⟨b, hbK, hbl, t, ht, e⟩ := rowCheck_spec h hb
  have htl : t.length = n := (boxOK_length t b ht).trans hbl
  have hdr : Digits t.reverse := fun x hx => digits_of_boxOK ht x (List.mem_reverse.1 hx)
  have := qpos_inj (by simp [htl, hl]) hdr hd e
  rw [← this, List.reverse_reverse]
  exact ⟨b, hbK, ht⟩

/-! ## The per-shape statement -/

/-- An excluded entry of shape `s` lies in a key box of shape `s`, or (read backwards) in a key box of
shape `canon s.reverse`. -/
def GoodT (T : List Entry) (s : List Nat) : Prop :=
  ∀ syms : List Nat, syms.length + 1 = s.length → Digits syms → wforbK7R34C7W16 s syms = true →
    ∃ e ∈ T, ∃ b ∈ e.2, (e.1 = s ∧ boxOK syms b = true) ∨ (e.1 = canon s.reverse ∧ boxOK syms.reverse b = true)

theorem wforb_eq (ds syms : List Nat) : wforbK7R34C7W16 ds syms =
    ((sfwdK7R34C7W16 syms.length (wshK7R34C7W16 ds)) ||| (srevK7R34C7W16 syms.length (wshK7R34C7W16 ds.reverse))).testBit
      (qpos syms) := rfl

/-- The forward part of `GoodT`, from a row check against table entry `i`. -/
def FwdOK (T : List Entry) (s : List Nat) (n : Nat) : Prop :=
  ∀ syms : List Nat, syms.length = n → Digits syms → (sfwdK7R34C7W16 n (wshK7R34C7W16 s)).testBit (qpos syms) = true →
    ∃ e ∈ T, ∃ b ∈ e.2, e.1 = s ∧ boxOK syms b = true

def RevOK (T : List Entry) (s : List Nat) (n : Nat) : Prop :=
  ∀ syms : List Nat, syms.length = n → Digits syms → (srevK7R34C7W16 n (wshK7R34C7W16 s.reverse)).testBit (qpos syms) = true →
    ∃ e ∈ T, ∃ b ∈ e.2, e.1 = canon s.reverse ∧ boxOK syms.reverse b = true

theorem goodT_of {T : List Entry} {s : List Nat} {n : Nat} (hn : n + 1 = s.length)
    (hf : FwdOK T s n) (hr : RevOK T s n) : GoodT T s := by
  intro syms hl hd hw
  have hl' : syms.length = n := by omega
  rw [wforb_eq, Nat.testBit_or, hl'] at hw
  rcases Bool.or_eq_true_iff.1 hw with h | h
  · obtain ⟨e, he, b, hb, h1, h2⟩ := hf syms hl' hd h
    exact ⟨e, he, b, hb, Or.inl ⟨h1, h2⟩⟩
  · obtain ⟨e, he, b, hb, h1, h2⟩ := hr syms hl' hd h
    exact ⟨e, he, b, hb, Or.inr ⟨h1, h2⟩⟩

theorem getD_mem {T : List Entry} {i : Nat} (hi : i < T.length) : T.getD i ([], []) ∈ T := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- Forward row checked against the keys of entry `i` of shape `s`. -/
theorem fwdOK_of {T : List Entry} {s : List Nat} {n d i : Nat} (hi : i < T.length)
    (hs : (T.getD i ([], [])).1 = s)
    (h : rowCheck qpos n d (sfwdK7R34C7W16 n (wshK7R34C7W16 s)) (T.getD i ([], [])).2 = true) : FwdOK T s n := by
  intro syms hl hd hb
  obtain ⟨b, hbK, hbox⟩ := fwd_hit h hl hd hb
  exact ⟨_, getD_mem hi, b, hbK, hs, hbox⟩

/-- The forward row of a shape without keys is empty. -/
theorem fwdOK_zero {T : List Entry} {s : List Nat} {n : Nat}
    (h : sfwdK7R34C7W16 n (wshK7R34C7W16 s) = 0) : FwdOK T s n := by
  intro syms _ _ hb
  rw [h, Nat.zero_testBit] at hb
  exact absurd hb (by decide)

theorem revOK_of {T : List Entry} {s : List Nat} {n d i : Nat} (hi : i < T.length)
    (hs : (T.getD i ([], [])).1 = canon s.reverse)
    (h : rowCheck qposR n d (srevK7R34C7W16 n (wshK7R34C7W16 s.reverse)) (T.getD i ([], [])).2 = true) :
    RevOK T s n := by
  intro syms hl hd hb
  obtain ⟨b, hbK, hbox⟩ := rev_hit h hl hd hb
  exact ⟨_, getD_mem hi, b, hbK, hs, hbox⟩

theorem revOK_zero {T : List Entry} {s : List Nat} {n : Nat}
    (h : srevK7R34C7W16 n (wshK7R34C7W16 s.reverse) = 0) : RevOK T s n := by
  intro syms _ _ hb
  rw [h, Nat.zero_testBit] at hb
  exact absurd hb (by decide)

/-- Two-centre rows also hold copies of their entries (for the 512-field blocks of the chain's
check); they are checked under the mask `V` of the bits `qpos [a, b]` that `wforb` reads. -/
theorem fwdOK_of_mask {T : List Entry} {s : List Nat} {d i V : Nat} (hi : i < T.length)
    (hs : (T.getD i ([], [])).1 = s)
    (hV : ∀ a b, a < 8 → b < 8 → V.testBit (qpos [a + 1, b + 1]) = true)
    (h : rowCheck qpos 2 d (sfwdK7R34C7W16 2 (wshK7R34C7W16 s) &&& V) (T.getD i ([], [])).2 = true) :
    FwdOK T s 2 := by
  intro syms hl hd hb
  match syms, hl, hd with
  | [x, y], _, hd =>
    have hx := hd x (by simp)
    have hy := hd y (by simp)
    have hv := hV (x - 1) (y - 1) (by omega) (by omega)
    rw [show x - 1 + 1 = x by omega, show y - 1 + 1 = y by omega] at hv
    have hb' : (sfwdK7R34C7W16 2 (wshK7R34C7W16 s) &&& V).testBit (qpos [x, y]) = true := by
      rw [Nat.testBit_and, hb, hv]; rfl
    obtain ⟨b, hbK, hbox⟩ := fwd_hit h rfl hd hb'
    exact ⟨_, getD_mem hi, b, hbK, hs, hbox⟩

theorem revOK_of_mask {T : List Entry} {s : List Nat} {d i V : Nat} (hi : i < T.length)
    (hs : (T.getD i ([], [])).1 = canon s.reverse)
    (hV : ∀ a b, a < 8 → b < 8 → V.testBit (qpos [a + 1, b + 1]) = true)
    (h : rowCheck qposR 2 d (srevK7R34C7W16 2 (wshK7R34C7W16 s.reverse) &&& V) (T.getD i ([], [])).2 = true) :
    RevOK T s 2 := by
  intro syms hl hd hb
  match syms, hl, hd with
  | [x, y], _, hd =>
    have hx := hd x (by simp)
    have hy := hd y (by simp)
    have hv := hV (x - 1) (y - 1) (by omega) (by omega)
    rw [show x - 1 + 1 = x by omega, show y - 1 + 1 = y by omega] at hv
    have hb' : (srevK7R34C7W16 2 (wshK7R34C7W16 s.reverse) &&& V).testBit (qpos [x, y]) = true := by
      rw [Nat.testBit_and, hb, hv]; rfl
    obtain ⟨b, hbK, hbox⟩ := rev_hit h rfl hd hb'
    exact ⟨_, getD_mem hi, b, hbK, hs, hbox⟩

/-- Every shape of a list satisfies `GoodT` (one conjunct per shape). -/
def AllGood (T : List Entry) : List (List Nat) → Prop
  | [] => True
  | s :: l => GoodT T s ∧ AllGood T l

theorem AllGood.get {T : List Entry} : ∀ {L : List (List Nat)}, AllGood T L → ∀ s ∈ L, GoodT T s
  | [], _, _, hs => absurd hs List.not_mem_nil
  | _ :: _, ⟨h, hL⟩, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h
    · exact AllGood.get hL s hs

/-! ## Canonical shapes -/

theorem canon_canon (ds : List Nat) : canon (canon ds) = canon ds := by
  have := canon_canon_take ds ds.length
  rwa [List.take_of_length_le (by rw [length_canon]), List.take_of_length_le (Nat.le_refl _)] at this

theorem canon_canon_reverse' (ds : List Nat) : canon (canon ds).reverse = canon ds.reverse := by
  have := canon_canon_drop_reverse ds 0
  simpa using this

theorem wforb_canon (ds syms : List Nat) : wforbK7R34C7W16 (canon ds) syms = wforbK7R34C7W16 ds syms := by
  unfold wforbK7R34C7W16 wshK7R34C7W16
  rw [canon_canon, canon_canon_reverse']

/-- A shape list covers the canonical windows of `n` directions: every restricted growth string of
length `n` that passes the xor-mask induced test is listed (kernel-checked per length). -/
def ShapesCover (sh : List (List Nat)) (n : Nat) : Prop :=
  sh.all (fun s => s.length == n && s.all (· < 8)) = true ∧
  ∀ c, c.length = n → isRGS c 0 = true → (!inducedFast c || (sh.map shapeCode).any (Nat.beq (shapeCode c))) = true

/-- `ShareBonus.window_shape_mem_of` of the relaxed-keller line (not ported: it sits in a module of
the parallel share), for `blockList`. -/
theorem window_shape_mem {sh : List (List Nat)} {n : Nat} (hn : n ≤ 8) (hc : ShapesCover sh n)
    {m : Nat} (p : Snake m) (j : Nat) (hj : j + n ≤ m) : canon (blockList p j n) ∈ sh := by
  obtain ⟨hok, hcov⟩ := hc
  have hlen : (canon (blockList p j n)).length = n := by
    rw [length_canon]; simp [blockList]
  have hr := canon_isRGS (blockList p j n)
  have hm := hcov _ hlen hr
  have hind : inducedPattern (canon (blockList p j n)) = true := by
    rw [inducedPattern_canon]; exact snake_inducedPattern_block p j n hj
  have hb : ∀ a, a ∈ canon (blockList p j n) → a < 8 := fun a ha => by
    have := isRGS_bound _ 0 hr a ha; rw [hlen] at this; omega
  have hfast := inducedFast_of_inducedPattern _ (fun d hd => by have := hb d hd; omega) hind
  rw [hfast] at hm
  simp only [Bool.not_true, Bool.false_or] at hm
  obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hm
  obtain ⟨s, hs, hsx⟩ := List.mem_map.mp hx
  have hcode : shapeCode s = shapeCode (canon (blockList p j n)) := by
    rw [hsx]; exact (Nat.eq_of_beq_eq_true hxe).symm
  have hsh : s.length = n ∧ ∀ a, a ∈ s → a < 8 := by
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    exact hok s hs
  unfold shapeCode at hcode
  rw [codeFrom_inj _ s 1 (by rw [hlen, hsh.1]) hb hsh.2 hcode.symm]
  exact hs

/-! ## Windows of a snake -/

section Window
variable {m : Nat} (p : Snake m)

/-- Lumped counts (cap 8) of the `n - 1` centres of the window of `n` directions at `r`. -/
def symsK (r n : Nat) : List Nat := (List.range (n - 1)).map (fun i => symK 8 (coreAlpha p (r + i + 1)))

theorem length_symsK (r n : Nat) : (symsK p r n).length = n - 1 := by simp [symsK]

theorem getD_symsK {r n i : Nat} (hi : i < n - 1) :
    (symsK p r n).getD i 0 = symK 8 (coreAlpha p (r + i + 1)) := by
  simp [symsK, List.getD_eq_getElem?_getD, hi]

theorem symsK_rev (r n : Nat) (hr : r + n ≤ m) :
    symsK (revSnake p) (m - r - n) n = (symsK p r n).reverse := by
  apply List.ext_getElem
  · simp [symsK]
  · intro i h1 h2
    simp only [symsK, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    simp only [symsK, List.length_map, List.length_range] at h1
    rw [coreAlpha_rev p (by omega)]
    congr 2
    omega

theorem digits_symsK {r n : Nat} (hr : r + n ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j) : Digits (symsK p r n) := by
  intro x hx
  simp only [symsK, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have := hpos (r + i + 1) (by omega) (by omega)
  unfold symK
  omega

/-- A window whose canonical shape carries a key box containing its lumped counts contradicts the
key's certificate. -/
theorem window_refute {r n : Nat} (hn : 3 ≤ n) (hr : r + n ≤ m) {b : List (Nat × Nat)}
    (href : Refuted (winOf (canon (dsOf p r n))) b) (hbox : boxOK (symsK p r n) b = true) : False := by
  have hlen := length_dsOf p r n
  have hblen : b.length + 1 = n := by
    have := boxOK_length _ _ hbox
    rw [length_symsK] at this
    omega
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ seenAfter [] (dsOf p r n) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine refuted_dir_iv href p r (u := seenAfter [] (dsOf p r n)) (by rw [length_canon]; omega)
    (by rw [length_canon]; omega) (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro j hj
    rw [length_canon] at hj
    have e : (canon (dsOf p r n)).getD j 0 = idx (seenAfter [] (dsOf p r n)) ((dsOf p r n).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    have hs := boxOK_getD _ _ hbox i (by rw [length_symsK]; omega)
    rw [getD_symsK p (by omega)] at hs
    have hpos : 1 ≤ coreAlpha p (r + i + 1) := by
      by_contra h0
      have h0' : coreAlpha p (r + i + 1) = 0 := by omega
      rw [h0'] at hs
      simp [symOK, symK] at hs
    have h21 := coreAlpha_le_21 p (k := r + i + 1) (by omega) (by omega)
    unfold symOK symK at hs
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
    omega

/-- No window of `n` directions is excluded, given the table, the shape cover and `GoodT`. -/
theorem no_forb {T : List Entry} (hT : AllTab T) {sh : List (List Nat)} {n : Nat} (hn : 3 ≤ n ∧ n ≤ 8)
    (hc : ShapesCover sh n) (hg : AllGood T sh)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j) (r : Nat) (hr : r + n ≤ m) :
    wforbK7R34C7W16 (dsOf p r n) (symsK p r n) = false := by
  cases hw : wforbK7R34C7W16 (dsOf p r n) (symsK p r n)
  · rfl
  exfalso
  have hbl : blockList p r n = dsOf p r n := by
    apply List.ext_getElem
    · simp [blockList, dsOf]
    · intro j h1 h2
      simp only [blockList, dsOf, List.getElem_map, List.getElem_range', List.getElem_range, Nat.one_mul]
      simp only [blockList, List.length_map, List.length_range'] at h1
      exact pathDir_eq_dir p (by omega)
  have hsh : canon (dsOf p r n) ∈ sh := by
    rw [← hbl]; exact window_shape_mem hn.2 hc p r hr
  have hgood := hg.get _ hsh
  rw [← wforb_canon] at hw
  obtain ⟨e, he, b, hb, hcase⟩ := hgood (symsK p r n) (by rw [length_symsK, length_canon, length_dsOf]; omega)
    (digits_symsK p hr hpos) hw
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have href := hT e he b hb
    rw [h1] at href
    exact window_refute p hn.1 hr href h2
  · have href := hT e he b hb
    rw [h1, canon_canon_reverse', ← dsOf_rev p r n hr] at href
    rw [← symsK_rev p r n hr] at h2
    exact window_refute (revSnake p) hn.1 (by omega) href h2

end Window

end Snake9.C230
