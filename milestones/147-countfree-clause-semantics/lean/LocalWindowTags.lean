import LocalWindowModel

/-!
# Every local window clause follows from the snake axioms

The clauses of a local window CNF (`milestones/10-window-aggregate/scripts/wincert.py`)
are necessary conditions on a snake.  This module makes that precise for the UNSAT
cores of `LocalWindowCnf`: from `S`, `E` satisfying `Axioms` it builds an assignment
`tau S E M cs` and shows that it satisfies every clause accepted by the Bool checker
`checkAll`.  A certificate module (`LocalWindowSat/<M>.lean`) only supplies data and
runs `checkAll` once in the kernel.

The data of a certificate:

* `M : MT` assigns each variable a meaning, stored as a binary tree indexed by the
  bits of the variable number: `.p v` (primary variable of ball vertex `v`, value
  `S v`), `.e v` (endpoint flag of `v`, value `E v`), `.r c i j` (register `s[i][j]`
  of the sequential counter `c`: at least `j+1` of the first `i+1` literals of the
  counter hold).
* `cs : List Ctr` lists the sequential counters (`atmost(lits, k)`) with the reason
  why at most `k` of their literals hold: the endpoint budget (`end_two`), or an
  upper / lower bound on the absent corners of a centre (`alpha`).
* one `Tag` per clause naming its family.

Literals are the compact codes of `decodeLit`: `2*x` is `x`, `2*x+1` is `-x`.
-/

namespace Snake9.LocalWindow.Tags

open Snake9.LocalWindow

/-! ## Data -/

/-- Variable meanings, and binary trees of them (`n l r`: even indices left). -/
inductive MT where
  | z
  | p (v : Nat)
  | e (v : Nat)
  | r (c i j : Nat)
  | n (lt rt : MT)

def MT.get : MT → Nat → MT
  | .n lt rt, x => if x % 2 = 0 then lt.get (x / 2) else rt.get (x / 2)
  | .z, _ => .z
  | .p v, _ => .p v
  | .e v, _ => .e v
  | .r c i j, _ => .r c i j

/-- Why a counter is bounded: endpoint budget, or the bounds of centre `ci`. -/
inductive Kind where
  | ends
  | hi (ci : Nat)
  | lo (ci : Nat)

/-- A sequential counter: at most `k` of `lits` hold. -/
structure Ctr where
  lits : List Nat
  k : Nat
  kind : Kind

def dfltCtr : Ctr := ⟨[], 2, .ends⟩
def dfltCentre : Centre := ⟨0, 0, 0, 0, 0⟩

/-- Clause families. -/
inductive Tag where
  /-- `[x]` with `x` a window vertex. -/
  | window
  /-- `[-v, -a, -b, -c]`, `a, b, c` neighbours of `v`. -/
  | deg2
  /-- `-v :: nbrs v`. -/
  | degPos
  /-- `[-e_v, v]`. -/
  | endSel
  /-- `-v :: e_v :: (nbrs v).eraseIdx t`. -/
  | lowEnd (t : Nat)
  /-- `[-e_v, -a, -b]`, `a, b` neighbours of `v`. -/
  | endLow
  /-- negation of a vertex set in which every vertex has two neighbours. -/
  | cut
  /-- `[-l_i, s[i][0]]`. -/
  | first (c i : Nat)
  /-- `[-s[0][j]]`, `j ≥ 1`. -/
  | zero (c j : Nat)
  /-- `[-s[i][j], s[i+1][j]]`. -/
  | mono (c i j : Nat)
  /-- `[-l_{i+1}, -s[i][j], s[i+1][j+1]]`. -/
  | step (c i j : Nat)
  /-- `[-l_{i+1}, -s[i][k-1]]`. -/
  | over (c i : Nat)

/-! ## The assignment -/

/-- Value of a literal code. -/
def lv (τ : Nat → Bool) (a : Nat) : Bool := if a % 2 = 0 then τ (a / 2) else !τ (a / 2)

/-- Values of primary variables and endpoint flags. -/
def base (S E : Nat → Bool) (M : MT) (x : Nat) : Bool :=
  match M.get x with
  | .p v => S v
  | .e v => E v
  | _ => false

/-- Number of true literals among the first `i+1` literals of a counter. -/
def pc (S E : Nat → Bool) (M : MT) (lits : List Nat) (i : Nat) : Nat :=
  (lits.take (i + 1)).countP (lv (base S E M))

def tau (S E : Nat → Bool) (M : MT) (cs : List Ctr) (x : Nat) : Bool :=
  match M.get x with
  | .p v => S v
  | .e v => E v
  | .r c i j => decide (j + 1 ≤ pc S E M (cs.getD c dfltCtr).lits i)
  | _ => false

/-! ## Kernel-friendly centres

`Nat.log2` is defined by well-founded recursion and does not reduce in the kernel, so
the checker computes the centres with a fuel-based logarithm and `centresK_eq` shows
that they agree with `centresOf`. -/

/-- `lg f n = Nat.log2 n` whenever `n < 2 ^ f`. -/
def lg : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if 2 ≤ n then lg f (n / 2) + 1 else 0

def centresK (window : List Nat) (bounds : List (Nat × Nat)) : List Centre :=
  (List.range bounds.length).map fun i =>
    let c := window.getD (i + 1) 0
    { v := c, d₁ := lg (window.getD i 0 ^^^ c) (window.getD i 0 ^^^ c),
      d₂ := lg (c ^^^ window.getD (i + 2) 0) (c ^^^ window.getD (i + 2) 0),
      lo := (bounds.getD i (0, 21)).1, hi := (bounds.getD i (0, 21)).2 }

theorem lg_eq : ∀ (f n : Nat), n < 2 ^ f → lg f n = Nat.log2 n
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; rw [Nat.log2.eq_1]; rfl
  | f + 1, n, h => by
    rw [Nat.log2.eq_1, lg]
    have h2 : 2 ^ (f + 1) = 2 ^ f * 2 := Nat.pow_succ 2 f
    by_cases hn : 2 ≤ n
    · rw [if_pos hn, if_pos hn, lg_eq f (n / 2) (by omega)]
    · rw [if_neg hn, if_neg hn]

theorem dirOfStep_eq (u v : Nat) : dirOfStep u v = lg (u ^^^ v) (u ^^^ v) :=
  (lg_eq _ _ Nat.lt_two_pow_self).symm

theorem centresK_eq (window : List Nat) (bounds : List (Nat × Nat)) :
    centresOf window bounds = centresK window bounds := by
  simp only [centresOf, centresK, dirOfStep_eq]

/-! ## The checker -/

def vOf (M : MT) (x : Nat) : Nat :=
  match M.get x with
  | .p v => v
  | .e v => v
  | _ => 0

def isP (M : MT) (x : Nat) : Bool :=
  match M.get x with
  | .p _ => true
  | _ => false

def isE (M : MT) (x : Nat) : Bool :=
  match M.get x with
  | .e _ => true
  | _ => false

def isR (M : MT) (x c i j : Nat) : Bool :=
  match M.get x with
  | .r c' i' j' => c' == c && i' == i && j' == j
  | _ => false

/-- Vertex of a literal code. -/
def vl (M : MT) (a : Nat) : Nat := vOf M (a / 2)

def posP (M : MT) (a : Nat) : Bool := a % 2 == 0 && decide (2 ≤ a) && isP M (a / 2)
def negP (M : MT) (a : Nat) : Bool := a % 2 == 1 && decide (2 ≤ a) && isP M (a / 2)
def posE (M : MT) (a : Nat) : Bool := a % 2 == 0 && decide (2 ≤ a) && isE M (a / 2)
def negE (M : MT) (a : Nat) : Bool := a % 2 == 1 && decide (2 ≤ a) && isE M (a / 2)
def posR (M : MT) (a c i j : Nat) : Bool := a % 2 == 0 && decide (2 ≤ a) && isR M (a / 2) c i j
def negR (M : MT) (a c i j : Nat) : Bool := a % 2 == 1 && decide (2 ≤ a) && isR M (a / 2) c i j
/-- `a` is the negation of the literal `l`. -/
def negOf (a l : Nat) : Bool := a / 2 == l / 2 && a % 2 != l % 2 && decide (2 ≤ l)
/-- Literal over a primary variable or an endpoint flag. -/
def baseOK (M : MT) (l : Nat) : Bool := decide (2 ≤ l) && (isP M (l / 2) || isE M (l / 2))

/-- Greedy sublist test. -/
def subl : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then subl as bs else subl (a :: as) bs

/-- Strictly increasing (pairwise). -/
def pw : List Nat → Bool
  | [] => true
  | a :: t => t.all (fun b => decide (a < b)) && pw t

def corners (c : Centre) : List Nat :=
  (freePairs c.d₁ c.d₂).map fun ab => c.v ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2)

def ctrOK (M : MT) (cens : List Centre) (ct : Ctr) : Bool :=
  ct.lits.all (baseOK M) &&
  match ct.kind with
  | .ends => ct.k == 2 && ct.lits.all (posE M) && pw (ct.lits.map (vl M))
  | .hi ci => decide (ci < cens.length) && ct.lits.all (negP M) &&
      ct.k == (cens.getD ci dfltCentre).hi && ct.lits.map (vl M) == corners (cens.getD ci dfltCentre)
  | .lo ci => decide (ci < cens.length) && ct.lits.all (posP M) &&
      ct.k + (cens.getD ci dfltCentre).lo ==
        (freePairs (cens.getD ci dfltCentre).d₁ (cens.getD ci dfltCentre).d₂).length &&
      ct.lits.map (vl M) == corners (cens.getD ci dfltCentre)

def ckWindow (M : MT) (w : List Nat) : List Nat → Bool
  | [a] => posP M a && w.contains (vl M a)
  | _ => false

def ckDeg2 (M : MT) : List Nat → Bool
  | [a, b, c, d] => negP M a && negP M b && negP M c && negP M d &&
      subl [vl M b, vl M c, vl M d] (nbrs (vl M a))
  | _ => false

def ckDegPos (M : MT) : List Nat → Bool
  | a :: rest => negP M a && rest.all (posP M) && rest.map (vl M) == nbrs (vl M a)
  | _ => false

def ckEndSel (M : MT) : List Nat → Bool
  | [a, b] => negE M a && posP M b && vl M a == vl M b
  | _ => false

def ckLowEnd (M : MT) (t : Nat) : List Nat → Bool
  | a :: b :: rest => negP M a && posE M b && vl M a == vl M b && rest.all (posP M) &&
      rest.map (vl M) == (nbrs (vl M a)).eraseIdx t
  | _ => false

def ckEndLow (M : MT) : List Nat → Bool
  | [a, b, c] => negE M a && negP M b && negP M c && subl [vl M b, vl M c] (nbrs (vl M a))
  | _ => false

def ckCut (M : MT) (cl : List Nat) : Bool :=
  !cl.isEmpty && cl.all (negP M) &&
    (cl.map (vl M)).all fun v => decide (2 ≤ cnt (fun w => (cl.map (vl M)).contains w) (nbrs v))

def ckFirst (M : MT) (cs : List Ctr) (c i : Nat) : List Nat → Bool
  | [a, b] => decide (i < (cs.getD c dfltCtr).lits.length) &&
      negOf a ((cs.getD c dfltCtr).lits.getD i 0) && posR M b c i 0
  | _ => false

def ckZero (M : MT) (c j : Nat) : List Nat → Bool
  | [a] => decide (1 ≤ j) && negR M a c 0 j
  | _ => false

def ckMono (M : MT) (c i j : Nat) : List Nat → Bool
  | [a, b] => negR M a c i j && posR M b c (i + 1) j
  | _ => false

def ckStep (M : MT) (cs : List Ctr) (c i j : Nat) : List Nat → Bool
  | [a, b, d] => decide (i + 1 < (cs.getD c dfltCtr).lits.length) &&
      negOf a ((cs.getD c dfltCtr).lits.getD (i + 1) 0) && negR M b c i j &&
      posR M d c (i + 1) (j + 1)
  | _ => false

def ckOver (M : MT) (cs : List Ctr) (c i : Nat) : List Nat → Bool
  | [a, b] => decide (i + 1 < (cs.getD c dfltCtr).lits.length) &&
      negOf a ((cs.getD c dfltCtr).lits.getD (i + 1) 0) && decide (1 ≤ (cs.getD c dfltCtr).k) &&
      negR M b c i ((cs.getD c dfltCtr).k - 1)
  | _ => false

def ckClause (M : MT) (cs : List Ctr) (w : List Nat) : Tag → List Nat → Bool
  | .window, cl => ckWindow M w cl
  | .deg2, cl => ckDeg2 M cl
  | .degPos, cl => ckDegPos M cl
  | .endSel, cl => ckEndSel M cl
  | .lowEnd t, cl => ckLowEnd M t cl
  | .endLow, cl => ckEndLow M cl
  | .cut, cl => ckCut M cl
  | .first c i, cl => ckFirst M cs c i cl
  | .zero c j, cl => ckZero M c j cl
  | .mono c i j, cl => ckMono M c i j cl
  | .step c i j, cl => ckStep M cs c i j cl
  | .over c i, cl => ckOver M cs c i cl

def ckAll (M : MT) (cs : List Ctr) (w : List Nat) : List Tag → List (List Nat) → Bool
  | [], [] => true
  | t :: ts, cl :: cls => ckClause M cs w t cl && ckAll M cs w ts cls
  | _, _ => false

def checkAll (M : MT) (cs : List Ctr) (w : List Nat) (b : List (Nat × Nat))
    (tags : List Tag) (raw : List (List Nat)) : Bool :=
  cs.all (ctrOK M (centresK w b)) && ckAll M cs w tags raw

/-! ## Soundness -/

section Lemmas

variable {S E : Nat → Bool} {M : MT} {cs : List Ctr}

theorem decode_eq (τ : Nat → Bool) {a : Nat} (h : 2 ≤ a) : litTrue τ (decodeLit a) = lv τ a := by
  unfold litTrue decodeLit lv
  have h1 : 1 ≤ a / 2 := by omega
  by_cases h2 : a % 2 = 0
  · have : (0 : Int) < Int.ofNat (a / 2) := by simp only [Int.ofNat_eq_coe]; omega
    rw [if_pos h2, if_pos h2, if_pos this]; rfl
  · have : ¬ (0 : Int) < -Int.ofNat (a / 2) := by simp only [Int.ofNat_eq_coe]; omega
    rw [if_neg h2, if_neg h2, if_neg this, Int.neg_neg]; rfl

theorem isP_get {x : Nat} (h : isP M x = true) : M.get x = .p (vOf M x) := by
  unfold isP at h; unfold vOf; split at h <;> simp_all

theorem isE_get {x : Nat} (h : isE M x = true) : M.get x = .e (vOf M x) := by
  unfold isE at h; unfold vOf; split at h <;> simp_all

theorem isR_get {x c i j : Nat} (h : isR M x c i j = true) : M.get x = .r c i j := by
  unfold isR at h; split at h <;> simp_all

theorem lit_posP {a : Nat} (h : posP M a = true) :
    litTrue (tau S E M cs) (decodeLit a) = S (vl M a) := by
  simp only [posP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h2⟩, hp⟩ := h
  rw [decode_eq _ h2]; simp [lv, h0, tau, vl, isP_get hp]

theorem lit_negP {a : Nat} (h : negP M a = true) :
    litTrue (tau S E M cs) (decodeLit a) = !S (vl M a) := by
  simp only [negP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h2⟩, hp⟩ := h
  rw [decode_eq _ h2]; simp [lv, h0, tau, vl, isP_get hp]

theorem lit_posE {a : Nat} (h : posE M a = true) :
    litTrue (tau S E M cs) (decodeLit a) = E (vl M a) := by
  simp only [posE, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h2⟩, hp⟩ := h
  rw [decode_eq _ h2]; simp [lv, h0, tau, vl, isE_get hp]

theorem lit_negE {a : Nat} (h : negE M a = true) :
    litTrue (tau S E M cs) (decodeLit a) = !E (vl M a) := by
  simp only [negE, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h2⟩, hp⟩ := h
  rw [decode_eq _ h2]; simp [lv, h0, tau, vl, isE_get hp]

theorem lit_posR {a c i j : Nat} (h : posR M a c i j = true) :
    litTrue (tau S E M cs) (decodeLit a) = decide (j + 1 ≤ pc S E M (cs.getD c dfltCtr).lits i) := by
  simp only [posR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h2⟩, hp⟩ := h
  rw [decode_eq _ h2]; simp [lv, h0, tau, isR_get hp]

theorem lit_negR {a c i j : Nat} (h : negR M a c i j = true) :
    litTrue (tau S E M cs) (decodeLit a) = !decide (j + 1 ≤ pc S E M (cs.getD c dfltCtr).lits i) := by
  simp only [negR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h2⟩, hp⟩ := h
  rw [decode_eq _ h2]; simp [lv, h0, tau, isR_get hp]

theorem tau_lit_base {l : Nat} (h : baseOK M l = true) :
    lv (tau S E M cs) l = lv (base S E M) l := by
  simp only [baseOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hp | hp⟩ := h
  · simp [lv, tau, base, isP_get hp]
  · simp [lv, tau, base, isE_get hp]

theorem lit_negOf {a l : Nat} (h : negOf a l = true) (hl : baseOK M l = true) :
    litTrue (tau S E M cs) (decodeLit a) = !lv (base S E M) l := by
  simp only [negOf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [decode_eq _ (by omega), ← tau_lit_base (cs := cs) hl]
  have : a % 2 = 0 ∧ l % 2 = 1 ∨ a % 2 = 1 ∧ l % 2 = 0 := by omega
  rcases this with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [lv, ha, hb, h1]

theorem base_posE {l : Nat} (h : posE M l = true) : lv (base S E M) l = E (vl M l) := by
  simp only [posE, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, _⟩, hp⟩ := h
  simp [lv, h0, base, vl, isE_get hp]

theorem base_posP {l : Nat} (h : posP M l = true) : lv (base S E M) l = S (vl M l) := by
  simp only [posP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, _⟩, hp⟩ := h
  simp [lv, h0, base, vl, isP_get hp]

theorem base_negP {l : Nat} (h : negP M l = true) : lv (base S E M) l = !S (vl M l) := by
  simp only [negP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h0, _⟩, hp⟩ := h
  simp [lv, h0, base, vl, isP_get hp]

theorem clause_intro {τ : Nat → Bool} {cl : List Nat}
    (h : (∀ x ∈ cl, litTrue τ (decodeLit x) = false) → False) :
    clauseTrue τ (cl.map decodeLit) = true := by
  unfold clauseTrue
  rw [List.any_map, List.any_eq_true]
  apply Classical.byContradiction
  intro hn
  apply h
  intro x hx
  cases hb : litTrue τ (decodeLit x)
  · rfl
  · exact absurd ⟨x, hx, by simpa using hb⟩ hn

theorem subl_sublist : ∀ {l m : List Nat}, subl l m = true → l.Sublist m
  | [], _, _ => List.nil_sublist _
  | _ :: _, [], h => by simp [subl] at h
  | a :: as, b :: bs, h => by
    unfold subl at h
    by_cases hab : a = b
    · subst hab; simp only [if_true] at h; exact (subl_sublist h).cons₂ a
    · simp only [hab, if_false] at h; exact (subl_sublist h).cons b

theorem cnt_ge {l m : List Nat} (hs : subl l m = true) (ht : ∀ x ∈ l, S x = true) :
    l.length ≤ cnt S m := by
  unfold cnt
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length.2 ht]
  exact (subl_sublist hs).countP_le

theorem cnt_zero {m : List Nat} (h : ∀ x ∈ m, S x = false) : cnt S m = 0 := by
  unfold cnt
  rw [← List.countP_eq_length_filter, List.countP_eq_zero]
  intro a ha; simp [h a ha]

theorem cnt_eraseIdx : ∀ (m : List Nat) (t : Nat), (∀ x ∈ m.eraseIdx t, S x = false) → cnt S m ≤ 1
  | [], _, _ => by simp [cnt]
  | b :: bs, 0, h => by
    have := cnt_zero (S := S) (m := bs) (by simpa using h)
    unfold cnt at this ⊢
    rw [← List.countP_eq_length_filter] at this ⊢
    rw [List.countP_cons, this]; split <;> omega
  | b :: bs, t + 1, h => by
    rw [List.eraseIdx_cons_succ] at h
    have hb : S b = false := h b (by simp)
    have := cnt_eraseIdx bs t (fun x hx => h x (by simp [hx]))
    unfold cnt at this ⊢
    rw [← List.countP_eq_length_filter] at this ⊢
    rw [List.countP_cons]; simp [hb]; exact this

theorem take_succ_countP {f : Nat → Bool} {lits : List Nat} {i : Nat} (h : i < lits.length) :
    (lits.take (i + 1)).countP f = (lits.take i).countP f + if f (lits.getD i 0) then 1 else 0 := by
  rw [List.take_succ, List.countP_append, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  simp [Option.toList, List.countP_cons]

theorem pc_succ {lits : List Nat} {i : Nat} (h : i + 1 < lits.length) :
    pc S E M lits (i + 1) =
      pc S E M lits i + if lv (base S E M) (lits.getD (i + 1) 0) then 1 else 0 := by
  unfold pc; exact take_succ_countP h

theorem pc_mono (lits : List Nat) (i : Nat) : pc S E M lits i ≤ pc S E M lits (i + 1) :=
  (List.take_sublist_take_left (by omega)).countP_le

theorem pc_zero (lits : List Nat) : pc S E M lits 0 ≤ 1 := by
  unfold pc
  have := List.countP_le_length (p := lv (base S E M)) (l := lits.take (0 + 1))
  rw [List.length_take] at this; omega

theorem pc_le_total (lits : List Nat) (i : Nat) :
    pc S E M lits i ≤ lits.countP (lv (base S E M)) :=
  (List.take_sublist _ _).countP_le

theorem getD_mem {lits : List Nat} {i : Nat} (h : i < lits.length) : lits.getD i 0 ∈ lits := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem pw_pairwise : ∀ {l : List Nat}, pw l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | a :: t, h => by
    simp only [pw, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact List.pairwise_cons.2 ⟨h.1, pw_pairwise h.2⟩

theorem ends_le {l : List Nat}
    (he : ∀ a b c, E a = true → E b = true → E c = true → a = b ∨ a = c ∨ b = c)
    (hl : l.Pairwise (· < ·)) : l.countP E ≤ 2 := by
  rw [List.countP_eq_length_filter]
  have hp : (l.filter E).Pairwise (· < ·) := hl.sublist List.filter_sublist
  have hm : ∀ x ∈ l.filter E, E x = true := fun x hx => (List.mem_filter.1 hx).2
  revert hp hm
  generalize l.filter E = f
  intro hp hm
  match f, hp, hm with
  | [], _, _ => simp
  | [_], _, _ => simp
  | [_, _], _, _ => simp
  | a :: b :: c :: rest, hp, hm =>
    exfalso
    have hab : a < b := List.rel_of_pairwise_cons hp (by simp)
    have hac : a < c := List.rel_of_pairwise_cons hp (by simp)
    have hbc : b < c := List.rel_of_pairwise_cons (List.Pairwise.of_cons hp) (by simp)
    rcases he a b c (hm a (by simp)) (hm b (by simp)) (hm c (by simp)) with h | h | h <;> omega

theorem getD_centre_mem {cens : List Centre} {ci : Nat} (h : ci < cens.length) :
    cens.getD ci dfltCentre ∈ cens := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem countP_corners_abs (c : Centre) :
    (corners c).countP (fun x => !S x) = absentCorners S c.v c.d₁ c.d₂ := by
  unfold corners absentCorners
  rw [List.countP_map, List.countP_eq_length_filter]; rfl

theorem countP_corners_sel (c : Centre) :
    (corners c).countP S + absentCorners S c.v c.d₁ c.d₂ = (freePairs c.d₁ c.d₂).length := by
  rw [← countP_corners_abs]
  unfold corners
  rw [List.countP_map, List.countP_map,
    List.length_eq_countP_add_countP (fun ab => S (c.v ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2)))]
  congr 1
  apply List.countP_congr; intro x _; simp

/-- The bound of a checked counter. -/
theorem ctr_bound {w : List Nat} {cens : List Centre} {ct : Ctr}
    (hc : ctrOK M cens ct = true) (ax : Axioms S E w cens) :
    ct.lits.countP (lv (base S E M)) ≤ ct.k := by
  unfold ctrOK at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨_, hc⟩ := hc
  split at hc
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
    obtain ⟨⟨hk, hE⟩, hpw⟩ := hc
    have : ct.lits.countP (lv (base S E M)) = (ct.lits.map (vl M)).countP E := by
      rw [List.countP_map]; apply List.countP_congr; intro x hx; simp [base_posE (hE x hx)]
    rw [this, hk]
    exact ends_le ax.end_two (pw_pairwise hpw)
  · rename_i ci _
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hci, hN⟩, hk⟩, hmap⟩ := hc
    have : ct.lits.countP (lv (base S E M)) = (ct.lits.map (vl M)).countP (fun x => !S x) := by
      rw [List.countP_map]; apply List.countP_congr; intro x hx; simp [base_negP (hN x hx)]
    rw [this, hmap, countP_corners_abs, hk]
    exact (ax.alpha _ (getD_centre_mem hci)).2
  · rename_i ci _
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hci, hP⟩, hk⟩, hmap⟩ := hc
    have : ct.lits.countP (lv (base S E M)) = (ct.lits.map (vl M)).countP S := by
      rw [List.countP_map]; apply List.countP_congr; intro x hx; simp [base_posP (hP x hx)]
    rw [this, hmap]
    have h1 := countP_corners_sel (S := S) (cens.getD ci dfltCentre)
    have h2 := (ax.alpha _ (getD_centre_mem hci)).1
    omega

theorem ctrOK_getD {cens : List Centre} (h : cs.all (ctrOK M cens) = true) (c : Nat) :
    ctrOK M cens (cs.getD c dfltCtr) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hc : cs[c]? with
  | none => simp [ctrOK, dfltCtr, pw]
  | some ct => exact List.all_eq_true.1 h ct (List.mem_of_getElem? hc)

theorem ctr_lit_ok {cens : List Centre} {ct : Ctr} (h : ctrOK M cens ct = true) {i : Nat}
    (hi : i < ct.lits.length) : baseOK M (ct.lits.getD i 0) = true := by
  unfold ctrOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 _ (getD_mem hi)

end Lemmas

/-! ### Clause families -/

section Families

variable {S E : Nat → Bool} {M : MT} {cs : List Ctr} {w : List Nat} {cens : List Centre}

theorem sound_window {cl : List Nat} (h : ckWindow M w cl = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a], h =>
    simp only [ckWindow, Bool.and_eq_true, List.contains_iff_mem] at h
    apply clause_intro; intro hf
    have := hf a (by simp)
    rw [lit_posP h.1, ax.window_sel _ h.2] at this
    exact absurd this (by decide)

theorem sound_deg2 {cl : List Nat} (h : ckDeg2 M cl = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b, c, d], h =>
    simp only [ckDeg2, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, hs⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    have fc := hf c (by simp); have fd := hf d (by simp)
    rw [lit_negP ha, Bool.not_eq_false'] at fa
    rw [lit_negP hb, Bool.not_eq_false'] at fb
    rw [lit_negP hc, Bool.not_eq_false'] at fc
    rw [lit_negP hd, Bool.not_eq_false'] at fd
    have h3 := cnt_ge hs (S := S) (by simp [fb, fc, fd])
    have h2 := ax.deg_le_two _ fa
    simp at h3; omega

theorem sound_degPos {cl : List Nat} (h : ckDegPos M cl = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | a :: rest, h =>
    simp only [ckDegPos, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨ha, hr⟩, hm⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp)
    rw [lit_negP ha, Bool.not_eq_false'] at fa
    have h0 : cnt S (nbrs (vl M a)) = 0 := by
      apply cnt_zero; rw [← hm]; intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      have := hf x (by simp [hx]); rwa [lit_posP (hr x hx)] at this
    have := ax.deg_pos _ fa; omega

theorem sound_endSel {cl : List Nat} (h : ckEndSel M cl = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckEndSel, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨ha, hb⟩, he⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negE ha, Bool.not_eq_false'] at fa
    rw [lit_posP hb, ← he, ax.end_sel _ fa] at fb
    exact absurd fb (by decide)

theorem sound_lowEnd {cl : List Nat} {t : Nat} (h : ckLowEnd M t cl = true)
    (ax : Axioms S E w cens) : clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | a :: b :: rest, h =>
    simp only [ckLowEnd, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨ha, hb⟩, he⟩, hr⟩, hm⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negP ha, Bool.not_eq_false'] at fa
    rw [lit_posE hb, ← he] at fb
    have h1 : cnt S (nbrs (vl M a)) ≤ 1 := by
      apply cnt_eraseIdx _ t; rw [← hm]; intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      have := hf x (by simp [hx]); rwa [lit_posP (hr x hx)] at this
    rw [ax.low_end _ fa h1] at fb
    exact absurd fb (by decide)

theorem sound_endLow {cl : List Nat} (h : ckEndLow M cl = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b, c], h =>
    simp only [ckEndLow, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, hs⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp); have fc := hf c (by simp)
    rw [lit_negE ha, Bool.not_eq_false'] at fa
    rw [lit_negP hb, Bool.not_eq_false'] at fb
    rw [lit_negP hc, Bool.not_eq_false'] at fc
    have h2 := cnt_ge hs (S := S) (by simp [fb, fc])
    have h1 := ax.end_low _ fa
    simp at h2; omega

theorem sound_cut {cl : List Nat} (h : ckCut M cl = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  simp only [ckCut, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hne, hN⟩, hc⟩ := h
  apply clause_intro; intro hf
  obtain ⟨v, hv, hS⟩ := ax.acyclic (cl.map (vl M)) (by simpa using hne) hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
  have := hf x hx
  rw [lit_negP (hN x hx), hS] at this
  exact absurd this (by decide)

theorem sound_first {cl : List Nat} {c i : Nat} (h : ckFirst M cs c i cl = true)
    (hcs : cs.all (ctrOK M cens) = true) : clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckFirst, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, ha⟩, hb⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negOf ha (ctr_lit_ok (ctrOK_getD hcs c) hi), Bool.not_eq_false'] at fa
    rw [lit_posR hb, decide_eq_false_iff_not] at fb
    apply fb
    unfold pc; rw [take_succ_countP hi, if_pos fa]; omega

theorem sound_zero {cl : List Nat} {c j : Nat} (h : ckZero M c j cl = true) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a], h =>
    simp only [ckZero, Bool.and_eq_true, decide_eq_true_eq] at h
    apply clause_intro; intro hf
    have fa := hf a (by simp)
    rw [lit_negR h.2, Bool.not_eq_false', decide_eq_true_eq] at fa
    have := pc_zero (S := S) (E := E) (M := M) (cs.getD c dfltCtr).lits
    omega

theorem sound_mono {cl : List Nat} {c i j : Nat} (h : ckMono M c i j cl = true) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckMono, Bool.and_eq_true] at h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negR h.1, Bool.not_eq_false', decide_eq_true_eq] at fa
    rw [lit_posR h.2, decide_eq_false_iff_not] at fb
    have := pc_mono (S := S) (E := E) (M := M) (cs.getD c dfltCtr).lits i
    omega

theorem sound_step {cl : List Nat} {c i j : Nat} (h : ckStep M cs c i j cl = true)
    (hcs : cs.all (ctrOK M cens) = true) : clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b, d], h =>
    simp only [ckStep, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, ha⟩, hb⟩, hd⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp); have fd := hf d (by simp)
    rw [lit_negOf ha (ctr_lit_ok (ctrOK_getD hcs c) hi), Bool.not_eq_false'] at fa
    rw [lit_negR hb, Bool.not_eq_false', decide_eq_true_eq] at fb
    rw [lit_posR hd, decide_eq_false_iff_not] at fd
    rw [pc_succ hi, if_pos fa] at fd
    omega

theorem sound_over {cl : List Nat} {c i : Nat} (h : ckOver M cs c i cl = true)
    (hcs : cs.all (ctrOK M cens) = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  match cl, h with
  | [a, b], h =>
    simp only [ckOver, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, ha⟩, hk⟩, hb⟩ := h
    apply clause_intro; intro hf
    have fa := hf a (by simp); have fb := hf b (by simp)
    rw [lit_negOf ha (ctr_lit_ok (ctrOK_getD hcs c) hi), Bool.not_eq_false'] at fa
    rw [lit_negR hb, Bool.not_eq_false', decide_eq_true_eq] at fb
    have h1 := pc_succ (S := S) (E := E) (M := M) hi
    rw [if_pos fa] at h1
    have h2 := pc_le_total (S := S) (E := E) (M := M) (cs.getD c dfltCtr).lits (i + 1)
    have h3 := ctr_bound (ctrOK_getD hcs c) ax
    omega

theorem sound_clause {t : Tag} {cl : List Nat} (h : ckClause M cs w t cl = true)
    (hcs : cs.all (ctrOK M cens) = true) (ax : Axioms S E w cens) :
    clauseTrue (tau S E M cs) (cl.map decodeLit) = true := by
  cases t with
  | window => exact sound_window h ax
  | deg2 => exact sound_deg2 h ax
  | degPos => exact sound_degPos h ax
  | endSel => exact sound_endSel h ax
  | lowEnd t => exact sound_lowEnd h ax
  | endLow => exact sound_endLow h ax
  | cut => exact sound_cut h ax
  | first c i => exact sound_first h hcs
  | zero c j => exact sound_zero h
  | mono c i j => exact sound_mono h
  | step c i j => exact sound_step h hcs
  | over c i => exact sound_over h hcs ax

theorem sound_all : ∀ {tags : List Tag} {raw : List (List Nat)}, ckAll M cs w tags raw = true →
    cs.all (ctrOK M cens) = true → Axioms S E w cens →
    ∀ cl ∈ raw, clauseTrue (tau S E M cs) (cl.map decodeLit) = true
  | [], [], _, _, _ => by simp
  | t :: ts, cl :: cls, h, hcs, ax => by
    simp only [ckAll, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact sound_clause h.1 hcs ax
    · exact sound_all h.2 hcs ax x hx
  | [], _ :: _, h, _, _ => by simp [ckAll] at h
  | _ :: _, [], h, _, _ => by simp [ckAll] at h

end Families

/-- Main soundness theorem: a checked certificate yields a satisfying assignment of
the core from any `S`, `E` satisfying the axioms. -/
theorem sound (M : MT) (cs : List Ctr) (w : List Nat) (b : List (Nat × Nat)) (tags : List Tag)
    (raw : List (List Nat)) (h : checkAll M cs w b tags raw = true) (S E : Nat → Bool)
    (ax : Axioms S E w (centresOf w b)) :
    cnfTrue (tau S E M cs) (raw.map (·.map decodeLit)) = true := by
  simp only [checkAll, Bool.and_eq_true] at h
  rw [centresK_eq] at ax
  unfold cnfTrue
  rw [List.all_map, List.all_eq_true]
  intro cl hcl
  exact sound_all h.2 h.1 ax cl hcl

/-- A certificate's `sat` theorem and the refutation of its core give `Refuted`. -/
theorem refuted_of_sat {window : List Nat} {bounds : List (Nat × Nat)} {f : List (List Int)}
    (hsat : ∀ S E : Nat → Bool, Axioms S E window (centresOf window bounds) →
      ∃ τ, cnfTrue τ f = true)
    (hunsat : Unsat f) : Refuted window bounds := by
  intro S E ax
  obtain ⟨τ, hτ⟩ := hsat S E ax
  rw [hunsat τ] at hτ
  exact Bool.false_ne_true hτ

end Snake9.LocalWindow.Tags
