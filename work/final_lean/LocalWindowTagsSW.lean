import LocalWindowTagsW
import LocalWindowTagsShare

/-!
# Share clause soundness with flat meaning tables (Sat v2, share)

The share checker `Tags.checkAllS` / `Tags.soundS` of `LocalWindowTagsShare` (unchanged, used by
main's share floors), copied with the change of `LocalWindowTagsW`: both meaning trees are
functions, `M : Nat → MT` (window variables) and `X : Nat → MS` (share variables), so a
certificate can pass flat tables (`TagsW.getF` and `getSF`, one shift and one mask per lookup).
The old window families are checked by the kernel-native `TagsW.ckClauseK` and the counters by
`TagsW.ctrOKK` (equal to `TagsW.ckClause` and `TagsW.ctrOK` by `ckClauseK_eq`, `ctrOKK_eq`);
the share families are those of `LocalWindowTagsShare`.  `soundS` holds for every pair of
lookup functions, totalizer list and tag list that `checkAllS` accepts, so the decoders need no
proofs.  Its statement is that of `Tags.soundS` with `tauS` over the functions, so
`Tags.refutedShare_of_sat` applies unchanged.  Measured on main's share floor 7300 in
`milestones/26-replay-efficiency/README.md`, "Sat v2"; no generator writes this format yet.
-/

namespace Snake9.LocalWindow.TagsSW

open Snake9.LocalWindow
open Snake9.LocalWindow.Tags (MT Kind Ctr Tag dfltCtr dfltCentre centresK centresK_eq MS TotKind Tot dfltTot TagS)
open Snake9.LocalWindow.TagsW

noncomputable section

/-! ## The assignment -/

/-- `⌊Mr · e0(q) / d(q)⌋`, the share `q` gives to each selected neighbour. -/
def fl (Mr : Nat) (S : Nat → Bool) (q : Nat) : Nat := Mr * emptyCount S q / cnt S (nbrs q)

/-- `x` is a window variable. -/
def oldVar (M : Nat → MT) (x : Nat) : Bool :=
  match M x with
  | .p _ => true
  | .e _ => true
  | .r _ _ _ => true
  | _ => false

/-- Values of the square and threshold variables. -/
def sval (S : Nat → Bool) (Mr : Nat) (X : Nat → MS) (x : Nat) : Bool :=
  match X x with
  | .sq q a b => emptyPred S q (a, b)
  | .u q t => decide (t ≤ fl Mr S q)
  | _ => false

/-- Values of the totalizer inputs. -/
def baseS (S E : Nat → Bool) (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (x : Nat) : Bool :=
  if oldVar M x then base S E M x else sval S Mr X x

/-- The block `[lo, hi)` of a list. -/
def blk (l : List Nat) (lo hi : Nat) : List Nat := (l.drop lo).take (hi - lo)

/-- Number of true literals in the block `[lo, hi)` of totalizer `i`. -/
def bc (S E : Nat → Bool) (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (tots : List Tot) (i lo hi : Nat) : Nat :=
  (blk (tots.getD i dfltTot).lits lo hi).countP (lv (baseS S E M X Mr))

def tauS (S E : Nat → Bool) (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot)
    (x : Nat) : Bool :=
  if oldVar M x then tau S E M cs x else
  match X x with
  | .t i lo hi c => decide (c ≤ bc S E M X Mr tots i lo hi)
  | _ => sval S Mr X x

/-! ## The checker -/

/-- A positive literal over a share variable. -/
def posS (M : Nat → MT) (a : Nat) : Bool := a % 2 == 0 && decide (2 ≤ a) && !oldVar M (a / 2)

def sqOf (X : Nat → MS) (a : Nat) : Option (Nat × Nat × Nat) :=
  match X (a / 2) with
  | .sq q a b => some (q, a, b)
  | _ => none

def uOf (X : Nat → MS) (a : Nat) : Option (Nat × Nat) :=
  match X (a / 2) with
  | .u q t => some (q, t)
  | _ => none

/-- Square vertex and pair of a literal (`(0, 0, 0)` if it is not a square literal). -/
def sqQ (X : Nat → MS) (a : Nat) : Nat := ((sqOf X a).getD (0, 0, 0)).1
def sqAB (X : Nat → MS) (a : Nat) : Nat × Nat := ((sqOf X a).getD (0, 0, 0)).2
def uQT (X : Nat → MS) (a : Nat) : Nat × Nat := (uOf X a).getD (0, 0)

def isSq (X : Nat → MS) (a : Nat) : Bool := (sqOf X a).isSome
def isU (X : Nat → MS) (a : Nat) : Bool := (uOf X a).isSome

def posSq (M : Nat → MT) (X : Nat → MS) (a : Nat) : Bool := posS M a && isSq X a
def posU (M : Nat → MT) (X : Nat → MS) (a : Nat) : Bool := posS M a && isU X a

/-- A literal over a primary, an endpoint flag, a square or a threshold variable. -/
def baseOKS (M : Nat → MT) (X : Nat → MS) (l : Nat) : Bool :=
  decide (2 ≤ l) &&
    if oldVar M (l / 2) then isP M (l / 2) || isE M (l / 2) else isSq X l || isU X l

/-- The block meaning of a positive totalizer literal of totalizer `i`. -/
def tInfo (M : Nat → MT) (X : Nat → MS) (i a : Nat) : Option (Nat × Nat × Nat) :=
  if posS M a then
    match X (a / 2) with
    | .t i' lo hi c => if i' = i then some (lo, hi, c) else none
    | _ => none
  else none

/-- The block meaning `(lo, hi, c)` of a literal of totalizer `i`: a totalizer output,
or the input literal at position `pos` itself (a leaf, block `[pos, pos+1)`, `c = 1`). -/
def litInfo (M : Nat → MT) (X : Nat → MS) (tots : List Tot) (i a pos : Nat) : Option (Nat × Nat × Nat) :=
  match tInfo M X i a with
  | some r => some r
  | none =>
    if a = (tots.getD i dfltTot).lits.getD pos 0 ∧ pos < (tots.getD i dfltTot).lits.length then
      some (pos, pos + 1, 1) else none

/-- The negation of a literal code. -/
def negL (x : Nat) : Nat := if x % 2 = 0 then x + 1 else x - 1

/-- Greedy sublist test. -/
def sublG {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then sublG as bs else sublG (a :: as) bs

/-- The threshold literals of the cap totalizer, per centre and neighbour. -/
def capL : List Centre → List (List (Nat × Nat)) → List (Nat × Nat)
  | c :: cs, s :: ss =>
    (s.flatMap fun kt => (List.range kt.2).map fun t => (c.v ^^^ (1 <<< kt.1), t + 1)) ++ capL cs ss
  | _, _ => []

def totOK (M : Nat → MT) (X : Nat → MS) (w : List Nat) (cens : List Centre) (t : Tot) : Bool :=
  t.lits.all (baseOKS M X) &&
  match t.kind with
  | .emp q => t.lits.all (fun a => posSq M X a && sqQ X a == q) &&
      sublG (t.lits.map (sqAB X)) (freePairs 9 9)
  | .nb q => t.lits.all (posP M) && t.lits.map (vl M) == nbrs q &&
      (nbrs q).any (fun v => w.contains v)
  | .cap spec => t.lits.all (posU M X) && t.lits.map (uQT X) == capL cens spec &&
      spec.all (fun s => subl (s.map (·.1)) (List.range 9))

def isEmp (q : Nat) : TotKind → Bool
  | .emp q' => q' == q
  | _ => false

def isNb (q : Nat) : TotKind → Bool
  | .nb q' => q' == q
  | _ => false

def isCap : TotKind → Bool
  | .cap _ => true
  | _ => false

def oldLits (M : Nat → MT) (cl : List Nat) : Bool := cl.all fun a => decide (2 ≤ a) && oldVar M (a / 2)

def ckEmptyE (M : Nat → MT) (X : Nat → MS) : List Nat → Bool
  | [a1, a2, a3, a4, e] => posP M a1 && posP M a2 && posP M a3 && posP M a4 && posSq M X e &&
      vl M a1 == sqQ X e && vl M a2 == sqQ X e ^^^ (1 <<< (sqAB X e).1) &&
      vl M a3 == sqQ X e ^^^ (1 <<< (sqAB X e).2) &&
      vl M a4 == sqQ X e ^^^ (1 <<< (sqAB X e).1) ^^^ (1 <<< (sqAB X e).2)
  | _ => false

def subUp (lo hi c : Nat) : Option (Nat × Nat × Nat) → Bool
  | some (l, h, c1) => decide (lo ≤ l ∧ l ≤ h ∧ h ≤ hi ∧ c ≤ c1)
  | none => false

def subDown (lo hi c : Nat) : Option (Nat × Nat × Nat) → Bool
  | some (l, h, c1) => decide (lo ≤ l ∧ l ≤ h ∧ h ≤ hi ∧ l - lo + c1 + (hi - h) ≤ c)
  | none => false

def twoUp (lo hi c : Nat) : Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat) → Bool
  | some (l1, h1, c1), some (l2, h2, c2) =>
    decide (lo ≤ l1 ∧ l1 ≤ h1 ∧ h1 ≤ l2 ∧ l2 ≤ h2 ∧ h2 ≤ hi ∧ c ≤ c1 + c2)
  | _, _ => false

def twoDown (lo hi c : Nat) : Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat) → Bool
  | some (l1, h1, c1), some (l2, h2, c2) =>
    decide (lo ≤ l1 ∧ l1 ≤ h1 ∧ h1 ≤ l2 ∧ l2 ≤ h2 ∧ h2 ≤ hi ∧
      l1 - lo + c1 + (l2 - h1) + c2 + (hi - h2) ≤ c + 1)
  | _, _ => false

def ckTotUp (M : Nat → MT) (X : Nat → MS) (tots : List Tot) (i : Nat) : List Nat → Bool
  | [o, x] => decide (2 ≤ x) &&
    match tInfo M X i o with
    | some (lo, hi, c) => subUp lo hi c (litInfo M X tots i (negL x) lo) ||
        subUp lo hi c (litInfo M X tots i (negL x) (hi - 1))
    | none => false
  | [o, x, y] => decide (2 ≤ x) && decide (2 ≤ y) &&
    match tInfo M X i o with
    | some (lo, hi, c) =>
      twoUp lo hi c (litInfo M X tots i (negL x) lo) (litInfo M X tots i (negL y) (hi - 1))
    | none => false
  | _ => false

def ckTotDown (M : Nat → MT) (X : Nat → MS) (tots : List Tot) (i : Nat) : List Nat → Bool
  | [o, x] => decide (2 ≤ o) && decide (2 ≤ x) &&
    match tInfo M X i (negL o) with
    | some (lo, hi, c) => subDown lo hi c (litInfo M X tots i x lo) ||
        subDown lo hi c (litInfo M X tots i x (hi - 1))
    | none => false
  | [o, x, y] => decide (2 ≤ o) && decide (2 ≤ x) && decide (2 ≤ y) &&
    match tInfo M X i (negL o) with
    | some (lo, hi, c) =>
      twoDown lo hi c (litInfo M X tots i x lo) (litInfo M X tots i y (hi - 1))
    | none => false
  | _ => false

def ckShareCl (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (tots : List Tot) (eT dT : Nat) : List Nat → Bool
  | [u, x] => decide (2 ≤ x) && posU M X u &&
    isEmp (uQT X u).1 (tots.getD eT dfltTot).kind &&
    isNb (uQT X u).1 (tots.getD dT dfltTot).kind &&
    match litInfo M X tots eT (negL x) 0 with
    | some (_, _, cn) => decide ((uQT X u).2 * 9 ≤ Mr * cn)
    | none => false
  | [u, x, y] => decide (2 ≤ x) && decide (2 ≤ y) && posU M X u &&
    isEmp (uQT X u).1 (tots.getD eT dfltTot).kind &&
    isNb (uQT X u).1 (tots.getD dT dfltTot).kind &&
    match litInfo M X tots eT (negL x) 0, litInfo M X tots dT y 0 with
    | some (_, _, cn), some (l, h, c2) =>
      decide (l = 0 ∧ 9 ≤ h ∧ (uQT X u).2 * (c2 - 1) ≤ Mr * cn)
    | _, _ => false
  | _ => false

def ckShareCap (M : Nat → MT) (X : Nat → MS) (tots : List Tot) (cap i : Nat) : List Nat → Bool
  | [x] => decide (2 ≤ x) && isCap (tots.getD i dfltTot).kind &&
    match tInfo M X i (negL x) with
    | some (_, _, c) => decide (cap + 1 ≤ c)
    | none => false
  | _ => false

def ckClauseS (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (cap : Nat) : TagS → List Nat → Bool
  | .old t, cl => oldLits M cl && ckClauseK M cs w t cl
  | .emptyE, cl => ckEmptyE M X cl
  | .totUp i, cl => ckTotUp M X tots i cl
  | .totDown i, cl => ckTotDown M X tots i cl
  | .shareCl eT dT, cl => ckShareCl M X Mr tots eT dT cl
  | .shareCap i, cl => ckShareCap M X tots cap i cl

def ckAllS (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (cap : Nat) : List TagS → List (List Nat) → Bool
  | [], [] => true
  | t :: ts, cl :: cls => ckClauseS M X Mr cs tots w cap t cl && ckAllS M X Mr cs tots w cap ts cls
  | _, _ => false

/-- The share checker: counters, totalizers, and one tag per core clause. -/
def checkAllS (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (b : List (Nat × Nat)) (cap : Nat) (tags : List TagS) (raw : List (List Nat)) : Bool :=
  allK (ctrOKK M (centresK w b)) cs && tots.all (totOK M X w (centresK w b)) &&
    ckAllS M X Mr cs tots w cap tags raw

/-! ## Soundness -/

section Lemmas

variable {S E : Nat → Bool} {M : Nat → MT} {X : Nat → MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}

theorem lv_congr {τ₁ τ₂ : Nat → Bool} {a : Nat} (h : τ₁ (a / 2) = τ₂ (a / 2)) :
    lv τ₁ a = lv τ₂ a := by
  unfold lv; rw [h]

theorem lv_negL (τ : Nat → Bool) {x : Nat} (hx : 2 ≤ x) : lv τ (negL x) = !lv τ x := by
  unfold negL lv
  by_cases h : x % 2 = 0
  · have h1 : (x + 1) % 2 = 1 := by omega
    have h2 : (x + 1) / 2 = x / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (x - 1) % 2 = 0 := by omega
    have h2 : (x - 1) / 2 = x / 2 := by omega
    simp [h, h1, h2]

theorem negL_ge {x : Nat} (hx : 2 ≤ x) : 2 ≤ negL x := by
  unfold negL; split <;> omega

theorem oldVar_of_isP {x : Nat} (h : isP M x = true) : oldVar M x = true := by
  simp [oldVar, isP_get h]

theorem oldVar_of_isE {x : Nat} (h : isE M x = true) : oldVar M x = true := by
  simp [oldVar, isE_get h]

theorem tauS_old {x : Nat} (h : oldVar M x = true) :
    tauS S E M X Mr cs tots x = tau S E M cs x := by
  unfold tauS; rw [if_pos h]

theorem baseS_old {x : Nat} (h : oldVar M x = true) :
    baseS S E M X Mr x = base S E M x := by
  unfold baseS; rw [if_pos h]

theorem sqOf_get {a q x y : Nat} (h : sqOf X a = some (q, x, y)) : X (a / 2) = .sq q x y := by
  unfold sqOf at h; split at h <;> simp_all

theorem uOf_get {a q t : Nat} (h : uOf X a = some (q, t)) : X (a / 2) = .u q t := by
  unfold uOf at h; split at h <;> simp_all

theorem sqOf_of_isSq {a : Nat} (h : isSq X a = true) :
    sqOf X a = some (sqQ X a, sqAB X a) := by
  unfold isSq at h; unfold sqQ sqAB
  cases hs : sqOf X a with
  | none => rw [hs] at h; simp at h
  | some r => simp

theorem uOf_of_isU {a : Nat} (h : isU X a = true) : uOf X a = some (uQT X a) := by
  unfold isU at h; unfold uQT
  cases hs : uOf X a with
  | none => rw [hs] at h; simp at h
  | some r => simp

theorem sval_sq {a : Nat} (h : isSq X a = true) :
    sval S Mr X (a / 2) = emptyPred S (sqQ X a) (sqAB X a) := by
  have := sqOf_get (sqOf_of_isSq h)
  unfold sval; rw [this]; rfl

theorem sval_u {a : Nat} (h : isU X a = true) :
    sval S Mr X (a / 2) = decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  have := uOf_get (uOf_of_isU h)
  unfold sval; rw [this]; rfl

theorem tauS_su {a : Nat} (hn : oldVar M (a / 2) = false) (h : isSq X a = true ∨ isU X a = true) :
    tauS S E M X Mr cs tots (a / 2) = sval S Mr X (a / 2) := by
  unfold tauS; rw [if_neg (by simp [hn])]
  rcases h with h | h
  · rw [sqOf_get (sqOf_of_isSq h)]
  · rw [uOf_get (uOf_of_isU h)]

/-- On a totalizer input, `tauS` and `baseS` agree. -/
theorem lv_base_ok {l : Nat} (h : baseOKS M X l = true) :
    lv (tauS S E M X Mr cs tots) l = lv (baseS S E M X Mr) l := by
  simp only [baseOKS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, h⟩ := h
  apply lv_congr
  by_cases ho : oldVar M (l / 2) = true
  · rw [if_pos ho, Bool.or_eq_true] at h
    rw [tauS_old ho, baseS_old ho]
    rcases h with hp | hp
    · simp [tau, base, isP_get hp]
    · simp [tau, base, isE_get hp]
  · rw [if_neg ho, Bool.or_eq_true] at h
    have hn : oldVar M (l / 2) = false := by simpa using ho
    rw [tauS_su hn h]
    unfold baseS; rw [if_neg ho]

theorem posS_parts {a : Nat} (h : posS M a = true) :
    a % 2 = 0 ∧ 2 ≤ a ∧ oldVar M (a / 2) = false := by
  simp only [posS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lit_posP_S {a : Nat} (h : posP M a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) = S (vl M a) := by
  have h' := h
  simp only [posP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  obtain ⟨⟨h0, h2⟩, hp⟩ := h'
  rw [decode_eq _ h2]
  simp [lv, h0, tauS_old (oldVar_of_isP hp), tau, vl, isP_get hp]

theorem base_posSq {a : Nat} (h : posSq M X a = true) :
    lv (baseS S E M X Mr) a = emptyPred S (sqQ X a) (sqAB X a) := by
  simp only [posSq, Bool.and_eq_true] at h
  obtain ⟨h0, h2, hn⟩ := posS_parts h.1
  simp only [lv, h0, if_true]
  unfold baseS; rw [if_neg (by simp [hn]), sval_sq h.2]

theorem base_posU {a : Nat} (h : posU M X a = true) :
    lv (baseS S E M X Mr) a = decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  simp only [posU, Bool.and_eq_true] at h
  obtain ⟨h0, h2, hn⟩ := posS_parts h.1
  simp only [lv, h0, if_true]
  unfold baseS; rw [if_neg (by simp [hn]), sval_u h.2]

theorem lit_posSq {a : Nat} (h : posSq M X a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) = emptyPred S (sqQ X a) (sqAB X a) := by
  have h' := h
  simp only [posSq, Bool.and_eq_true] at h'
  obtain ⟨h0, h2, hn⟩ := posS_parts h'.1
  rw [decode_eq _ h2]
  simp only [lv, h0, if_true]
  rw [tauS_su hn (Or.inl h'.2), sval_sq h'.2]

theorem lit_posU {a : Nat} (h : posU M X a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) =
      decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  have h' := h
  simp only [posU, Bool.and_eq_true] at h'
  obtain ⟨h0, h2, hn⟩ := posS_parts h'.1
  rw [decode_eq _ h2]
  simp only [lv, h0, if_true]
  rw [tauS_su hn (Or.inr h'.2), sval_u h'.2]

theorem tInfo_sem {i a lo hi c : Nat} (h : tInfo M X i a = some (lo, hi, c)) :
    lv (tauS S E M X Mr cs tots) a = decide (c ≤ bc S E M X Mr tots i lo hi) := by
  unfold tInfo at h
  split at h
  · rename_i hp
    obtain ⟨h0, _, hn⟩ := posS_parts hp
    split at h
    · rename_i i' lo' hi' c' hX
      split at h
      · rename_i hi'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        subst hi'
        simp only [lv, h0, if_true]
        unfold tauS; rw [if_neg (by simp [hn]), hX]
      · simp at h
    · simp at h
  · simp at h

/-! ### Blocks -/

theorem blk_split (l : List Nat) {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    blk l lo hi = blk l lo mid ++ blk l mid hi := by
  unfold blk
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, List.take_add, List.drop_drop,
    show lo + (mid - lo) = mid by omega]

theorem countP_blk_split (f : Nat → Bool) (l : List Nat) {lo mid hi : Nat} (h1 : lo ≤ mid)
    (h2 : mid ≤ hi) :
    (blk l lo hi).countP f = (blk l lo mid).countP f + (blk l mid hi).countP f := by
  rw [blk_split l h1 h2, List.countP_append]

theorem countP_blk_le (f : Nat → Bool) (l : List Nat) (lo hi : Nat) :
    (blk l lo hi).countP f ≤ hi - lo :=
  Nat.le_trans (List.countP_le_length) (List.length_take_le _ _)

theorem countP_blk_total (f : Nat → Bool) (l : List Nat) (lo hi : Nat) :
    (blk l lo hi).countP f ≤ l.countP f :=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).countP_le

theorem totOK_getD {w : List Nat} {cens : List Centre} (h : tots.all (totOK M X w cens) = true)
    (i : Nat) : totOK M X w cens (tots.getD i dfltTot) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hc : tots[i]? with
  | none => simp [totOK, dfltTot, capL]
  | some t => exact List.all_eq_true.1 h t (List.mem_of_getElem? hc)

theorem totOK_lits {w : List Nat} {cens : List Centre} {t : Tot} (h : totOK M X w cens t = true) :
    ∀ l ∈ t.lits, baseOKS M X l = true := by
  unfold totOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem litInfo_sem {w : List Nat} {cens : List Centre} (ht : tots.all (totOK M X w cens) = true)
    {i a pos lo hi c : Nat} (h : litInfo M X tots i a pos = some (lo, hi, c)) :
    lv (tauS S E M X Mr cs tots) a = decide (c ≤ bc S E M X Mr tots i lo hi) := by
  unfold litInfo at h
  split at h
  · rename_i r hr
    simp only [Option.some.injEq] at h
    subst h
    exact tInfo_sem hr
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨ha, hpos⟩ := hc
      have hmem : a ∈ (tots.getD i dfltTot).lits := by rw [ha]; exact getD_mem hpos
      rw [lv_base_ok (totOK_lits (totOK_getD ht i) a hmem)]
      unfold bc blk
      rw [show pos + 1 - pos = 1 by omega, List.drop_eq_getElem_cons hpos]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos] at ha
      simp only [Option.getD_some] at ha
      rw [← ha]
      cases hb : lv (baseS S E M X Mr) a <;> simp [hb]
    · simp at h

/-! ### Totalizer kinds -/

theorem sublG_sublist {α : Type} [DecidableEq α] : ∀ {l m : List α}, sublG l m = true → l.Sublist m
  | [], _, _ => List.nil_sublist _
  | _ :: _, [], h => by simp [sublG] at h
  | a :: as, b :: bs, h => by
    unfold sublG at h
    by_cases hab : a = b
    · subst hab; simp only [if_true] at h; exact (sublG_sublist h).cons₂ a
    · simp only [hab, if_false] at h; exact (sublG_sublist h).cons b

theorem emp_total {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .emp q) :
    t.lits.countP (lv (baseS S E M X Mr)) ≤ emptyCount S q := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, hs, hsub⟩ := h
  have : t.lits.countP (lv (baseS S E M X Mr)) = (t.lits.map (sqAB X)).countP (emptyPred S q) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro a ha
    obtain ⟨h1, h2⟩ := hs a ha
    rw [base_posSq h1, h2]; rfl
  rw [this]
  unfold emptyCount
  rw [← List.countP_eq_length_filter]
  exact (sublG_sublist hsub).countP_le

theorem nb_total {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .nb q) :
    t.lits.countP (lv (baseS S E M X Mr)) = cnt S (nbrs q) ∧ t.lits.length = 9 := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, hp, hm, _⟩ := h
  constructor
  · unfold cnt
    rw [← List.countP_eq_length_filter, ← hm, List.countP_map]
    apply List.countP_congr
    intro a ha
    have hP : isP M (a / 2) = true := by
      have := hp a ha
      simp only [posP, Bool.and_eq_true] at this; exact this.2
    have hb : lv (baseS S E M X Mr) a = S (vl M a) := by
      rw [lv_congr (τ₂ := base S E M) (baseS_old (oldVar_of_isP hP))]
      exact base_posP (hp a ha)
    simp [hb]
  · have := congrArg List.length hm
    rw [List.length_map] at this
    rw [this]; rfl

theorem nb_pos {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .nb q) (hw : ∀ v ∈ w, S v = true) :
    1 ≤ cnt S (nbrs q) := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.contains_iff_mem, and_assoc] at h
  obtain ⟨_, _, _, v, hv, hvw⟩ := h
  unfold cnt
  rw [← List.countP_eq_length_filter]
  exact List.countP_pos_iff.2 ⟨v, hv, hw v hvw⟩

theorem sum_sublist_le : ∀ {l₁ l₂ : List Nat}, l₁.Sublist l₂ → l₁.sum ≤ l₂.sum
  | _, _, .slnil => Nat.le_refl _
  | _, _, .cons a h => by rw [List.sum_cons]; have := sum_sublist_le h; omega
  | _, _, .cons₂ a h => by rw [List.sum_cons, List.sum_cons]; have := sum_sublist_le h; omega

theorem sum_map_le {α : Type} {f g : α → Nat} : ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := sum_map_le (l := l) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem countP_range_le (x : Nat) : ∀ n, (List.range n).countP (fun t => decide (t + 1 ≤ x)) ≤ x
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append]
    have ih := countP_range_le x n
    have hl : (List.range n).countP (fun t => decide (t + 1 ≤ x)) ≤ n := by
      have := List.countP_le_length (p := fun t => decide (t + 1 ≤ x)) (l := List.range n)
      rwa [List.length_range] at this
    by_cases hx : n + 1 ≤ x
    · simp [hx]; omega
    · simp [hx]; omega

theorem shareSum_cons (c : Centre) (cens : List Centre) :
    shareSum Mr S (c :: cens) = shareLocal Mr S c.v + shareSum Mr S cens := by
  simp [shareSum]

theorem shareLocal_fl (x : Nat) :
    shareLocal Mr S x = ((List.range 9).map fun k => fl Mr S (x ^^^ (1 <<< k))).sum := rfl

theorem capL_le : ∀ (cens : List Centre) (spec : List (List (Nat × Nat))),
    (∀ s ∈ spec, subl (s.map (·.1)) (List.range 9) = true) →
    (capL cens spec).countP (fun p => decide (p.2 ≤ fl Mr S p.1)) ≤ shareSum Mr S cens
  | [], _, _ => by simp [capL]
  | _ :: _, [], _ => by simp [capL]
  | c :: cens, s :: spec, hs => by
    simp only [capL]
    rw [List.countP_append, shareSum_cons]
    have ih := capL_le cens spec (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
    have h1 : (s.flatMap fun kt => (List.range kt.2).map fun t => (c.v ^^^ (1 <<< kt.1), t + 1)).countP
        (fun p => decide (p.2 ≤ fl Mr S p.1)) ≤
        ((s.map (·.1)).map fun k => fl Mr S (c.v ^^^ (1 <<< k))).sum := by
      rw [List.countP_flatMap, List.map_map]
      apply sum_map_le
      intro kt _
      simp only [Function.comp, List.countP_map]
      exact countP_range_le (fl Mr S (c.v ^^^ 1 <<< kt.1)) kt.2
    have h2 := sum_sublist_le ((subl_sublist (hs s List.mem_cons_self)).map
      (fun k => fl Mr S (c.v ^^^ (1 <<< k))))
    rw [shareLocal_fl]
    omega

theorem cap_total {w : List Nat} {cens : List Centre} {t : Tot}
    (h : totOK M X w cens t = true) (hk : isCap t.kind = true) :
    t.lits.countP (lv (baseS S E M X Mr)) ≤ shareSum Mr S cens := by
  unfold totOK at h
  cases hk' : t.kind with
  | emp q => rw [hk'] at hk; simp [isCap] at hk
  | nb q => rw [hk'] at hk; simp [isCap] at hk
  | cap spec =>
    rw [hk'] at h
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨_, hu, hm, hs⟩ := h
    have : t.lits.countP (lv (baseS S E M X Mr)) =
        (t.lits.map (uQT X)).countP (fun p => decide (p.2 ≤ fl Mr S p.1)) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro a ha
      rw [base_posU (hu a ha)]; rfl
    rw [this, hm]
    exact capL_le cens spec hs

theorem bc_total (i lo hi : Nat) :
    bc S E M X Mr tots i lo hi ≤ (tots.getD i dfltTot).lits.countP (lv (baseS S E M X Mr)) :=
  countP_blk_total _ _ _ _

theorem old_clause {cl : List Nat} (ho : oldLits M cl = true)
    (h : clauseTrue (tau S E M cs) (cl.map decodeLit) = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  unfold clauseTrue at h ⊢
  rw [List.any_map, List.any_eq_true] at h ⊢
  obtain ⟨a, ha, hv⟩ := h
  refine ⟨a, ha, ?_⟩
  simp only [oldLits, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨h2, hv2⟩ := ho a ha
  simp only [Function.comp] at hv ⊢
  rw [decode_eq _ h2] at hv ⊢
  rwa [lv_congr (τ₂ := tau S E M cs) (tauS_old hv2)]

end Lemmas

/-! ### Clause families -/

section Families

variable {S E : Nat → Bool} {M : Nat → MT} {X : Nat → MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
  {w : List Nat} {cens : List Centre}

theorem sound_emptyE {cl : List Nat} (h : ckEmptyE M X cl = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [a1, a2, a3, a4, e], h =>
    simp only [ckEmptyE, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, he⟩, v1⟩, v2⟩, v3⟩, v4⟩ := h
    apply clause_intro; intro hf
    have f1 := hf a1 (by simp); have f2 := hf a2 (by simp)
    have f3 := hf a3 (by simp); have f4 := hf a4 (by simp); have fe := hf e (by simp)
    rw [lit_posP_S h1, v1] at f1
    rw [lit_posP_S h2, v2] at f2
    rw [lit_posP_S h3, v3] at f3
    rw [lit_posP_S h4, v4] at f4
    rw [lit_posSq he] at fe
    unfold emptyPred at fe
    rw [f1, f2, f3, f4] at fe
    exact absurd fe (by decide)

theorem lit_neg {τ : Nat → Bool} {x : Nat} (hx : 2 ≤ x) :
    litTrue τ (decodeLit x) = !lv τ (negL x) := by
  rw [decode_eq _ hx, lv_negL _ hx, Bool.not_not]

theorem sound_totUp {i : Nat} {cl : List Nat} (h : ckTotUp M X tots i cl = true)
    (ht : tots.all (totOK M X w cens) = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [o, x], h =>
    simp only [ckTotUp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hx, h⟩ := h
    split at h
    · rename_i lo hi c ho
      have ho2 : 2 ≤ o := by
        unfold tInfo at ho; split at ho
        · exact (posS_parts (by assumption)).2.1
        · simp at ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp)
      rw [decode_eq _ ho2, tInfo_sem ho, decide_eq_false_iff_not] at fo
      rw [lit_neg hx, Bool.not_eq_false'] at fx
      have key : ∀ pos, subUp lo hi c (litInfo M X tots i (negL x) pos) = true → False := by
        intro pos hs
        unfold subUp at hs
        split at hs
        · rename_i l hh c1 hl
          simp only [decide_eq_true_eq] at hs
          rw [litInfo_sem ht hl, decide_eq_true_eq] at fx
          have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := lo) (mid := l) (hi := hi) hs.1 (by omega)
          have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := l) (mid := hh) (hi := hi) hs.2.1 hs.2.2.1
          unfold bc at fo fx
          omega
        · simp at hs
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · exact key _ h
      · exact key _ h
    · simp at h
  | [o, x, y], h =>
    simp only [ckTotUp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hy⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      have ho2 : 2 ≤ o := by
        unfold tInfo at ho; split at ho
        · exact (posS_parts (by assumption)).2.1
        · simp at ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp); have fy := hf y (by simp)
      rw [decode_eq _ ho2, tInfo_sem ho, decide_eq_false_iff_not] at fo
      rw [lit_neg hx, Bool.not_eq_false'] at fx
      rw [lit_neg hy, Bool.not_eq_false'] at fy
      unfold twoUp at h
      split at h
      · rename_i l1 h1 c1 l2 h2 c2 hl1 hl2
        simp only [decide_eq_true_eq] at h
        rw [litInfo_sem ht hl1, decide_eq_true_eq] at fx
        rw [litInfo_sem ht hl2, decide_eq_true_eq] at fy
        have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := lo) (mid := l1) (hi := hi) h.1 (by omega)
        have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l1) (mid := h1) (hi := hi) h.2.1 (by omega)
        have s3 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := h1) (mid := l2) (hi := hi) h.2.2.1 (by omega)
        have s4 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l2) (mid := h2) (hi := hi) h.2.2.2.1 h.2.2.2.2.1
        unfold bc at fo fx fy
        omega
      · simp at h
    · simp at h

theorem sound_totDown {i : Nat} {cl : List Nat} (h : ckTotDown M X tots i cl = true)
    (ht : tots.all (totOK M X w cens) = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [o, x], h =>
    simp only [ckTotDown, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ho2, hx⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp)
      rw [lit_neg ho2, tInfo_sem ho, Bool.not_eq_false', decide_eq_true_eq] at fo
      rw [decode_eq _ hx] at fx
      have key : ∀ pos, subDown lo hi c (litInfo M X tots i x pos) = true → False := by
        intro pos hs
        unfold subDown at hs
        split at hs
        · rename_i l hh c1 hl
          simp only [decide_eq_true_eq] at hs
          rw [litInfo_sem ht hl, decide_eq_false_iff_not] at fx
          have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := lo) (mid := l) (hi := hi) hs.1 (by omega)
          have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := l) (mid := hh) (hi := hi) hs.2.1 hs.2.2.1
          have b1 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits lo l
          have b2 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits hh hi
          unfold bc at fo fx
          omega
        · simp at hs
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · exact key _ h
      · exact key _ h
    · simp at h
  | [o, x, y], h =>
    simp only [ckTotDown, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ho2, hx⟩, hy⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp); have fy := hf y (by simp)
      rw [lit_neg ho2, tInfo_sem ho, Bool.not_eq_false', decide_eq_true_eq] at fo
      rw [decode_eq _ hx] at fx
      rw [decode_eq _ hy] at fy
      unfold twoDown at h
      split at h
      · rename_i l1 h1 c1 l2 h2 c2 hl1 hl2
        simp only [decide_eq_true_eq] at h
        rw [litInfo_sem ht hl1, decide_eq_false_iff_not] at fx
        rw [litInfo_sem ht hl2, decide_eq_false_iff_not] at fy
        have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := lo) (mid := l1) (hi := hi) h.1 (by omega)
        have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l1) (mid := h1) (hi := hi) h.2.1 (by omega)
        have s3 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := h1) (mid := l2) (hi := hi) h.2.2.1 (by omega)
        have s4 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l2) (mid := h2) (hi := hi) h.2.2.2.1 h.2.2.2.2.1
        have b1 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits lo l1
        have b2 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits h1 l2
        have b3 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits h2 hi
        unfold bc at fo fx fy
        omega
      · simp at h
    · simp at h

theorem kind_emp {k : TotKind} {q : Nat} (h : isEmp q k = true) : k = .emp q := by
  cases k <;> simp_all [isEmp]

theorem kind_nb {k : TotKind} {q : Nat} (h : isNb q k = true) : k = .nb q := by
  cases k <;> simp_all [isNb]

/-- The arithmetic of a threshold clause: `u` false, `ge` true and `gd` false clash. -/
theorem share_arith {Mr e0 d t cn dd : Nat} (hd : 1 ≤ d) (hdd : d ≤ dd) (he : cn ≤ e0)
    (hm : t * dd ≤ Mr * cn) (hu : ¬ t ≤ Mr * e0 / d) : False := by
  apply hu
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact Nat.le_trans (Nat.mul_le_mul_left t hdd)
    (Nat.le_trans hm (Nat.mul_le_mul_left Mr he))

theorem sound_shareCl {eT dT : Nat} {cl : List Nat} (h : ckShareCl M X Mr tots eT dT cl = true)
    (ht : tots.all (totOK M X w cens) = true) (hw : ∀ v ∈ w, S v = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [u, x], h =>
    simp only [ckShareCl, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hx, hu⟩, he⟩, hn⟩, h⟩ := h
    split at h
    · rename_i l hh cn hl
      simp only [decide_eq_true_eq] at h
      apply clause_intro; intro hf
      have fu := hf u (by simp); have fx := hf x (by simp)
      rw [lit_posU hu, decide_eq_false_iff_not] at fu
      rw [lit_neg hx, Bool.not_eq_false', litInfo_sem ht hl, decide_eq_true_eq] at fx
      have hE := emp_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht eT) (kind_emp he)
      have hN := nb_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht dT) (kind_nb hn)
      have hP := nb_pos (totOK_getD ht dT) (kind_nb hn) hw
      have hB := bc_total (S := S) (E := E) (M := M) (X := X) (Mr := Mr) (tots := tots) eT l hh
      have h9 : cnt S (nbrs (uQT X u).1) ≤ 9 := by
        have := hN.2; rw [← hN.1]
        exact Nat.le_trans List.countP_le_length (by omega)
      exact share_arith hP h9 (by omega) h fu
    · simp at h
  | [u, x, y], h =>
    simp only [ckShareCl, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hx, hy⟩, hu⟩, he⟩, hn⟩, h⟩ := h
    split at h
    · rename_i l hh cn l2 h2 c2 hl hl2
      simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, h9, hm⟩ := h
      apply clause_intro; intro hf
      have fu := hf u (by simp); have fx := hf x (by simp); have fy := hf y (by simp)
      rw [lit_posU hu, decide_eq_false_iff_not] at fu
      rw [lit_neg hx, Bool.not_eq_false', litInfo_sem ht hl, decide_eq_true_eq] at fx
      rw [decode_eq _ hy, litInfo_sem ht hl2, decide_eq_false_iff_not] at fy
      have hE := emp_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht eT) (kind_emp he)
      have hN := nb_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht dT) (kind_nb hn)
      have hP := nb_pos (totOK_getD ht dT) (kind_nb hn) hw
      have hB := bc_total (S := S) (E := E) (M := M) (X := X) (Mr := Mr) (tots := tots) eT l hh
      have hall : bc S E M X Mr tots dT 0 h2 = cnt S (nbrs (uQT X u).1) := by
        unfold bc blk
        rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le (by omega)]
        exact hN.1
      rw [hall] at fy
      exact share_arith hP (Nat.le_sub_one_of_lt (by omega)) (by omega) hm fu
    · simp at h

theorem sound_shareCap {i cap : Nat} {cl : List Nat} (h : ckShareCap M X tots cap i cl = true)
    (ht : tots.all (totOK M X w cens) = true) (hs : shareSum Mr S cens ≤ cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [x], h =>
    simp only [ckShareCap, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hk⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      simp only [decide_eq_true_eq] at h
      apply clause_intro; intro hf
      have fx := hf x (by simp)
      rw [lit_neg hx, Bool.not_eq_false', tInfo_sem ho, decide_eq_true_eq] at fx
      have h1 := bc_total (S := S) (E := E) (M := M) (X := X) (Mr := Mr) (tots := tots) i lo hi
      have h2 := cap_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht i) hk
      omega
    · simp at h

theorem sound_clauseS {cap : Nat} {t : TagS} {cl : List Nat}
    (h : ckClauseS M X Mr cs tots w cap t cl = true)
    (hcs : cs.all (ctrOK M cens) = true) (ht : tots.all (totOK M X w cens) = true)
    (ax : AxiomsS S E w cens Mr cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  cases t with
  | old t =>
    simp only [ckClauseS, Bool.and_eq_true, ckClauseK_eq] at h
    exact old_clause h.1 (sound_clause h.2 hcs ax.toAxioms)
  | emptyE => exact sound_emptyE h
  | totUp i => exact sound_totUp h ht
  | totDown i => exact sound_totDown h ht
  | shareCl eT dT => exact sound_shareCl h ht ax.window_sel
  | shareCap i => exact sound_shareCap h ht ax.share_le

theorem sound_allS {cap : Nat} : ∀ {tags : List TagS} {raw : List (List Nat)},
    ckAllS M X Mr cs tots w cap tags raw = true →
    cs.all (ctrOK M cens) = true → tots.all (totOK M X w cens) = true →
    AxiomsS S E w cens Mr cap →
    ∀ cl ∈ raw, clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true
  | [], [], _, _, _, _ => by simp
  | t :: ts, cl :: cls, h, hcs, ht, ax => by
    simp only [ckAllS, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact sound_clauseS h.1 hcs ht ax
    · exact sound_allS h.2 hcs ht ax x hx
  | [], _ :: _, h, _, _, _ => by simp [ckAllS] at h
  | _ :: _, [], h, _, _, _ => by simp [ckAllS] at h

end Families

/-- Main soundness theorem for share certificates: a checked certificate yields a
satisfying assignment of the core from any `S`, `E` satisfying the share axioms. -/
theorem soundS (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (b : List (Nat × Nat)) (cap : Nat) (tags : List TagS) (raw : List (List Nat))
    (h : checkAllS M X Mr cs tots w b cap tags raw = true) (S E : Nat → Bool)
    (ax : AxiomsS S E w (centresOf w b) Mr cap) :
    cnfTrue (tauS S E M X Mr cs tots) (raw.map (·.map decodeLit)) = true := by
  have hk : ctrOKK M (centresK w b) = ctrOK M (centresK w b) := funext (ctrOKK_eq M _)
  simp only [checkAllS, Bool.and_eq_true, allK_eq, hk] at h
  rw [centresK_eq] at ax
  unfold cnfTrue
  rw [List.all_map, List.all_eq_true]
  intro cl hcl
  exact sound_allS h.2 h.1.1 h.1.2 ax cl hcl



/-! ## Checking in parts -/

/-- Two consecutive parts of the clauses, checked separately. -/
theorem ckAllS_append (M : Nat → MT) (X : Nat → MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot)
    (w : List Nat) (cap : Nat) :
    ∀ (t₁ : List TagS) (r₁ : List (List Nat)) (t₂ : List TagS) (r₂ : List (List Nat)),
      ckAllS M X Mr cs tots w cap t₁ r₁ = true → ckAllS M X Mr cs tots w cap t₂ r₂ = true →
      ckAllS M X Mr cs tots w cap (t₁ ++ t₂) (r₁ ++ r₂) = true
  | [], [], _, _, _, h₂ => h₂
  | t :: ts, cl :: cls, t₂, r₂, h₁, h₂ => by
    simp only [ckAllS, Bool.and_eq_true, List.cons_append] at h₁ ⊢
    exact ⟨h₁.1, ckAllS_append M X Mr cs tots w cap ts cls t₂ r₂ h₁.2 h₂⟩
  | [], _ :: _, _, _, h₁, _ => by simp [ckAllS] at h₁
  | _ :: _, [], _, _, h₁, _ => by simp [ckAllS] at h₁

/-- `checkAllS` from the counters, the totalizers and the clauses, checked separately. -/
theorem checkAllS_of_parts {M : Nat → MT} {X : Nat → MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
    {w : List Nat} {b : List (Nat × Nat)} {cap : Nat} {tags : List TagS} {raw : List (List Nat)}
    (hc : allK (ctrOKK M (centresK w b)) cs = true) (ht : tots.all (totOK M X w (centresK w b)) = true)
    (ha : ckAllS M X Mr cs tots w cap tags raw = true) : checkAllS M X Mr cs tots w b cap tags raw = true := by
  simp only [checkAllS, Bool.and_eq_true]
  exact ⟨⟨hc, ht⟩, ha⟩

end

/-! ## Flat share meaning tables -/

section Decode

noncomputable section

local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- The share meaning of a field code: kind in 2 bits (`0` `.z`, `1` `.sq q a b`, `2` `.t i lo hi c`,
`3` `.u q t`), then the fields in `qw`, `aw` (`a`, `b`, `t`), `iw`, `hw` (`lo`, `hi`) bits and `c`. -/
def leafSF (qw aw iw hw : Nat) (x : Nat) : MS :=
  kif Nat.beq (Nat.land x 3) 0 then MS.z else
  kif Nat.beq (Nat.land x 3) 1 then
    withLit (Nat.land (Nat.shiftRight x 2) (Nat.sub (Nat.shiftLeft 1 qw) 1)) fun q =>
    withLit (Nat.land (Nat.shiftRight x (Nat.add 2 qw)) (Nat.sub (Nat.shiftLeft 1 aw) 1)) fun a =>
    withLit (Nat.shiftRight x (Nat.add (Nat.add 2 qw) aw)) fun b => MS.sq q a b else
  kif Nat.beq (Nat.land x 3) 3 then
    withLit (Nat.land (Nat.shiftRight x 2) (Nat.sub (Nat.shiftLeft 1 qw) 1)) fun q =>
    withLit (Nat.shiftRight x (Nat.add 2 qw)) fun t => MS.u q t else
    withLit (Nat.land (Nat.shiftRight x 2) (Nat.sub (Nat.shiftLeft 1 iw) 1)) fun i =>
    withLit (Nat.land (Nat.shiftRight x (Nat.add 2 iw)) (Nat.sub (Nat.shiftLeft 1 hw) 1)) fun lo =>
    withLit (Nat.land (Nat.shiftRight x (Nat.add (Nat.add 2 iw) hw)) (Nat.sub (Nat.shiftLeft 1 hw) 1)) fun hi =>
    withLit (Nat.shiftRight x (Nat.add (Nat.add (Nat.add 2 iw) hw) hw)) fun c => MS.t i lo hi c

/-- Entry `x` of the share table `T` of `W`-bit fields. -/
def getSF (T W qw aw iw hw : Nat) (x : Nat) : MS :=
  leafSF qw aw iw hw (Nat.land (Nat.shiftRight T (Nat.mul x W)) (Nat.sub (Nat.shiftLeft 1 W) 1))

end

end Decode

end Snake9.LocalWindow.TagsSW
