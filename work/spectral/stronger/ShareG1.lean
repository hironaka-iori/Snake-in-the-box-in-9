import Sh235Win
import ShareBonus
/-!
# G1 for the share CNFs (bound 234): empty squares, share indicators, totalizer

A *share CNF* (`milestones/10-window-aggregate/scripts/share_enc.py`, `ShareEncoding`, counter
`stot`) is the wincert window CNF of a direction shape with no count constraint (ball, endpoint and
cycle-cut clauses, checked by `W223G1.check`, all variables below `VS`), plus

* `E ↔ Q empty` for a square `Q` (vertex list `sq`), `g ↔ E ∧ #selected(pv) ≤ t` (`pv` the free
  corners of the parallel square `P`), as in `Info.e` / `Info.g`;
* per share term (centre, direction `k`, pair `{a, b}`) the unary vector of bits `[E, E, g1, g3, g3, g3]`
  (or a prefix of it);
* a totalizer: each node merges two children whose term ranges `[lo, mid)` and `[mid, hi)` are
  consecutive; output `j` of a node means "the term values of `[lo, hi)` sum to at least `j`";
* unit clauses `¬ o_j` (`j > B`) on nodes whose range starts at term `0` (the bound `Σ ≤ B`).

The value of a term is the largest index of a true bit (`topv`), so a true bit at index `i`
gives value `≥ i` without any monotonicity of the bits.  `tauS` is the intended assignment;
`sound4`: every clause accepted by `check4` holds under `tauS` for a selection satisfying `Hyp`
whose term values sum to at most `B` over `[0, NT)`.  `termsOK` relates each term to
`SquareIncidence.shareTerm` at its centre (`tval_le_shareTerm`), and `shareRef_of` turns a refuted
share CNF into a lower bound on `ShareBonus.windowShareK` for every snake through the window.
None of the tables needs to be trusted.
-/
namespace SH234
open Snake9 Snake9.SquareIncidence WinCNF W223G1 WinG1 S235

/-! ### Packed tables

Every table is one natural number of fixed-width fields; `fld X w i` is field `i` (kernel big-number
shifts, so a lookup costs a few GMP operations). -/

def fld (X w i : Nat) : Nat := (X >>> (w * i)) % 2 ^ w

/-- A binary tree read by index: `0` is the root, odd `n` goes left (`n / 2`), even `n > 0`
goes right (`n / 2 - 1`). -/
inductive BT where
  | nil : BT
  | node : BT → Nat → BT → BT

def BT.get : BT → Nat → Nat
  | .nil, _ => 0
  | .node l x r, n => if n = 0 then x else if n % 2 = 1 then l.get (n / 2) else r.get (n / 2 - 1)

/-- Field `i` of a table cut into chunks of 64 fields (small numbers keep the kernel's caches small). -/
def tget (X : BT) (w i : Nat) : Nat := fld (X.get (i / 64)) w (i % 64)

def allLt : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allLt n p && p n

theorem allLt_spec : ∀ (n : Nat) (p : Nat → Bool), allLt n p = true → ∀ i < n, p i = true
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, p, h, i, hi => by
    simp only [allLt, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact allLt_spec n p h.1 i hi
    · exact h.2

/-- `p lo, …, p (lo + n - 1)`; a universally quantified table fact is checked in chunks, one
kernel evaluation per chunk (`chunk_step`, `chunk_end`), which keeps the kernel's caches small. -/
def allFrom (p : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | lo, n + 1 => p lo && allFrom p (lo + 1) n

theorem allFrom_spec (p : Nat → Bool) : ∀ (lo n : Nat), allFrom p lo n = true → ∀ i, lo ≤ i → i < lo + n → p i = true
  | _, 0, _, i, h1, h2 => absurd h2 (by omega)
  | lo, n + 1, h, i, h1, h2 => by
    simp only [allFrom, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge lo i with hl | hl
    · exact allFrom_spec p (lo + 1) n h.2 i hl (by omega)
    · rw [show i = lo by omega]; exact h.1

theorem chunk_step {p : Nat → Bool} {n lo k : Nat} (h : allFrom p lo k = true)
    (t : ∀ i, lo + k ≤ i → i < n → p i = true) : ∀ i, lo ≤ i → i < n → p i = true := by
  intro i h1 h2
  rcases Nat.lt_or_ge i (lo + k) with hl | hl
  · exact allFrom_spec p lo k h i h1 hl
  · exact t i hl h2

theorem chunk_end {p : Nat → Bool} {n lo : Nat} (h : n ≤ lo) : ∀ i, lo ≤ i → i < n → p i = true :=
  fun _ h1 h2 => absurd h2 (by omega)

/-! ### Data -/

inductive Info where
  | none : Info
  | e (sq : List Nat) : Info
  | g (e : Nat) (pv : List Nat) (t : Nat) : Info
  | o (n : Nat) (j : Nat) : Info

instance : Inhabited Info := ⟨.none⟩

structure Node where
  lo : Nat
  mid : Nat
  hi : Nat
  lb : List Lit
  rb : List Lit

instance : Inhabited Node := ⟨⟨0, 0, 0, [], []⟩⟩

structure Term where
  cen : Nat
  k : Nat
  a : Nat
  b : Nat
  e : Nat
  bits : List Lit

instance : Inhabited Term := ⟨⟨0, 0, 0, 0, 0, []⟩⟩

/-- The data of a share CNF: G1 tables of the window CNF, the share variables `VS ≤ v < VE`
(table `I`, 64-bit fields), `NN` totalizer nodes (table `ND`, 64-bit fields), `NT` terms (table `TD`,
192-bit fields) and the bound `B`. -/
structure SD where
  T : Tables
  VS : Nat
  VE : Nat
  I : BT
  NN : Nat
  ND : BT
  NT : Nat
  TD : BT
  B : Nat

/-- Field layout of a share variable: tag `1` = `E` (four 9-bit vertices from bit 2), `2` = `g`
(`e` 16 bits from bit 2, `t` 2 bits at 18, number of corners 2 bits at 20, 9-bit corners from 22),
`3` = totalizer output (node 16 bits from bit 2, index 8 bits at 18). -/
def decInfo (x : Nat) : Info :=
  if x % 4 = 1 then .e [(x >>> 2) % 512, (x >>> 11) % 512, (x >>> 20) % 512, (x >>> 29) % 512]
  else if x % 4 = 2 then
    .g ((x >>> 2) % 65536) ((List.range ((x >>> 20) % 4)).map fun i => (x >>> (22 + 9 * i)) % 512)
      ((x >>> 18) % 4)
  else if x % 4 = 3 then .o ((x >>> 2) % 65536) ((x >>> 18) % 256)
  else .none

def infoOf (D : SD) (v : Nat) : Info :=
  if D.VS ≤ v ∧ v < D.VE then decInfo (tget D.I 64 (v - D.VS)) else .none

/-- Term layout: centre 3 bits, `k`, `a`, `b` 4 bits each, `E` variable 16 bits at 15, number of
bits 3 bits at 31, then the bit variables, 16 bits each from bit 34. -/
def termOf (D : SD) (t : Nat) : Term :=
  let x := tget D.TD 192 t
  ⟨x % 8, (x >>> 3) % 16, (x >>> 7) % 16, (x >>> 11) % 16, (x >>> 15) % 65536,
    (List.range ((x >>> 31) % 8)).map fun i => Int.ofNat ((x >>> (34 + 16 * i)) % 65536)⟩

/-- Node layout: `lo`, `mid`, `hi` 11 bits each; bit 33 (34): the left (right) child is a term. -/
def nodeOf (D : SD) (n : Nat) : Node :=
  let x := tget D.ND 64 n
  let lo := x % 2048
  let mid := (x >>> 11) % 2048
  ⟨lo, mid, (x >>> 22) % 2048, if (x >>> 33) % 2 = 1 then (termOf D lo).bits else [],
    if (x >>> 34) % 2 = 1 then (termOf D mid).bits else []⟩

/-! ### The intended assignment -/

def cntS (S : Nat → Bool) (l : List Nat) : Nat := (l.filter S).length

def eVal (D : SD) (S : Nat → Bool) (e : Nat) : Bool :=
  match infoOf D e with
  | .e sq => sq.all (fun w => !S w)
  | _ => false

def egVal (D : SD) (S : Nat → Bool) (v : Nat) : Bool :=
  match infoOf D v with
  | .e sq => sq.all (fun w => !S w)
  | .g e pv t => eVal D S e && decide (cntS S pv ≤ t)
  | _ => false

/-- Base and share-indicator variables. -/
def tau1 (D : SD) (S : Nat → Bool) (v : Nat) : Bool := if v < D.VS then tau D.T S v else egVal D S v

/-- Largest `i + 1` (counted from `i0`) with a true literal at position `i`. -/
def topv (τ : Nat → Bool) : Nat → List Lit → Nat
  | _, [] => 0
  | i, x :: xs => max (if litSat τ x then i + 1 else 0) (topv τ (i + 1) xs)

def tval (D : SD) (S : Nat → Bool) (t : Nat) : Nat := topv (tau1 D S) 0 (termOf D t).bits

open Classical in
noncomputable def rsum (D : SD) (S : Nat → Bool) (lo hi : Nat) : Nat :=
  ∑ t ∈ Finset.Ico lo hi, tval D S t

open Classical in
noncomputable def tauS (D : SD) (S : Nat → Bool) (v : Nat) : Bool :=
  if v < D.VS then tau D.T S v else
    match infoOf D v with
    | .o n j => decide (j ≤ rsum D S (nodeOf D n).lo (nodeOf D n).hi)
    | _ => egVal D S v

/-! ### The checker -/

def isE (D : SD) (e : Nat) : Bool := match infoOf D e with | .e _ => true | _ => false

def ruleE1 (D : SD) : Clause → Bool
  | [.negSucc e, x] => match infoOf D (e + 1) with
    | .e sq => negBall D.T x && sq.contains (litV D.T x)
    | _ => false
  | _ => false

def ruleE2 (D : SD) : Clause → Bool
  | .ofNat e :: rest => match infoOf D e with
    | .e sq => rest.all (posBall D.T) && rest.map (litV D.T) == sq
    | _ => false
  | _ => false

def ruleG1 (D : SD) : Clause → Bool
  | [.negSucc g, .ofNat e] => match infoOf D (g + 1) with
    | .g e' _ _ => e == e'
    | _ => false
  | _ => false

def ruleG2 (D : SD) : Clause → Bool
  | .negSucc v :: rest => match infoOf D (v + 1) with
     | .g _ pv t => rest.all (negBall D.T) && (rest.map (litV D.T)).isSublist pv && rest.length == t + 1
     | _ => false
  | _ => false

def ruleG3 (D : SD) : Clause → Bool
  | .negSucc v :: rest => isE D (v + 1) && match rest.getLast? with
     | some (.ofNat g) => match infoOf D g with
       | .g e pv t => e == v + 1 && rest.dropLast.all (posBall D.T) &&
           (rest.dropLast.map (litV D.T)).isSublist pv && decide (pv.length ≤ rest.dropLast.length + t)
       | _ => false
     | _ => false
  | _ => false

def ruleE (D : SD) (c : Clause) : Bool := ruleE1 D c || ruleE2 D c
def ruleG (D : SD) (c : Clause) : Bool := ruleG1 D c || ruleG2 D c || ruleG3 D c

def lastIdx (x : Lit) : Nat → List Lit → Nat
  | _, [] => 0
  | i, y :: ys => max (if y == x then i + 1 else 0) (lastIdx x (i + 1) ys)

/-- Reading of the negated literal `x` of an up clause as "child range sums to at least `i`":
the child is a node with range `[lo, hi)` or (bits `lb ≠ []`) the single term `lo`. -/
def readC (D : SD) (lo hi : Nat) (lb : List Lit) : Lit → Option Nat
  | .negSucc v => match infoOf D (v + 1) with
    | .o n' i => if decide (n' < D.NN) && (nodeOf D n').lo == lo && (nodeOf D n').hi == hi then some i
        else none
    | _ => if lb.isEmpty then none else some (lastIdx (.ofNat (v + 1)) 0 lb)
  | _ => none

def ruleT (D : SD) : Clause → Bool
  | [x, y, .ofNat o] => match infoOf D o with
    | .o n j => decide (n < D.NN) &&
        let N := nodeOf D n
        match readC D N.lo N.mid N.lb x, readC D N.mid N.hi N.rb y with
        | some i, some i' => decide (j ≤ i + i')
        | _, _ => false
    | _ => false
  | [x, .ofNat o] => match infoOf D o with
    | .o n j => decide (n < D.NN) &&
        let N := nodeOf D n
        (match readC D N.lo N.mid N.lb x with
         | some i => decide (j ≤ i)
         | none => false) ||
        (match readC D N.mid N.hi N.rb x with
         | some i => decide (j ≤ i)
         | none => false)
    | _ => false
  | [.negSucc o] => match infoOf D (o + 1) with
    | .o n j => decide (n < D.NN) && decide (D.B < j) && (nodeOf D n).lo == 0 &&
        decide ((nodeOf D n).hi ≤ D.NT)
    | _ => false
  | _ => false

def check4 (D : SD) (c : Clause) : Bool :=
  (c.all (fun l => decide (l.natAbs < D.VS)) && check D.T c) || ruleE D c || ruleG D c || ruleT D c

def nodeOK (D : SD) (n : Nat) : Bool :=
  let N := nodeOf D n
  decide (N.lo ≤ N.mid) && decide (N.mid ≤ N.hi) &&
    (N.lb.isEmpty || (N.mid == N.lo + 1 && N.lb == (termOf D N.lo).bits)) &&
    (N.rb.isEmpty || (N.hi == N.mid + 1 && N.rb == (termOf D N.mid).bits))

def NodesOK (D : SD) : Prop := ∀ n < D.NN, nodeOK D n = true

/-- Side conditions on the variable ranges. -/
def sdOK (D : SD) : Bool := decide (nBase D.T < D.VS) && decide (D.T.nb < D.VS)

/-! ### Soundness of the checker -/

section
variable {D : SD} {S : Nat → Bool}

theorem infoOf_lt {v : Nat} (h : v < D.VS) : infoOf D v = .none := by
  unfold infoOf; rw [if_neg (by omega)]

theorem tauS_lt {v : Nat} (h : v < D.VS) : tauS D S v = tau D.T S v := by
  unfold tauS; rw [if_pos h]

theorem tauS_eg {v : Nat} (hv : D.VS ≤ v) (h : ∀ n j, infoOf D v ≠ .o n j) :
    tauS D S v = egVal D S v := by
  unfold tauS; rw [if_neg (by omega)]
  split
  · rename_i n j hn; exact absurd hn (h n j)
  · rfl

theorem tauS_o {v n j : Nat} (h : infoOf D v = .o n j) :
    tauS D S v = decide (j ≤ rsum D S (nodeOf D n).lo (nodeOf D n).hi) := by
  have hv : D.VS ≤ v := by
    by_contra hc; rw [infoOf_lt (by omega)] at h; exact absurd h (by simp)
  unfold tauS; rw [if_neg (by omega), h]

theorem tauS_not_o {v : Nat} (h : ∀ n j, infoOf D v ≠ .o n j) : tauS D S v = tau1 D S v := by
  unfold tau1
  by_cases hv : v < D.VS
  · rw [if_pos hv, tauS_lt hv]
  · rw [if_neg hv, tauS_eg (by omega) h]

theorem tauS_e {v : Nat} {sq : List Nat} (h : infoOf D v = .e sq) :
    tauS D S v = sq.all (fun w => !S w) := by
  rw [tauS_not_o (by intro n j hc; rw [h] at hc; exact absurd hc (by simp))]
  have hv : ¬ v < D.VS := by
    intro hc; rw [infoOf_lt hc] at h; exact absurd h (by simp)
  unfold tau1 egVal; rw [if_neg hv, h]

theorem tauS_g {v e t : Nat} {pv : List Nat} (h : infoOf D v = .g e pv t) :
    tauS D S v = (eVal D S e && decide (cntS S pv ≤ t)) := by
  rw [tauS_not_o (by intro n j hc; rw [h] at hc; exact absurd hc (by simp))]
  have hv : ¬ v < D.VS := by
    intro hc; rw [infoOf_lt hc] at h; exact absurd h (by simp)
  unfold tau1 egVal; rw [if_neg hv, h]

theorem eVal_of {e : Nat} {sq : List Nat} (h : infoOf D e = .e sq) :
    eVal D S e = sq.all (fun w => !S w) := by
  unfold eVal; rw [h]

theorem isE_spec {e : Nat} (h : isE D e = true) : ∃ sq, infoOf D e = .e sq := by
  unfold isE at h
  split at h
  · rename_i sq hs; exact ⟨sq, hs⟩
  · exact absurd h (by simp)

theorem eVal_tauS {e : Nat} (h : isE D e = true) : eVal D S e = tauS D S e := by
  obtain ⟨sq, hs⟩ := isE_spec h
  rw [eVal_of hs, tauS_e hs]

theorem tauS_ball (hD : sdOK D = true) {v : Nat} (h : isBall D.T v = true) : tauS D S v = S (bv D.T v) := by
  simp only [sdOK, Bool.and_eq_true, decide_eq_true_eq] at hD
  simp only [isBall, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [tauS_lt (by omega), tau_ball (by simp [isBall]; omega)]

theorem litSat_negBallS (hD : sdOK D = true) {l : Lit} (h : negBall D.T l = true) :
    litSat (tauS D S) l = !S (litV D.T l) := by
  match l, h with
  | .negSucc n, h =>
    simp only [negBall] at h
    show (!tauS D S (n + 1)) = _
    rw [tauS_ball hD h]; rfl

theorem litSat_posBallS (hD : sdOK D = true) {l : Lit} (h : posBall D.T l = true) :
    litSat (tauS D S) l = S (litV D.T l) := by
  match l, h with
  | .ofNat v, h =>
    simp only [posBall] at h
    show tauS D S v = _
    rw [tauS_ball hD h]; rfl

theorem cntS_le_length (S : Nat → Bool) (l : List Nat) : cntS S l ≤ l.length :=
  List.length_filter_le _ _

theorem cntS_sublist {S : Nat → Bool} {l₁ l₂ : List Nat} (h : l₁.Sublist l₂) :
    cntS S l₁ ≤ cntS S l₂ := (h.filter S).length_le

theorem cntS_compl (S : Nat → Bool) (l : List Nat) :
    cntS S l + (l.filter (fun w => !S w)).length = l.length := by
  unfold cntS
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.length_cons]
    cases S x <;> simp <;> omega

/-! #### Rules E and G -/

theorem ruleE1_sound (hD : sdOK D = true) {c : Clause} (h : ruleE1 D c = true) :
    clauseSat (tauS D S) c := by
  unfold clauseSat
  match c, h with
  | [.negSucc e, x], h =>
    simp only [ruleE1] at h
    split at h
    · rename_i sq hs
      simp only [Bool.and_eq_true] at h
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [litSat_negBallS hD h.1]
      show ((!tauS D S (e + 1)) || _) = true
      rw [tauS_e hs]
      have hm := List.contains_iff_mem.mp h.2
      cases hx : S (litV D.T x)
      · simp
      · have : sq.all (fun w => !S w) = false := by
          rw [List.all_eq_false]; exact ⟨_, hm, by simp [hx]⟩
        simp [this]
    · exact absurd h (by simp)
  | [], h => simp [ruleE1] at h
  | [_], h => simp [ruleE1] at h
  | [.ofNat _, _], h => simp [ruleE1] at h
  | _ :: _ :: _ :: _, h => simp [ruleE1] at h

theorem ruleE2_sound (hD : sdOK D = true) {c : Clause} (h : ruleE2 D c = true) :
    clauseSat (tauS D S) c := by
  unfold clauseSat
  match c, h with
  | .ofNat e :: rest, h =>
    simp only [ruleE2] at h
    split at h
    · rename_i sq hs
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      simp only [List.any_cons]
      show (tauS D S e || _) = true
      rw [tauS_e hs]
      cases ha : sq.all (fun w => !S w)
      · simp only [Bool.false_or]
        rw [List.all_eq_false] at ha
        obtain ⟨w, hw, hsw⟩ := ha
        rw [← h2] at hw
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hw
        apply List.any_eq_true.mpr
        refine ⟨l, hl, ?_⟩
        rw [litSat_posBallS hD (List.all_eq_true.mp h1 l hl)]
        simpa using hsw
      · rfl
    · exact absurd h (by simp)
  | [], h => simp [ruleE2] at h
  | .negSucc _ :: _, h => simp [ruleE2] at h

theorem ruleG1_sound {c : Clause} (h : ruleG1 D c = true) : clauseSat (tauS D S) c := by
  unfold clauseSat
  match c, h with
  | [.negSucc g, .ofNat e], h =>
    simp only [ruleG1] at h
    split at h
    · rename_i e' pv t hg
      have he : e = e' := by simpa using h
      subst he
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      show ((!tauS D S (g + 1)) || tauS D S e) = true
      rw [tauS_g hg]
      cases he : eVal D S e
      · simp
      · unfold eVal at he
        split at he
        · rename_i sq hs
          rw [tauS_e hs, he]; simp
        · exact absurd he (by simp)
    · exact absurd h (by simp)
  | [], h => simp [ruleG1] at h
  | [_], h => simp [ruleG1] at h
  | [.ofNat _, _], h => simp [ruleG1] at h
  | [.negSucc _, .negSucc _], h => simp [ruleG1] at h
  | _ :: _ :: _ :: _, h => simp [ruleG1] at h

theorem ruleG2_sound (hD : sdOK D = true) {c : Clause} (h : ruleG2 D c = true) :
    clauseSat (tauS D S) c := by
  unfold clauseSat
  match c, h with
  | .negSucc v :: rest, h =>
    simp only [ruleG2] at h
    split at h
    · rename_i e pv t hg
      simp only [Bool.and_eq_true, beq_iff_eq, List.isSublist_iff_sublist] at h
      obtain ⟨⟨hn, hsub⟩, hlen⟩ := h
      simp only [List.any_cons]
      show ((!tauS D S (v + 1)) || _) = true
      rw [tauS_g hg]
      cases hg' : (eVal D S e && decide (cntS S pv ≤ t))
      · rfl
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
        simp only [Bool.not_true, Bool.false_or]
        by_contra hc
        simp only [Bool.not_eq_true, List.any_eq_false] at hc
        have hall : ∀ w ∈ rest.map (litV D.T), S w = true := by
          intro w hw
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hw
          have := hc l hl
          rw [litSat_negBallS hD (List.all_eq_true.mp hn l hl)] at this
          simpa using this
        have h3 : cntS S (rest.map (litV D.T)) = rest.length := by
          unfold cntS; rw [List.filter_eq_self.mpr hall, List.length_map]
        have := cntS_sublist (S := S) hsub
        omega
    · exact absurd h (by simp)
  | [], h => simp [ruleG2] at h
  | .ofNat _ :: _, h => simp [ruleG2] at h

theorem ruleG3_sound (hD : sdOK D = true) {c : Clause} (h : ruleG3 D c = true) :
    clauseSat (tauS D S) c := by
  unfold clauseSat
  match c, h with
  | .negSucc v :: rest, h =>
    simp only [ruleG3, Bool.and_eq_true] at h
    obtain ⟨hE, h1⟩ := h
    split at h1
    · rename_i g hl
      split at h1
      · rename_i e pv t hg
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isSublist_iff_sublist] at h1
        obtain ⟨⟨⟨rfl, hp⟩, hsub⟩, hlen⟩ := h1
        have hrest : rest = rest.dropLast ++ [.ofNat g] := (List.dropLast_append_getLast? _ hl).symm
        simp only [List.any_cons]
        show ((!tauS D S (v + 1)) || _) = true
        rw [← eVal_tauS hE]
        cases hev : eVal D S (v + 1)
        · rfl
        · simp only [Bool.not_true, Bool.false_or]
          rw [hrest, List.any_append]
          cases hx : (rest.dropLast).any (litSat (tauS D S))
          · simp only [Bool.false_or, List.any_cons, List.any_nil, Bool.or_false]
            show tauS D S g = true
            rw [tauS_g hg, hev, Bool.true_and, decide_eq_true_eq]
            simp only [List.any_eq_false] at hx
            have hall : ∀ w ∈ rest.dropLast.map (litV D.T), S w = false := by
              intro w hw
              obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hw
              have := hx l hl
              rw [litSat_posBallS hD (List.all_eq_true.mp hp l hl)] at this
              simpa using this
            have h3 : ((rest.dropLast.map (litV D.T)).filter (fun w => !S w)).length =
                rest.dropLast.length := by
              rw [List.filter_eq_self.mpr (by intro w hw; simp [hall w hw]), List.length_map]
            have h4 := (hsub.filter (fun w => !S w)).length_le
            have h5 := cntS_compl S pv
            omega
          · rfl
      · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
  | [], h => simp [ruleG3] at h
  | .ofNat _ :: _, h => simp [ruleG3] at h

theorem ruleE_sound (hD : sdOK D = true) {c : Clause} (h : ruleE D c = true) :
    clauseSat (tauS D S) c := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact ruleE1_sound hD h
  · exact ruleE2_sound hD h

theorem ruleG_sound (hD : sdOK D = true) {c : Clause} (h : ruleG D c = true) :
    clauseSat (tauS D S) c := by
  unfold ruleG at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact ruleG1_sound h
  · exact ruleG2_sound hD h
  · exact ruleG3_sound hD h

/-! #### Totalizer rules -/

theorem topv_ge (τ : Nat → Bool) : ∀ (i0 : Nat) (l : List Lit) (i : Nat), i < l.length →
    litSat τ (l.getD i 0) = true → i0 + i + 1 ≤ topv τ i0 l
  | _, [], _, h, _ => absurd h (by simp)
  | i0, x :: xs, 0, _, h => by
    simp only [List.getD_cons_zero] at h
    simp only [topv, h, if_true]; omega
  | i0, x :: xs, i + 1, hi, h => by
    simp only [List.getD_cons_succ] at h
    have := topv_ge τ (i0 + 1) xs i (by simp at hi; omega) h
    simp only [topv]; omega

theorem topv_le (τ : Nat → Bool) (B : Nat) : ∀ (i0 : Nat) (l : List Lit),
    (∀ i < l.length, litSat τ (l.getD i 0) = true → i0 + i + 1 ≤ B) → topv τ i0 l ≤ B
  | _, [], _ => by simp [topv]
  | i0, x :: xs, h => by
    have h0 := h 0 (by simp)
    have ht := topv_le τ B (i0 + 1) xs (fun i hi hs => by
      have := h (i + 1) (by simp; omega) (by simpa using hs); omega)
    simp only [List.getD_cons_zero] at h0
    simp only [topv]
    apply max_le _ ht
    split
    · rename_i hx; have := h0 hx; omega
    · omega

theorem lastIdx_spec (x : Lit) : ∀ (i0 : Nat) (l : List Lit), lastIdx x i0 l = 0 ∨
    ∃ i < l.length, l.getD i 0 = x ∧ lastIdx x i0 l = i0 + i + 1
  | _, [] => Or.inl rfl
  | i0, y :: ys => by
    simp only [lastIdx]
    rcases lastIdx_spec x (i0 + 1) ys with h | ⟨i, hi, hx, he⟩
    · rw [h]
      by_cases hy : (y == x) = true
      · refine Or.inr ⟨0, by simp, by simpa using hy, by simp [hy]⟩
      · left; simp [hy]
    · right
      by_cases hy : (y == x) = true
      · refine ⟨i + 1, by simp; omega, by simpa using hx, ?_⟩
        rw [he]; simp only [hy, if_true]; omega
      · refine ⟨i + 1, by simp; omega, by simpa using hx, ?_⟩
        rw [he]; simp only [hy]; simp; omega

theorem rsum_single (t : Nat) : rsum D S t (t + 1) = tval D S t := by
  unfold rsum; simp

theorem rsum_split {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    rsum D S lo hi = rsum D S lo mid + rsum D S mid hi := by
  unfold rsum; rw [Finset.sum_Ico_consecutive _ h1 h2]

theorem nodeOK_spec (hN : NodesOK D) {n : Nat} (hn : n < D.NN) :
    (nodeOf D n).lo ≤ (nodeOf D n).mid ∧ (nodeOf D n).mid ≤ (nodeOf D n).hi ∧
    ((nodeOf D n).lb = [] ∨ ((nodeOf D n).mid = (nodeOf D n).lo + 1 ∧
      (nodeOf D n).lb = (termOf D (nodeOf D n).lo).bits)) ∧
    ((nodeOf D n).rb = [] ∨ ((nodeOf D n).hi = (nodeOf D n).mid + 1 ∧
      (nodeOf D n).rb = (termOf D (nodeOf D n).mid).bits)) := by
  have h := hN n hn
  simp only [nodeOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.isEmpty_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A negated child literal that is false under `tauS` (its variable is true) certifies a lower
bound on the child's range sum. -/
theorem readC_sound (hN : NodesOK D) {lo hi : Nat} {lb : List Lit} {x : Lit} {i : Nat}
    (hlb : lb = [] ∨ (hi = lo + 1 ∧ lb = (termOf D lo).bits))
    (h : readC D lo hi lb x = some i) (hx : litSat (tauS D S) x = false) : i ≤ rsum D S lo hi := by
  match x, h with
  | .negSucc v, h =>
    have hv : tauS D S (v + 1) = true := by simpa [litSat] using hx
    simp only [readC] at h
    split at h
    · rename_i n' i' hi'
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h
        subst h
        rw [tauS_o hi', hc.1.2, hc.2] at hv
        simpa using hv
      · exact absurd h (by simp)
    · rename_i hno
      split at h
      · exact absurd h (by simp)
      · rename_i hne
        simp only [Option.some.injEq] at h
        subst h
        rcases hlb with hlb | ⟨rfl, hlb⟩
        · subst hlb; simp at hne
        · rw [rsum_single]
          unfold tval
          rcases lastIdx_spec (.ofNat (v + 1)) 0 lb with h0 | ⟨k, hk, hkx, hke⟩
          · rw [h0]; omega
          · rw [hke, ← hlb]
            have := topv_ge (tau1 D S) 0 lb k hk (by
              rw [hkx]; show tau1 D S (v + 1) = true
              rw [← tauS_not_o (fun n j hc => hno n j hc)]; exact hv)
            omega

theorem ruleT_sound (hN : NodesOK D) (hB : rsum D S 0 D.NT ≤ D.B)
    {c : Clause} (h : ruleT D c = true) : clauseSat (tauS D S) c := by
  unfold clauseSat
  match c, h with
  | [x, y, .ofNat o], h =>
    simp only [ruleT] at h
    split at h
    · rename_i n j ho
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hn, h⟩ := h
      obtain ⟨h1, h2, hl, hr⟩ := nodeOK_spec hN hn
      split at h
      · rename_i i i' hx hy
        simp only [decide_eq_true_eq] at h
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        cases hxs : litSat (tauS D S) x
        · cases hys : litSat (tauS D S) y
          · have e1 := readC_sound hN hl hx hxs
            have e2 := readC_sound hN hr hy hys
            show (false || (false || tauS D S o)) = true
            rw [tauS_o ho, rsum_split h1 h2]
            simp only [Bool.false_or, decide_eq_true_eq]; omega
          · simp
        · simp
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | [x, .ofNat o], h =>
    simp only [ruleT] at h
    split at h
    · rename_i n j ho
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
      obtain ⟨hn, h⟩ := h
      obtain ⟨h1, h2, hl, hr⟩ := nodeOK_spec hN hn
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      cases hxs : litSat (tauS D S) x
      · show (false || tauS D S o) = true
        rw [tauS_o ho, rsum_split h1 h2]
        simp only [Bool.false_or, decide_eq_true_eq]
        rcases h with h | h
        · split at h
          · rename_i i hx
            have := readC_sound hN hl hx hxs
            simp only [decide_eq_true_eq] at h; omega
          · exact absurd h (by simp)
        · split at h
          · rename_i i hx
            have := readC_sound hN hr hx hxs
            simp only [decide_eq_true_eq] at h; omega
          · exact absurd h (by simp)
      · simp
    · exact absurd h (by simp)
  | [.negSucc o], h =>
    simp only [ruleT] at h
    split at h
    · rename_i n j ho
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨⟨hn, hj⟩, hlo⟩, hhi⟩ := h
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      show (!tauS D S (o + 1)) = true
      rw [tauS_o ho, hlo]
      have hle : rsum D S 0 (nodeOf D n).hi ≤ rsum D S 0 D.NT := by
        rw [rsum_split (lo := 0) (mid := (nodeOf D n).hi) (hi := D.NT) (by omega) hhi]; omega
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
    · exact absurd h (by simp)
  | [], h => simp [ruleT] at h
  | [.ofNat _], h => simp [ruleT] at h
  | [_, .negSucc _], h => simp [ruleT] at h
  | [_, _, .negSucc _], h => simp [ruleT] at h
  | _ :: _ :: _ :: _ :: _, h => simp [ruleT] at h

theorem sound4 (hD : sdOK D = true) (hN : NodesOK D) (hS : Hyp D.T S) (hok : blocksOK D.T = true)
    (hB : rsum D S 0 D.NT ≤ D.B) {c : Clause} (h : check4 D c = true) : clauseSat (tauS D S) c := by
  unfold check4 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h with ((⟨hv, hc⟩ | h) | h) | h
  · exact D239.clauseSat_congr (fun l hl => (tauS_lt (hv l hl)).symm) (sound hS hok hc)
  · exact ruleE_sound hD h
  · exact ruleG_sound hD h
  · exact ruleT_sound hN hB h

end

end SH234
