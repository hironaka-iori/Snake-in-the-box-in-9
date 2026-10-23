import D239LexG1
/-!
# G1 for shape CNFs (bound 235): base, cut, lex-leader and totalizer clauses

A *shape CNF* is the wincert window CNF of a direction shape with no count constraint (ball,
endpoint and cycle-cut clauses, checked by `W223G1.check`), lex-leader clauses for the
adjacent transpositions of the free coordinates (`D239.ruleLex`), and one totalizer per centre
over the 21 "absent corner" literals.  A totalizer node `n` (table `Tot`) owns the output
variables `base, …, base + len - 1`, `len = (lits n).length`; output `o_j` (variable
`base + j - 1`) is intended to mean "at least `j` of the leaf literals `lits n` are true".

`tau3` extends `D239.tau2` by these values; `check3` accepts the clauses of `check2` that avoid
the totalizer variables and the four totalizer clause families, read through `wire`:
a clause literal is either an output literal `±o_j` of a node or a leaf literal `l`, which is
the one-leaf "node" `[l]` with `j = 1` (or `[-l]` when the clause needs it negated).

* up (2 literals)   `[¬(X ≥ a), (Y ≥ b)]`   with `X` an affix of `Y` and `b ≤ a`;
* down (2 literals) `[¬(X ≥ a), (Y ≥ b)]`   with `Y` an affix of `X` and `b + |X| - |Y| ≤ a`;
* up (3 literals)   `[¬(X ≥ a), ¬(Y ≥ b), (Z ≥ c)]` with `Z = X ++ Y`, `c ≤ a + b`;
* down (3 literals) `[¬(X ≥ a), (Y ≥ b), (Z ≥ c)]`  with `X = Y ++ Z`, `b + c ≤ a + 1`.

`sound3`: every accepted clause holds under `tau3` for a selection satisfying `Hyp` and the
lex conditions.  Nothing about the tables needs to be trusted.
-/
namespace S235
open WinCNF W223G1 WinG1 D239

structure TotNode where
  base : Nat
  lits : List Lit
deriving Inhabited

/-- Variable `v` is output `o_j` (`1 ≤ j ≤ len`) of node `n` (counting from `n0`). -/
def totDec (v : Nat) : Nat → List TotNode → Option (Nat × Nat)
  | _, [] => none
  | n, t :: ts => if t.base ≤ v ∧ v < t.base + t.lits.length then some (n, v + 1 - t.base)
      else totDec v (n + 1) ts

def nodeL (Tot : List TotNode) (n : Nat) : List Lit := (Tot.getD n default).lits

/-- The data of a shape CNF: G1 tables, lex generators, totalizer nodes; variables below `VT`
are base variables, `VT ≤ v < VL` totalizer outputs, `v ≥ VL` lex auxiliaries. -/
structure Sh where
  T : Tables
  X : List LexT
  Tot : List TotNode
  VT : Nat
  VL : Nat

def inTot (D : Sh) (v : Nat) : Bool := decide (D.VT ≤ v) && decide (v < D.VL)

def tau3 (D : Sh) (S : Nat → Bool) (v : Nat) : Bool :=
  if inTot D v = true then
    match totDec v 0 D.Tot with
    | some (n, j) => decide (j ≤ cnt (baseVal D.T S) (nodeL D.Tot n))
    | none => false
  else tau2 D.T D.X D.VL S v

def posL : Lit → Bool
  | .ofNat _ => true
  | .negSucc _ => false

def isBallLit (T : Tables) (l : Lit) : Bool := negBall T l || posBall T l

/-- Reading of a clause literal as a counting statement `j ≤ cnt L` (`s = true`) or its
negation (`s = false`). -/
def wire (D : Sh) (l : Lit) (s : Bool) : Option (List Lit × Nat) :=
  if inTot D l.natAbs = true then
    match totDec l.natAbs 0 D.Tot with
    | some (n, j) => if posL l == s then some (nodeL D.Tot n, j) else none
    | none => none
  else if isBallLit D.T l then (if s then some ([l], 1) else some ([-l], 1))
  else none

def affix (A N : List Lit) : Bool := A.isPrefixOf N || A.isSuffixOf N

def totRule (D : Sh) : Clause → Bool
  | [x, y] => match wire D x false, wire D y true with
    | some (X, a), some (Y, b) =>
        (affix X Y && decide (b ≤ a)) || (affix Y X && decide (b + (X.length - Y.length) ≤ a))
    | _, _ => false
  | [x, y, z] =>
    (match wire D x false, wire D y false, wire D z true with
     | some (X, a), some (Y, b), some (Z, c) => Z == X ++ Y && decide (c ≤ a + b)
     | _, _, _ => false) ||
    (match wire D x false, wire D y true, wire D z true with
     | some (X, a), some (Y, b), some (Z, c) => X == Y ++ Z && decide (b + c ≤ a + 1)
     | _, _, _ => false)
  | _ => false

def check3 (D : Sh) (c : Clause) : Bool :=
  (c.all (fun l => !inTot D l.natAbs) && check2 D.T D.X D.VL c) || totRule D c

/-- Side conditions on the variable ranges (kernel-decidable). -/
def shOK (D : Sh) : Bool := decide (D.T.nb < D.VT) && decide (D.VT ≤ D.VL)

/-! ### Counting lemmas -/

theorem cnt_append (τ : Nat → Bool) (A B : List Lit) : cnt τ (A ++ B) = cnt τ A + cnt τ B := by
  unfold cnt; rw [List.filter_append, List.length_append]

theorem cnt_le_length (τ : Nat → Bool) (A : List Lit) : cnt τ A ≤ A.length :=
  List.length_filter_le _ _

theorem cnt_affix (τ : Nat → Bool) {A N : List Lit} (h : affix A N = true) :
    cnt τ A ≤ cnt τ N ∧ cnt τ N ≤ cnt τ A + (N.length - A.length) := by
  unfold affix at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · obtain ⟨R, rfl⟩ := List.isPrefixOf_iff_prefix.mp h
    have := cnt_le_length τ R
    rw [cnt_append, List.length_append]; omega
  · obtain ⟨R, rfl⟩ := List.isSuffixOf_iff_suffix.mp h
    have := cnt_le_length τ R
    rw [cnt_append, List.length_append]; omega

theorem cnt_single (τ : Nat → Bool) (l : Lit) :
    cnt τ [l] = if litSat τ l then 1 else 0 := by
  unfold cnt; simp only [List.filter_cons, List.filter_nil]; split <;> rfl

/-! ### Soundness -/

section
variable {D : Sh} {S : Nat → Bool}

theorem tau3_out {v : Nat} (h : inTot D v = false) : tau3 D S v = tau2 D.T D.X D.VL S v := by
  unfold tau3; rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

theorem litSat_tau3_out {l : Lit} (h : inTot D l.natAbs = false) :
    litSat (tau3 D S) l = litSat (tau2 D.T D.X D.VL S) l := by
  match l with
  | .ofNat n => exact tau3_out h
  | .negSucc n =>
    have h' : inTot D (n + 1) = false := h
    show (!tau3 D S (n + 1)) = (!tau2 D.T D.X D.VL S (n + 1)); rw [tau3_out h']

theorem ball_lt (hD : shOK D = true) {v : Nat} (hb : isBall D.T v = true) :
    inTot D v = false ∧ v < D.VL := by
  simp only [shOK, Bool.and_eq_true, decide_eq_true_eq] at hD
  simp only [isBall, Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨?_, by omega⟩
  simp only [inTot, Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega

theorem litSat_ball (hD : shOK D = true) {l : Lit} (h : isBallLit D.T l = true) :
    litSat (tau3 D S) l = litSat (baseVal D.T S) l := by
  unfold isBallLit at h
  match l, h with
  | .ofNat v, h =>
    simp only [negBall, posBall, Bool.false_or] at h
    obtain ⟨h1, h2⟩ := ball_lt hD h
    show tau3 D S v = baseVal D.T S v
    rw [tau3_out h1, tau2_lt h2, tau_ball h]
    simp only [isBall, Bool.and_eq_true, decide_eq_true_eq] at h
    unfold baseVal; rw [if_neg (by omega), if_pos h.2]
  | .negSucc v, h =>
    simp only [negBall, posBall, Bool.or_false] at h
    obtain ⟨h1, h2⟩ := ball_lt hD h
    show (!tau3 D S (v + 1)) = !baseVal D.T S (v + 1)
    rw [tau3_out h1, tau2_lt h2, tau_ball h]
    simp only [isBall, Bool.and_eq_true, decide_eq_true_eq] at h
    unfold baseVal; rw [if_neg (by omega), if_pos h.2]

theorem litSat_neg_ball (l : Lit) (h : isBallLit D.T l = true) (τ : Nat → Bool) :
    litSat τ (-l) = !litSat τ l := by
  apply litSat_negate
  intro h0; subst h0; simp [isBallLit, negBall, posBall, isBall] at h

theorem wire_sound (hD : shOK D = true) {l : Lit} {s : Bool} {L : List Lit} {j : Nat}
    (h : wire D l s = some (L, j)) :
    litSat (tau3 D S) l = (s == decide (j ≤ cnt (baseVal D.T S) L)) := by
  by_cases hin : inTot D l.natAbs = true
  · unfold wire at h
    rw [if_pos hin] at h
    cases hd : totDec l.natAbs 0 D.Tot with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some nj =>
      obtain ⟨n, j'⟩ := nj
      rw [hd] at h
      simp only at h
      split at h
      · rename_i hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hs' := beq_iff_eq.mp hs
        cases l with
        | ofNat v =>
          have hin' : inTot D v = true := hin
          have hd' : totDec v 0 D.Tot = some (n, j') := hd
          simp only [posL] at hs'; subst hs'
          show tau3 D S v = _
          unfold tau3; rw [if_pos hin', hd']; simp
        | negSucc v =>
          have hin' : inTot D (v + 1) = true := hin
          have hd' : totDec (v + 1) 0 D.Tot = some (n, j') := hd
          simp only [posL] at hs'; subst hs'
          show (!tau3 D S (v + 1)) = _
          unfold tau3; rw [if_pos hin', hd']; simp
      · exact absurd h (by simp)
  · unfold wire at h
    rw [if_neg hin] at h
    split at h
    · rename_i hb
      rw [litSat_ball hD hb]
      cases s
      · simp only [Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [cnt_single, litSat_neg_ball l hb]
        cases litSat (baseVal D.T S) l <;> rfl
      · simp only [if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [cnt_single]
        cases litSat (baseVal D.T S) l <;> rfl
    · exact absurd h (by simp)

theorem totRule_sound (hD : shOK D = true) {c : Clause} (h : totRule D c = true) :
    clauseSat (tau3 D S) c := by
  unfold clauseSat
  match c, h with
  | [x, y], h =>
    simp only [totRule] at h
    split at h
    · rename_i X a Y b hx hy
      have ex := wire_sound (S := S) hD hx
      have ey := wire_sound (S := S) hD hy
      simp only [List.any_cons, List.any_nil, Bool.or_false, ex, ey]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      cases hX : decide (a ≤ cnt (baseVal D.T S) X)
      · rfl
      · have hX' := of_decide_eq_true hX
        have : decide (b ≤ cnt (baseVal D.T S) Y) = true := by
          apply decide_eq_true
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have := (cnt_affix (baseVal D.T S) h1).1; omega
          · have := (cnt_affix (baseVal D.T S) h1).2
            have := Nat.sub_le_sub_left (List.length_filter_le (litSat (baseVal D.T S)) Y) X.length
            unfold cnt at *; omega
        simp [this]
    · exact absurd h (by simp)
  | [x, y, z], h =>
    simp only [totRule, Bool.or_eq_true] at h
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    rcases h with h | h
    · split at h
      · rename_i X a Y b Z c hx hy hz
        rw [wire_sound hD hx, wire_sound hD hy, wire_sound hD hz]
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨rfl, h⟩ := h
        rw [cnt_append]
        cases h1 : decide (a ≤ cnt (baseVal D.T S) X) <;>
          cases h2 : decide (b ≤ cnt (baseVal D.T S) Y) <;> simp_all <;> omega
      · exact absurd h (by simp)
    · split at h
      · rename_i X a Y b Z c hx hy hz
        rw [wire_sound hD hx, wire_sound hD hy, wire_sound hD hz]
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨rfl, h⟩ := h
        rw [cnt_append]
        cases h1 : decide (b ≤ cnt (baseVal D.T S) Y) <;>
          cases h2 : decide (c ≤ cnt (baseVal D.T S) Z) <;> simp_all <;> omega
      · exact absurd h (by simp)
  | [], h => simp [totRule] at h
  | [_], h => simp [totRule] at h
  | _ :: _ :: _ :: _ :: _, h => simp [totRule] at h

theorem sound3 (hD : shOK D = true) (hS : Hyp D.T S) (hok : blocksOK D.T = true)
    (hX : ∀ g ∈ D.X, LexOKP S g.pairs) {c : Clause} (h : check3 D c = true) :
    clauseSat (tau3 D S) c := by
  unfold check3 at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    have h2 := sound2 (VB := D.VL) hS hok hX h.2
    obtain ⟨l, hl, hs⟩ := (clauseSat_iff _ c).mp h2
    exact (clauseSat_iff _ c).mpr ⟨l, hl, by rw [litSat_tau3_out (h.1 l hl)]; exact hs⟩
  · exact totRule_sound hD h

end

end S235
