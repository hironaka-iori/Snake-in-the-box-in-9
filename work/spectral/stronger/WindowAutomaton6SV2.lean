import WindowAutomaton6SDefs
import WindowAutomaton7V2

/-!
# Witness-driven shard check of the share-weighted six-centre automaton

The design of `WindowAutomaton7V2` (milestones/25-k7-234/lean/README.md, "Shard v2") for
`check6SAt`.  `check6SAtW T c t0 wt` evaluates, for every transition `(t1, t2, t3, t4, s)` of
one label, ONE disjunct of `check6SAt T c t0`, chosen by a 4-bit code in the literal `wt`
(field `cntIdx6 [t1, t2, t3, t4, s]`, 7,776 fields):

* `0`: the step inequality with the forward share field;
* `2 (w - 2) + 1`, `2 (w - 2) + 2` (w = 2..6): the k6 window of `w + 1` directions ending at the
  new vertex, forward / reversed;
* `11`: the H8 window;
* `12`: the step inequality with the reversed share field.

The share level of `check6SAt` is the maximum of the two fields, so each inequality code
implies the inequality of `check6SAt`.  A wrong code only makes the check fail.  The arithmetic
uses the kernel's GMP primitives and the list recursions of `cntIdx6`/`symIdx` are unfolded; the
potential rows of the source (`rs`, one per declaration) and of the target (`rd`, one per `t1`)
and the forward share row (`sf`, one per `t1`) are `let`-bound.
-/

namespace Snake9.WindowAutomaton

/-- The exclusion bit of the window `ds` with first count `s0`; `i` is the `symIdx` of the
other counts (the body of `forbBit6`). -/
def fb6 (T : Tables6) (ds : List Nat) (s0 i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (T.forb (T.wIdx (shapeCode (canon ds))) s0) i) 1) 1

/-- `cntIdx6 [a, b, c, d] 0`, unfolded. -/
def ix4 (a b c d : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.sub a 1) 6) (Nat.sub b 1)) 6)
    (Nat.sub c 1)) 6) (Nat.sub d 1)

/-- The `bits`-wide field at `cntIdx6 [a, b, c, d]` of the row `r`. -/
def fld4 (bits r a b c d : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.mul bits (ix4 a b c d))) (Nat.sub (Nat.pow 2 bits) 1)

/-- The step inequality, the potential rows `rs` (source) and `rd` (target) and the share
level `sh` given. -/
def ineq6SF (T : Tables6S) (rs rd t1 t2 t3 t4 s sh : Nat) : Bool :=
  Nat.ble (Nat.add T.k6.num (fld4 T.k6.bits rd t2 t3 t4 s))
    (Nat.add (Nat.mul T.k6.den (Nat.add (Nat.mul 120 s) sh)) (fld4 T.k6.bits rs t1 t2 t3 t4))

/-- One transition, selected by `code`. -/
def tr6SF (T : Tables6S) (c : List Nat) (rs rd sf t0 t1 t2 t3 t4 s code : Nat) : Bool :=
  cond (Nat.beq code 0) (ineq6SF T rs rd t1 t2 t3 t4 s (fld4 T.sbits sf t2 t3 t4 s)) (bsel4 code false
    (fb6 T.k6 (c.drop 5) t4 s)
    (fb6 T.k6 (c.drop 5).reverse s t4)
    (fb6 T.k6 (c.drop 4) t3 (Nat.add (Nat.mul t4 7) s))
    (fb6 T.k6 (c.drop 4).reverse s (Nat.add (Nat.mul t4 7) t3))
    (fb6 T.k6 (c.drop 3) t2 (Nat.add (Nat.mul (Nat.add (Nat.mul t3 7) t4) 7) s))
    (fb6 T.k6 (c.drop 3).reverse s (Nat.add (Nat.mul (Nat.add (Nat.mul t4 7) t3) 7) t2))
    (fb6 T.k6 (c.drop 2) t1 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t2 7) t3) 7) t4) 7) s))
    (fb6 T.k6 (c.drop 2).reverse s (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t4 7) t3) 7) t2) 7) t1))
    (fb6 T.k6 (c.drop 1) t0 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t1 7) t2) 7) t3) 7) t4) 7) s))
    (fb6 T.k6 (c.drop 1).reverse s (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t4 7) t3) 7) t2) 7) t1) 7) t0))
    (wforbH8 T c [t0, t1, t2, t3, t4, s])
    (ineq6SF T rs rd t1 t2 t3 t4 s
      (fld4 T.sbits (T.shr (T.sIdx (shapeCode (canon (c.drop 2).reverse))) s) t4 t3 t2 t1))
    false false false)

/-- Field of the transition `(t1, t2, t3, t4, s)`: `cntIdx6 [t1, t2, t3, t4, s] 0`. -/
def ix5 (t1 t2 t3 t4 s : Nat) : Nat :=
  Nat.sub (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul t1 6) t2) 6) t3) 6) t4) 6) s) 1555

/-- The witness-driven form of `check6SAt` (without its `inducedPattern` test): `wt` holds a
4-bit code per transition. -/
def check6SAtW (T : Tables6S) (c : List Nat) (t0 wt : Nat) : Bool :=
  let rs := T.k6.pot (T.k6.pIdx (shapeCode (canon (c.take 7)))) t0
  allSym (fun t1 =>
    let rd := T.k6.pot (T.k6.pIdx (shapeCode (canon (c.drop 1)))) t1
    let sf := T.shr (T.sIdx (shapeCode (canon (c.drop 2)))) t1
    allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
      tr6SF T c rs rd sf t0 t1 t2 t3 t4 s (code4 wt (ix5 t1 t2 t3 t4 s)))))))

/-! ### Soundness -/

theorem fb6_eq (T : Tables6) (ds : List Nat) (s0 : Nat) (rest : List Nat) :
    fb6 T ds s0 (symIdx rest 0) = wforbA6 T ds (s0 :: rest) := by
  unfold fb6 wforbA6 forbBit6
  rw [nat_beq_eq]
  rfl

theorem pot6_eq_fld4 (T : Tables6) (h : List Nat) (a b c d e : Nat) :
    pot6 T h [a, b, c, d, e] = fld4 T.bits (T.pot (T.pIdx (shapeCode (canon h))) a) b c d e := by
  simp only [pot6, potAt6, fld4, ix4, cntIdx4_eq]
  rfl

theorem shareA6_eq_fld4 (T : Tables6S) (ds : List Nat) (a b c d e : Nat) :
    shareA6 T ds [a, b, c, d, e] = fld4 T.sbits (T.shr (T.sIdx (shapeCode (canon ds))) a) b c d e := by
  simp only [shareA6, shareAt6, fld4, ix4, cntIdx4_eq]
  rfl

theorem ineq6SF_sound (T : Tables6S) (c : List Nat) (rs rd t0 t1 t2 t3 t4 s sh : Nat)
    (hrs : rs = T.k6.pot (T.k6.pIdx (shapeCode (canon (c.take 7)))) t0)
    (hrd : rd = T.k6.pot (T.k6.pIdx (shapeCode (canon (c.drop 1)))) t1)
    (hsh : sh ≤ share6 T (c.drop 2) [t1, t2, t3, t4, s])
    (h : ineq6SF T rs rd t1 t2 t3 t4 s sh = true) :
    decide (T.k6.num + pot6 T.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
      T.k6.den * (120 * s + share6 T (c.drop 2) [t1, t2, t3, t4, s]) +
        pot6 T.k6 (c.take 7) [t0, t1, t2, t3, t4]) = true := by
  rw [pot6_eq_fld4, pot6_eq_fld4, ← hrs, ← hrd]
  unfold ineq6SF at h
  rw [nat_ble_eq] at h
  have h' := of_decide_eq_true h
  simp only [Nat.add_eq, Nat.mul_eq] at h'
  have hm := Nat.mul_le_mul_left T.k6.den
    (show 120 * s + sh ≤ 120 * s + share6 T (c.drop 2) [t1, t2, t3, t4, s] by omega)
  apply decide_eq_true
  omega

/-- A selected transition disjunct implies the transition disjunction of `check6SAt`. -/
theorem tr6SF_sound (T : Tables6S) (c : List Nat) (rs rd sf t0 t1 t2 t3 t4 s code : Nat)
    (hrs : rs = T.k6.pot (T.k6.pIdx (shapeCode (canon (c.take 7)))) t0)
    (hrd : rd = T.k6.pot (T.k6.pIdx (shapeCode (canon (c.drop 1)))) t1)
    (hsf : sf = T.shr (T.sIdx (shapeCode (canon (c.drop 2)))) t1)
    (h : tr6SF T c rs rd sf t0 t1 t2 t3 t4 s code = true) :
    (wforb6 T.k6 (c.drop 5) [t4, s] || wforb6 T.k6 (c.drop 4) [t3, t4, s] ||
      wforb6 T.k6 (c.drop 3) [t2, t3, t4, s] || wforb6 T.k6 (c.drop 2) [t1, t2, t3, t4, s] ||
      wforb6 T.k6 (c.drop 1) [t0, t1, t2, t3, t4, s] ||
      wforbH8 T c [t0, t1, t2, t3, t4, s] ||
      decide (T.k6.num + pot6 T.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
        T.k6.den * (120 * s + share6 T (c.drop 2) [t1, t2, t3, t4, s]) +
          pot6 T.k6 (c.take 7) [t0, t1, t2, t3, t4])) = true := by
  unfold tr6SF at h
  cases hb : Nat.beq code 0 <;> rw [hb] at h <;> simp only [cond_true, cond_false] at h
  · rcases bsel4_sound h with ((((h | h) | (h | h)) | ((h | h) | (h | h))) |
      (((h | h) | (h | h)) | ((h | h) | (h | h))))
    · simp at h
    · have h' : wforbA6 T.k6 (c.drop 5) [t4, s] = true := by
        have e := fb6_eq T.k6 (c.drop 5) t4 [s]
        rw [symIdx_eq1] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 5).reverse [t4, s].reverse = true := by
        have e := fb6_eq T.k6 (c.drop 5).reverse s [t4]
        rw [symIdx_eq1] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 4) [t3, t4, s] = true := by
        have e := fb6_eq T.k6 (c.drop 4) t3 [t4, s]
        rw [symIdx_eq2] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 4).reverse [t3, t4, s].reverse = true := by
        have e := fb6_eq T.k6 (c.drop 4).reverse s [t4, t3]
        rw [symIdx_eq2] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 3) [t2, t3, t4, s] = true := by
        have e := fb6_eq T.k6 (c.drop 3) t2 [t3, t4, s]
        rw [symIdx_eq3] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 3).reverse [t2, t3, t4, s].reverse = true := by
        have e := fb6_eq T.k6 (c.drop 3).reverse s [t4, t3, t2]
        rw [symIdx_eq3] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 2) [t1, t2, t3, t4, s] = true := by
        have e := fb6_eq T.k6 (c.drop 2) t1 [t2, t3, t4, s]
        rw [symIdx_eq4] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 2).reverse [t1, t2, t3, t4, s].reverse = true := by
        have e := fb6_eq T.k6 (c.drop 2).reverse s [t4, t3, t2, t1]
        rw [symIdx_eq4] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 1) [t0, t1, t2, t3, t4, s] = true := by
        have e := fb6_eq T.k6 (c.drop 1) t0 [t1, t2, t3, t4, s]
        rw [symIdx_eq5] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · have h' : wforbA6 T.k6 (c.drop 1).reverse [t0, t1, t2, t3, t4, s].reverse = true := by
        have e := fb6_eq T.k6 (c.drop 1).reverse s [t4, t3, t2, t1, t0]
        rw [symIdx_eq5] at e
        rw [e] at h
        exact h
      simp only [Bool.or_eq_true, wforb6, h', true_or, or_true]
    · simp only [Bool.or_eq_true, h, true_or, or_true]
    · have e : fld4 T.sbits (T.shr (T.sIdx (shapeCode (canon (c.drop 2).reverse))) s) t4 t3 t2 t1 =
          shareA6 T (c.drop 2).reverse [t1, t2, t3, t4, s].reverse := by
        rw [show [t1, t2, t3, t4, s].reverse = [s, t4, t3, t2, t1] from rfl, shareA6_eq_fld4]
      have h' := ineq6SF_sound T c rs rd t0 t1 t2 t3 t4 s _ hrs hrd
        (by rw [e]; exact Nat.le_max_right _ _) h
      simp only [Bool.or_eq_true, h', or_true]
    · simp at h
    · simp at h
    · simp at h
  · have e : fld4 T.sbits sf t2 t3 t4 s = shareA6 T (c.drop 2) [t1, t2, t3, t4, s] := by
      rw [hsf, shareA6_eq_fld4]
    have h' := ineq6SF_sound T c rs rd t0 t1 t2 t3 t4 s _ hrs hrd
      (by rw [e]; exact Nat.le_max_left _ _) h
    simp only [Bool.or_eq_true, h', or_true]

/-- **Bridge** used by the shards: the witness-driven check of one label implies `check6SAt`,
whatever the codes `wt`. -/
theorem check6SAt_of_W (T : Tables6S) (c : List Nat) (t0 wt : Nat)
    (h : check6SAtW T c t0 wt = true) : check6SAt T c t0 = true := by
  unfold check6SAt
  unfold check6SAtW at h
  refine Bool.or_eq_true_iff.2 (Or.inr ?_)
  refine allSym_of_forall _ (fun t1 h1 h1' => allSym_of_forall _ (fun t2 h2 h2' =>
    allSym_of_forall _ (fun t3 h3 h3' => allSym_of_forall _ (fun t4 h4 h4' =>
    allSym_of_forall _ (fun s hs hs' => ?_)))))
  have := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ h
    t1 h1 h1') t2 h2 h2') t3 h3 h3') t4 h4 h4') s hs hs'
  exact tr6SF_sound T c _ _ _ t0 t1 t2 t3 t4 s _ rfl rfl rfl this

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.check6SAt_of_W
