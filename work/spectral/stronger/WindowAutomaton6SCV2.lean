import WindowAutomaton6SCDefs
import WindowAutomaton6SV2

/-!
# Witness-driven shard check with context shares (milestone 35)

`check6SCAtW T c t0 wt` is `check6SAtW` (`WindowAutomaton6SV2`, unchanged) with two more codes of
the 4-bit witness field of each transition `(t1, t2, t3, t4, s)`:

* `13`: the step inequality with the ctx 7 field `ctx7A T (c.drop 1) [t0, t1, t2, t3, t4, s]`;
* `14`: the step inequality with the ctx 8 field `ctx8A T c [t0, t1, t2, t3, t4, s]`;
* `0 … 12`: as in `check6SAtW` (`tr6SF`, on `T.s`).

The two ctx rows depend only on the label `(c, t0)` and are `let`-bound once per label (`r7`,
`r8`), next to the potential row of the source; a field is one shift and one mask (`fld5`).  Every
inequality code implies the inequality of `check6SCAt`, whose share level `S5C` is the maximum of
the share and the ctx levels, so a wrong code can only make a check fail (`check6SCAt_of_W`).
-/

namespace Snake9.WindowAutomaton

/-- `cntIdx6 [a, b, c, d, e] 0`, unfolded. -/
def ix5c (a b c d e : Nat) : Nat := Nat.add (Nat.mul (ix4 a b c d) 6) (Nat.sub e 1)

/-- The `bits`-wide field at `cntIdx6 [a, b, c, d, e]` of the row `r`. -/
def fld5 (bits r a b c d e : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.mul bits (ix5c a b c d e))) (Nat.sub (Nat.pow 2 bits) 1)

theorem ctxAt_eq_fld5 (bits : Nat) (row : Nat → Nat) (t0 a b c d e : Nat) :
    ctxAt bits row [t0, a, b, c, d, e] = fld5 bits (row t0) a b c d e := by
  simp only [ctxAt, fld5, ix5c, ix4, cntIdx6, Nat.zero_mul, Nat.zero_add]
  rfl

/-- One transition, selected by `code`. -/
def tr6SCF (T : Tables6SC) (c : List Nat) (rs rd sf r7 r8 t0 t1 t2 t3 t4 s code : Nat) : Bool :=
  cond (Nat.beq code 13) (ineq6SF T.s rs rd t1 t2 t3 t4 s (fld5 T.cbits r7 t1 t2 t3 t4 s))
    (cond (Nat.beq code 14) (ineq6SF T.s rs rd t1 t2 t3 t4 s (fld5 T.cbits r8 t1 t2 t3 t4 s))
      (tr6SF T.s c rs rd sf t0 t1 t2 t3 t4 s code))

/-- The witness-driven form of `check6SCAt` (without its `inducedPattern` test). -/
def check6SCAtW (T : Tables6SC) (c : List Nat) (t0 wt : Nat) : Bool :=
  let rs := T.s.k6.pot (T.s.k6.pIdx (shapeCode (canon (c.take 7)))) t0
  let r7 := T.c7 (T.c7Idx (shapeCode (canon (c.drop 1)))) t0
  let r8 := T.c8 (T.c8Idx (shapeCode (canon c))) t0
  allSym (fun t1 =>
    let rd := T.s.k6.pot (T.s.k6.pIdx (shapeCode (canon (c.drop 1)))) t1
    let sf := T.s.shr (T.s.sIdx (shapeCode (canon (c.drop 2)))) t1
    allSym (fun t2 => allSym (fun t3 => allSym (fun t4 => allSym (fun s =>
      tr6SCF T c rs rd sf r7 r8 t0 t1 t2 t3 t4 s (code4 wt (ix5 t1 t2 t3 t4 s)))))))

/-! ### Soundness -/

theorem ineq6SCF_sound (T : Tables6SC) (c : List Nat) (rs rd t0 t1 t2 t3 t4 s sh : Nat)
    (hrs : rs = T.s.k6.pot (T.s.k6.pIdx (shapeCode (canon (c.take 7)))) t0)
    (hrd : rd = T.s.k6.pot (T.s.k6.pIdx (shapeCode (canon (c.drop 1)))) t1)
    (hsh : sh ≤ S5C T c [t0, t1, t2, t3, t4, s])
    (h : ineq6SF T.s rs rd t1 t2 t3 t4 s sh = true) :
    decide (T.s.k6.num + pot6 T.s.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
      T.s.k6.den * (120 * s + S5C T c [t0, t1, t2, t3, t4, s]) +
        pot6 T.s.k6 (c.take 7) [t0, t1, t2, t3, t4]) = true := by
  rw [pot6_eq_fld4, pot6_eq_fld4, ← hrs, ← hrd]
  unfold ineq6SF at h
  rw [nat_ble_eq] at h
  have h' := of_decide_eq_true h
  simp only [Nat.add_eq, Nat.mul_eq] at h'
  have hm := Nat.mul_le_mul_left T.s.k6.den
    (show 120 * s + sh ≤ 120 * s + S5C T c [t0, t1, t2, t3, t4, s] by omega)
  apply decide_eq_true
  omega

/-- The disjunction of `check6SAt` (share level `share6`) implies that of `check6SCAt`. -/
theorem lift6SC (T : Tables6SC) (c : List Nat) (t0 t1 t2 t3 t4 s : Nat)
    (h : (wforb6 T.s.k6 (c.drop 5) [t4, s] || wforb6 T.s.k6 (c.drop 4) [t3, t4, s] ||
      wforb6 T.s.k6 (c.drop 3) [t2, t3, t4, s] || wforb6 T.s.k6 (c.drop 2) [t1, t2, t3, t4, s] ||
      wforb6 T.s.k6 (c.drop 1) [t0, t1, t2, t3, t4, s] ||
      wforbH8 T.s c [t0, t1, t2, t3, t4, s] ||
      decide (T.s.k6.num + pot6 T.s.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
        T.s.k6.den * (120 * s + share6 T.s (c.drop 2) [t1, t2, t3, t4, s]) +
          pot6 T.s.k6 (c.take 7) [t0, t1, t2, t3, t4])) = true) :
    (wforb6 T.s.k6 (c.drop 5) [t4, s] || wforb6 T.s.k6 (c.drop 4) [t3, t4, s] ||
      wforb6 T.s.k6 (c.drop 3) [t2, t3, t4, s] || wforb6 T.s.k6 (c.drop 2) [t1, t2, t3, t4, s] ||
      wforb6 T.s.k6 (c.drop 1) [t0, t1, t2, t3, t4, s] ||
      wforbH8 T.s c [t0, t1, t2, t3, t4, s] ||
      decide (T.s.k6.num + pot6 T.s.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
        T.s.k6.den * (120 * s + S5C T c [t0, t1, t2, t3, t4, s]) +
          pot6 T.s.k6 (c.take 7) [t0, t1, t2, t3, t4])) = true := by
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · right
    have hle := share6_le_S5C T c t0 [t1, t2, t3, t4, s]
    have hm := Nat.mul_le_mul_left T.s.k6.den
      (show 120 * s + share6 T.s (c.drop 2) [t1, t2, t3, t4, s] ≤
        120 * s + S5C T c [t0, t1, t2, t3, t4, s] by omega)
    have h' := of_decide_eq_true h
    exact decide_eq_true (by omega)

/-- A selected transition disjunct implies the transition disjunction of `check6SCAt`. -/
theorem tr6SCF_sound (T : Tables6SC) (c : List Nat) (rs rd sf r7 r8 t0 t1 t2 t3 t4 s code : Nat)
    (hrs : rs = T.s.k6.pot (T.s.k6.pIdx (shapeCode (canon (c.take 7)))) t0)
    (hrd : rd = T.s.k6.pot (T.s.k6.pIdx (shapeCode (canon (c.drop 1)))) t1)
    (hsf : sf = T.s.shr (T.s.sIdx (shapeCode (canon (c.drop 2)))) t1)
    (hr7 : r7 = T.c7 (T.c7Idx (shapeCode (canon (c.drop 1)))) t0)
    (hr8 : r8 = T.c8 (T.c8Idx (shapeCode (canon c))) t0)
    (h : tr6SCF T c rs rd sf r7 r8 t0 t1 t2 t3 t4 s code = true) :
    (wforb6 T.s.k6 (c.drop 5) [t4, s] || wforb6 T.s.k6 (c.drop 4) [t3, t4, s] ||
      wforb6 T.s.k6 (c.drop 3) [t2, t3, t4, s] || wforb6 T.s.k6 (c.drop 2) [t1, t2, t3, t4, s] ||
      wforb6 T.s.k6 (c.drop 1) [t0, t1, t2, t3, t4, s] ||
      wforbH8 T.s c [t0, t1, t2, t3, t4, s] ||
      decide (T.s.k6.num + pot6 T.s.k6 (c.drop 1) [t1, t2, t3, t4, s] ≤
        T.s.k6.den * (120 * s + S5C T c [t0, t1, t2, t3, t4, s]) +
          pot6 T.s.k6 (c.take 7) [t0, t1, t2, t3, t4])) = true := by
  unfold tr6SCF at h
  cases h13 : Nat.beq code 13 <;> rw [h13] at h <;> simp only [cond_true, cond_false] at h
  · cases h14 : Nat.beq code 14 <;> rw [h14] at h <;> simp only [cond_true, cond_false] at h
    · exact lift6SC T c t0 t1 t2 t3 t4 s (tr6SF_sound T.s c rs rd sf t0 t1 t2 t3 t4 s code hrs hrd hsf h)
    · have e : fld5 T.cbits r8 t1 t2 t3 t4 s = ctx8A T c [t0, t1, t2, t3, t4, s] := by
        rw [hr8, ← ctxAt_eq_fld5]; rfl
      have h' := ineq6SCF_sound T c rs rd t0 t1 t2 t3 t4 s _ hrs hrd
        (by rw [e]; exact ctx8A_le_S5C T c _) h
      simp only [Bool.or_eq_true, h', or_true]
  · have e : fld5 T.cbits r7 t1 t2 t3 t4 s = ctx7A T (c.drop 1) [t0, t1, t2, t3, t4, s] := by
      rw [hr7, ← ctxAt_eq_fld5]; rfl
    have h' := ineq6SCF_sound T c rs rd t0 t1 t2 t3 t4 s _ hrs hrd
      (by rw [e]; exact ctx7A_le_S5C T c _) h
    simp only [Bool.or_eq_true, h', or_true]

/-- **Bridge** used by the shards: the witness-driven check of one label implies `check6SCAt`,
whatever the codes `wt`. -/
theorem check6SCAt_of_W (T : Tables6SC) (c : List Nat) (t0 wt : Nat)
    (h : check6SCAtW T c t0 wt = true) : check6SCAt T c t0 = true := by
  unfold check6SCAt
  unfold check6SCAtW at h
  refine Bool.or_eq_true_iff.2 (Or.inr ?_)
  refine allSym_of_forall _ (fun t1 h1 h1' => allSym_of_forall _ (fun t2 h2 h2' =>
    allSym_of_forall _ (fun t3 h3 h3' => allSym_of_forall _ (fun t4 h4 h4' =>
    allSym_of_forall _ (fun s hs hs' => ?_)))))
  have := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ h
    t1 h1 h1') t2 h2 h2') t3 h3 h3') t4 h4 h4') s hs hs'
  exact tr6SCF_sound T c _ _ _ _ _ t0 t1 t2 t3 t4 s _ rfl rfl rfl rfl rfl this

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.check6SCAt_of_W
