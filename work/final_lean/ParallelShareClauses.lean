import ParallelShareBlocks

/-! A concrete assignment and clause checker for parallel-share totalizers.
The fallback assignment is reserved for existing window/endpoint counters. -/
namespace Snake9.ParallelShareClauses
open Snake9.LocalWindow Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks

structure Info where
  lo : Nat
  hi : Nat
  threshold : Nat
deriving Repr, DecidableEq

inductive Meaning where
  | boolean (f : Formula)
  | total (info : Info)
deriving Repr, DecidableEq

def assignment (B S : Nat → Bool) (ts : List Term) (M : Nat → Option Meaning) (x : Nat) : Bool :=
  match M x with
  | none => B x
  | some (.boolean f) => f.eval S
  | some (.total i) => decide (i.threshold ≤ blockMass S ts i.lo i.hi)

def booleanMeaning (M : Nat → Option Meaning) (x : Nat) : Option Formula :=
  match M x with
  | some (.boolean f) => some f
  | _ => none

def equivalent (f g : Formula) : Formula :=
  .conj (.disj (.neg f) g) (.disj (.neg g) f)

theorem equivalent_sem (f g : Formula) (S : Nat → Bool)
    (h : (equivalent f g).eval S = true) : f.eval S = g.eval S := by
  cases hf : f.eval S <;> cases hg : g.eval S <;> simp_all [equivalent, Formula.eval]

theorem assignment_boolean (B S : Nat → Bool) (ts : List Term) (M : Nat → Option Meaning)
    {x : Nat} {f : Formula} (h : booleanMeaning M x = some f) :
    assignment B S ts M x = f.eval S := by
  unfold booleanMeaning at h
  cases hm : M x with
  | none => simp [hm] at h
  | some m => cases m with
    | boolean g => simp only [hm, Option.some.injEq] at h; subst f; simp [assignment, hm]
    | total i => simp [hm] at h

theorem literal_sem (B S : Nat → Bool) (ts : List Term) (M : Nat → Option Meaning)
    {l : Int} {f : Formula} (h : literalFormula (booleanMeaning M) l = some f) :
    f.eval S = litTrue (assignment B S ts M) l := by
  unfold literalFormula at h
  unfold litTrue
  by_cases hp : 0 < l
  all_goals simp only [hp, ↓reduceIte] at h ⊢
  · exact (assignment_boolean B S ts M h).symm
  · cases hm : booleanMeaning M (-l).toNat with
    | none => simp [hm] at h
    | some g =>
      rw [hm] at h
      change some (.neg g) = some f at h
      have he := Option.some.inj h
      subst f
      simp only [Formula.eval, assignment_boolean B S ts M hm]

theorem formula_sem (B S : Nat → Bool) (ts : List Term) (M : Nat → Option Meaning)
    {cl : List Int} {f : Formula} (h : clauseFormula (booleanMeaning M) cl = some f) :
    f.eval S = clauseTrue (assignment B S ts M) cl := by
  induction cl generalizing f with
  | nil => simp only [clauseFormula, Option.some.injEq] at h; subst f; rfl
  | cons l ls ih =>
    cases hl : literalFormula (booleanMeaning M) l with
    | none => simp [clauseFormula, hl] at h
    | some a =>
      cases hr : clauseFormula (booleanMeaning M) ls with
      | none => simp [clauseFormula, hl, hr] at h
      | some b =>
        simp only [clauseFormula, hl, hr] at h
        change some (.disj a b) = some f at h
        have he := Option.some.inj h
        subst f
        simp only [Formula.eval, literal_sem B S ts M hl, ih hr, clauseTrue, List.any_cons]

theorem boolean_clause (B S : Nat → Bool) (ts : List Term) (M : Nat → Option Meaning)
    (w : List Nat) (cl : List Int)
    (h : checkClause 8 w (booleanMeaning M) cl = true)
    (hw : ∀ v ∈ w, S v = true) : clauseTrue (assignment B S ts M) cl = true := by
  unfold checkClause at h
  cases hf : clauseFormula (booleanMeaning M) cl with
  | none => simp [hf] at h
  | some f =>
    simp only [hf] at h
    rw [← formula_sem B S ts M hf]
    exact checkWindow_sound 8 w f h S hw

inductive Ref where
  | total
  | leaf (position threshold : Nat)
deriving Repr, DecidableEq

def dfltTerm : Term := ⟨0, 0, 0, 0⟩

def info (w : List Nat) (ts : List Term) (M : Nat → Option Meaning)
    (x : Nat) : Ref → Option Info
  | .total => match M x with
    | some (.total i) => some i
    | _ => none
  | .leaf p s => match booleanMeaning M x with
    | none => none
    | some f =>
      let t := ts.getD p dfltTerm
      if p < ts.length ∧ t.valid w ∧ 1 ≤ s ∧ s ≤ 6 then
        if checkWindow 8 w (equivalent f (t.leaf s)) then some ⟨p, p + 1, s⟩ else none
      else none

theorem blockMass_single (S : Nat → Bool) (ts : List Term) {p : Nat} (hp : p < ts.length) :
    blockMass S ts p (p + 1) = (ts.getD p dfltTerm).value S := by
  unfold blockMass mass block
  rw [show p + 1 - p = 1 by omega, List.drop_eq_getElem_cons hp]
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hp, Option.getD_some]

theorem info_sem {S E B : Nat → Bool} {w : List Nat} {cs : List Centre}
    (ax : Axioms S E w cs) (ts : List Term) (M : Nat → Option Meaning)
    (x : Nat) (r : Ref) (i : Info) (h : info w ts M x r = some i) :
    assignment B S ts M x = decide (i.threshold ≤ blockMass S ts i.lo i.hi) := by
  cases r with
  | total =>
    unfold info at h
    cases hm : M x with
    | none => simp [hm] at h
    | some m => cases m with
      | boolean f => simp [hm] at h
      | total j => simp only [hm, Option.some.injEq] at h; subst i; simp [assignment, hm]
  | leaf p s =>
    unfold info at h
    cases hm : booleanMeaning M x with
    | none => simp [hm] at h
    | some f =>
      simp only [hm] at h
      split at h
      · rename_i hp
        split at h
        · rename_i hc
          simp only [Option.some.injEq] at h
          subst i
          rw [assignment_boolean B S ts M hm, blockMass_single S ts hp.1]
          have he := equivalent_sem f ((ts.getD p dfltTerm).leaf s) S
            (checkWindow_sound 8 w _ hc S ax.window_sel)
          rw [he]
          exact Term.leaf_sem ax _ hp.2.1 hp.2.2.1 hp.2.2.2
        · simp at h
      · simp at h

def subCheck (o a : Info) : Bool :=
  decide (o.lo ≤ a.lo ∧ a.lo ≤ a.hi ∧ a.hi ≤ o.hi ∧ o.threshold ≤ a.threshold)

def pairCheck (o a b : Info) : Bool :=
  decide (o.lo ≤ a.lo ∧ a.lo ≤ a.hi ∧ a.hi ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.hi ≤ o.hi ∧
    o.threshold ≤ a.threshold + b.threshold)

theorem subCheck_sem (S : Nat → Bool) (ts : List Term) (o a : Info)
    (h : subCheck o a = true) (ha : a.threshold ≤ blockMass S ts a.lo a.hi) :
    o.threshold ≤ blockMass S ts o.lo o.hi := by
  simp only [subCheck, decide_eq_true_eq] at h
  have hb := blockMass_sub S ts h.1 h.2.1 h.2.2.1
  omega

theorem pairCheck_sem (S : Nat → Bool) (ts : List Term) (o a b : Info)
    (h : pairCheck o a b = true) (ha : a.threshold ≤ blockMass S ts a.lo a.hi)
    (hb : b.threshold ≤ blockMass S ts b.lo b.hi) :
    o.threshold ≤ blockMass S ts o.lo o.hi := by
  simp only [pairCheck, decide_eq_true_eq] at h
  have hc := blockMass_pair S ts ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  omega

def mergeCheck (w : List Nat) (ts : List Term) (M : Nat → Option Meaning)
    (r1 r2 : Ref) : List Int → Bool
  | [x, o] =>
    if x < 0 ∧ 0 < o then
      match info w ts M o.toNat .total, info w ts M (-x).toNat r1 with
      | some oi, some ai => subCheck oi ai
      | _, _ => false
    else false
  | [x, y, o] =>
    if x < 0 ∧ y < 0 ∧ 0 < o then
      match info w ts M o.toNat .total, info w ts M (-x).toNat r1,
          info w ts M (-y).toNat r2 with
      | some oi, some ai, some bi => pairCheck oi ai bi
      | _, _, _ => false
    else false
  | _ => false

theorem implication (a o : Bool) (h : a = true → o = true) : (!a || o) = true := by
  cases a <;> simp_all

theorem implication_two (a b o : Bool) (h : a = true → b = true → o = true) :
    (!a || !b || o) = true := by cases a <;> cases b <;> simp_all

theorem mergeCheck_sound {S E B : Nat → Bool} {w : List Nat} {cs : List Centre}
    (ax : Axioms S E w cs) (ts : List Term) (M : Nat → Option Meaning)
    (r1 r2 : Ref) (cl : List Int) (h : mergeCheck w ts M r1 r2 cl = true) :
    clauseTrue (assignment B S ts M) cl = true := by
  match cl, h with
  | [x, o], h =>
    simp only [mergeCheck] at h
    split at h
    · rename_i signs
      split at h
      · rename_i oi ai ho ha
        have hx : ¬ 0 < x := by omega
        simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, litTrue,
          hx, signs.2, ↓reduceIte]
        apply implication
        intro hax
        rw [info_sem ax ts M _ r1 ai ha, decide_eq_true_eq] at hax
        rw [info_sem ax ts M _ .total oi ho, decide_eq_true_eq]
        exact subCheck_sem S ts oi ai h hax
      · simp at h
    · simp at h
  | [x, y, o], h =>
    simp only [mergeCheck] at h
    split at h
    · rename_i signs
      split at h
      · rename_i oi ai bi ho ha hb
        have hx : ¬ 0 < x := by omega
        have hy : ¬ 0 < y := by omega
        simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, litTrue,
          hx, hy, signs.2.2, ↓reduceIte]
        rw [← Bool.or_assoc]
        apply implication_two
        intro hax hby
        rw [info_sem ax ts M _ r1 ai ha, decide_eq_true_eq] at hax
        rw [info_sem ax ts M _ r2 bi hb, decide_eq_true_eq] at hby
        rw [info_sem ax ts M _ .total oi ho, decide_eq_true_eq]
        exact pairCheck_sem S ts oi ai bi h hax hby
      · simp at h
    · simp at h

def boundCheck (cap : Nat) (M : Nat → Option Meaning) : List Int → Bool
  | [x] => if x < 0 then
      match M (-x).toNat with
      | some (.total i) => decide (cap < i.threshold)
      | _ => false
    else false
  | _ => false

theorem boundCheck_sound {S E B : Nat → Bool} {w : List Nat} {cs : List Centre} {cap : Nat}
    (ax : AxiomsP S E w cs cap) (ts : List Term) (ht : ts.Sublist (allTerms cs))
    (M : Nat → Option Meaning) (cl : List Int) (h : boundCheck cap M cl = true) :
    clauseTrue (assignment B S ts M) cl = true := by
  match cl, h with
  | [x], h =>
    simp only [boundCheck] at h
    split at h
    · rename_i hx
      split at h
      · rename_i i hm
        have hcap := blockMass_cap ax ht i.lo i.hi
        have hnot : ¬ i.threshold ≤ blockMass S ts i.lo i.hi := by
          simp only [decide_eq_true_eq] at h
          omega
        simp [clauseTrue, litTrue, show ¬ 0 < x by omega, assignment, hm, hnot]
      · simp at h
    · simp at h

#print axioms boolean_clause
#print axioms info_sem
#print axioms subCheck_sem
#print axioms pairCheck_sem
#print axioms mergeCheck_sound
#print axioms boundCheck_sound
end Snake9.ParallelShareClauses
