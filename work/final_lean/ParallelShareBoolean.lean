import ParallelShareGeometry

/-! A proved finite Boolean checker for the square and gate clauses.  Window
vertices are substituted by true only under the geometric window premise.
The checker may reject a valid formula when fuel runs out; acceptance is sound. -/
namespace Snake9.ParallelShareBoolean
open Snake9.LocalWindow Snake9.ParallelShareTerm

inductive Formula where
  | val (b : Bool)
  | sel (v : Nat)
  | neg (f : Formula)
  | conj (f g : Formula)
  | disj (f g : Formula)
deriving Repr, DecidableEq

def Formula.eval (S : Nat → Bool) : Formula → Bool
  | .val b => b
  | .sel v => S v
  | .neg f => !(f.eval S)
  | .conj f g => f.eval S && g.eval S
  | .disj f g => f.eval S || g.eval S

def Formula.subst (v : Nat) (b : Bool) : Formula → Formula
  | .val c => .val c
  | .sel w => if w = v then .val b else .sel w
  | .neg f => .neg (f.subst v b)
  | .conj f g => .conj (f.subst v b) (g.subst v b)
  | .disj f g => .disj (f.subst v b) (g.subst v b)

def Formula.first : Formula → Option Nat
  | .val _ => none
  | .sel v => some v
  | .neg f => f.first
  | .conj f g | .disj f g => f.first.or g.first

theorem Formula.eval_subst (f : Formula) (S : Nat → Bool) (v : Nat) :
    (f.subst v (S v)).eval S = f.eval S := by
  induction f with
  | val b => rfl
  | sel w => by_cases h : w = v <;> simp [Formula.subst, Formula.eval, h]
  | neg f ih => simp only [Formula.subst, Formula.eval, ih]
  | conj f g ihf ihg => simp only [Formula.subst, Formula.eval, ihf, ihg]
  | disj f g ihf ihg => simp only [Formula.subst, Formula.eval, ihf, ihg]

theorem Formula.eval_of_first_none (f : Formula) (S T : Nat → Bool)
    (h : f.first = none) : f.eval S = f.eval T := by
  induction f with
  | val b => rfl
  | sel v => simp [Formula.first] at h
  | neg f ih => exact congrArg Bool.not (ih h)
  | conj f g ihf ihg =>
    have hf : f.first = none := by cases he : f.first <;> simp_all [Formula.first]
    have hg : g.first = none := by simpa [Formula.first, hf] using h
    simp only [Formula.eval, ihf hf, ihg hg]
  | disj f g ihf ihg =>
    have hf : f.first = none := by cases he : f.first <;> simp_all [Formula.first]
    have hg : g.first = none := by simpa [Formula.first, hf] using h
    simp only [Formula.eval, ihf hf, ihg hg]

def check : Nat → Formula → Bool
  | fuel, f => match f.first with
    | none => f.eval (fun _ => false)
    | some v => match fuel with
      | 0 => false
      | n + 1 => check n (f.subst v false) && check n (f.subst v true)

theorem check_sound (fuel : Nat) (f : Formula) (h : check fuel f = true)
    (S : Nat → Bool) : f.eval S = true := by
  induction fuel generalizing f with
  | zero =>
    cases hf : f.first with
    | none =>
      rw [Formula.eval_of_first_none f S (fun _ => false) hf]
      simpa [check, hf] using h
    | some v => simp [check, hf] at h
  | succ n ih =>
    cases hf : f.first with
    | none =>
      rw [Formula.eval_of_first_none f S (fun _ => false) hf]
      simpa [check, hf] using h
    | some v =>
      rw [check, hf] at h
      change (check n (f.subst v false) && check n (f.subst v true)) = true at h
      rw [Bool.and_eq_true] at h
      have hs : check n (f.subst v (S v)) = true := by
        cases he : S v
        · exact h.1
        · exact h.2
      simpa only [Formula.eval_subst] using ih _ hs

def Formula.fixWindow (w : List Nat) : Formula → Formula
  | .val b => .val b
  | .sel v => if w.contains v then .val true else .sel v
  | .neg f => .neg (f.fixWindow w)
  | .conj f g => .conj (f.fixWindow w) (g.fixWindow w)
  | .disj f g => .disj (f.fixWindow w) (g.fixWindow w)

theorem Formula.eval_fixWindow (f : Formula) (S : Nat → Bool) (w : List Nat)
    (hw : ∀ v ∈ w, S v = true) : (f.fixWindow w).eval S = f.eval S := by
  induction f with
  | val b => rfl
  | sel v =>
    by_cases h : v ∈ w
    · simp [Formula.fixWindow, Formula.eval, h, hw v h]
    · have hn : w.contains v = false := by simpa using h
      simp [Formula.fixWindow, Formula.eval, h, hn]
  | neg f ih => simp only [Formula.fixWindow, Formula.eval, ih]
  | conj f g ihf ihg => simp only [Formula.fixWindow, Formula.eval, ihf, ihg]
  | disj f g ihf ihg => simp only [Formula.fixWindow, Formula.eval, ihf, ihg]

def checkWindow (fuel : Nat) (w : List Nat) (f : Formula) : Bool :=
  check fuel (f.fixWindow w)

theorem checkWindow_sound (fuel : Nat) (w : List Nat) (f : Formula)
    (h : checkWindow fuel w f = true) (S : Nat → Bool)
    (hw : ∀ v ∈ w, S v = true) : f.eval S = true := by
  have hc := check_sound fuel (f.fixWindow w) h S
  rwa [Formula.eval_fixWindow f S w hw] at hc

def square (q a b : Nat) : Formula :=
  .conj (.neg (.sel q)) (.conj (.neg (.sel (q ^^^ 2 ^ a)))
    (.conj (.neg (.sel (q ^^^ 2 ^ b))) (.neg (.sel (q ^^^ 2 ^ a ^^^ 2 ^ b)))))

def one (e : Formula) (x y z : Nat) : Formula :=
  .conj e (.conj (.neg (.conj (.sel x) (.sel y)))
    (.conj (.neg (.conj (.sel x) (.sel z))) (.neg (.conj (.sel y) (.sel z)))))

def zero (e : Formula) (x y z : Nat) : Formula :=
  .conj e (.conj (.neg (.sel x)) (.conj (.neg (.sel y)) (.neg (.sel z))))

theorem square_eval (S : Nat → Bool) (q a b : Nat) :
    (square q a b).eval S = emptyPred S q (a, b) := by
  simp only [square, Formula.eval, emptyPred, Nat.one_shiftLeft]
  cases S q <;> cases S (q ^^^ 2 ^ a) <;> cases S (q ^^^ 2 ^ b) <;>
    cases S (q ^^^ 2 ^ a ^^^ 2 ^ b) <;> rfl

theorem one_eval (S : Nat → Bool) (e : Formula) (x y z : Nat) :
    (one e x y z).eval S = gate1 (e.eval S) (S x) (S y) (S z) := by
  simp only [one, Formula.eval]
  cases e.eval S <;> cases S x <;> cases S y <;> cases S z <;> rfl

theorem zero_eval (S : Nat → Bool) (e : Formula) (x y z : Nat) :
    (zero e x y z).eval S = gate3 (e.eval S) (S x) (S y) (S z) := by
  simp only [zero, Formula.eval]
  cases e.eval S <;> cases S x <;> cases S y <;> cases S z <;> rfl

def assignment (M : Nat → Option Formula) (S : Nat → Bool) (x : Nat) : Bool :=
  ((M x).map (Formula.eval S)).getD false

def literalFormula (M : Nat → Option Formula) (l : Int) : Option Formula :=
  if 0 < l then M l.toNat else (M (-l).toNat).map Formula.neg

def clauseFormula (M : Nat → Option Formula) : List Int → Option Formula
  | [] => some (.val false)
  | l :: ls => do
    let f ← literalFormula M l
    let g ← clauseFormula M ls
    return .disj f g

theorem literalFormula_sem (M : Nat → Option Formula) (S : Nat → Bool)
    (l : Int) (f : Formula) (h : literalFormula M l = some f) :
    f.eval S = litTrue (assignment M S) l := by
  unfold literalFormula at h
  unfold litTrue
  by_cases hp : 0 < l
  all_goals simp only [hp, ↓reduceIte] at h ⊢
  · simp [assignment, h]
  · cases hm : M (-l).toNat with
    | none => simp [hm] at h
    | some g =>
      simp only [hm, Option.map_some, Option.some.injEq] at h
      change some (.neg g) = some f at h
      have he := Option.some.inj h
      subst f
      simp [assignment, hm, Formula.eval]

theorem clauseFormula_sem (M : Nat → Option Formula) (S : Nat → Bool)
    (cl : List Int) (f : Formula) (h : clauseFormula M cl = some f) :
    f.eval S = clauseTrue (assignment M S) cl := by
  induction cl generalizing f with
  | nil =>
    simp only [clauseFormula, Option.some.injEq] at h
    subst f; rfl
  | cons l ls ih =>
    cases hl : literalFormula M l with
    | none => simp [clauseFormula, hl] at h
    | some a =>
      cases hr : clauseFormula M ls with
      | none => simp [clauseFormula, hl, hr] at h
      | some b =>
        simp only [clauseFormula, hl, hr, Option.bind_some, Option.some.injEq] at h
        change some (.disj a b) = some f at h
        have he := Option.some.inj h
        subst f
        simp only [Formula.eval, literalFormula_sem M S l a hl, ih b hr,
          clauseTrue, List.any_cons]

def checkClause (fuel : Nat) (w : List Nat) (M : Nat → Option Formula) (cl : List Int) : Bool :=
  match clauseFormula M cl with
  | none => false
  | some f => checkWindow fuel w f

theorem checkClause_sound (fuel : Nat) (w : List Nat) (M : Nat → Option Formula)
    (cl : List Int) (h : checkClause fuel w M cl = true) (S : Nat → Bool)
    (hw : ∀ v ∈ w, S v = true) : clauseTrue (assignment M S) cl = true := by
  unfold checkClause at h
  cases hf : clauseFormula M cl with
  | none => simp [hf] at h
  | some f =>
    simp only [hf] at h
    rw [← clauseFormula_sem M S cl f hf]
    exact checkWindow_sound fuel w f h S hw

theorem checkClauses_sound (fuel : Nat) (w : List Nat) (M : Nat → Option Formula)
    (cnf : List (List Int)) (h : cnf.all (checkClause fuel w M) = true) (S : Nat → Bool)
    (hw : ∀ v ∈ w, S v = true) : cnfTrue (assignment M S) cnf = true := by
  apply List.all_eq_true.mpr
  intro cl hcl
  exact checkClause_sound fuel w M cl (List.all_eq_true.mp h cl hcl) S hw

#print axioms check_sound
#print axioms checkWindow_sound
#print axioms square_eval
#print axioms one_eval
#print axioms zero_eval
#print axioms checkClause_sound
#print axioms checkClauses_sound
end Snake9.ParallelShareBoolean
