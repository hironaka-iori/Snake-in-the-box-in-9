import LocalWindowModel
/-! Renaming glue on `Nat` literal codes (`decodeLit`), with a binary-tree lookup.

`renN f core' core` checks clause by clause that `core'` is `core` with every variable `v'` replaced:
new variable `v'` stands for old variable `f v'`. Then `Unsat core'` gives `Unsat core`.
`BT.get` looks up a balanced tree by the bits of the index (least significant first), so a kernel
lookup costs about 14 `Nat` divisions instead of a linear `List.getD`. Chunks glue with `renN_app`. -/
namespace Dim8Lift.RenN
open Snake9.LocalWindow

inductive BT where
  | lf (n : Nat)
  | nd (l r : BT)

def BT.get : BT → Nat → Nat
  | .lf n, _ => n
  | .nd l r, i => if i % 2 = 0 then l.get (i / 2) else r.get (i / 2)

def renLit (f : Nat → Nat) (a b : Nat) : Bool :=
  (a % 2 == b % 2) && (a / 2 != 0) && (b / 2 != 0) && (f (a / 2) == b / 2)

def renCl (f : Nat → Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => renLit f a b && renCl f as bs
  | _, _ => false

def renN (f : Nat → Nat) : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | a :: as, b :: bs => renCl f a b && renN f as bs
  | _, _ => false

theorem lit_ok (τ : Nat → Bool) (f : Nat → Nat) (a b : Nat) (h : renLit f a b = true) :
    litTrue (fun v => τ (f v)) (decodeLit a) = litTrue τ (decodeLit b) := by
  simp only [renLit, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hm, ha⟩, hb⟩, hf⟩ := h
  unfold decodeLit litTrue
  have ha' : 0 < a / 2 := Nat.pos_of_ne_zero ha
  have hb' : 0 < b / 2 := Nat.pos_of_ne_zero hb
  by_cases p : a % 2 = 0
  · have q : b % 2 = 0 := by omega
    rw [if_pos p, if_pos q]
    have i1 : (0 : Int) < Int.ofNat (a / 2) := by simp; omega
    have i2 : (0 : Int) < Int.ofNat (b / 2) := by simp; omega
    rw [if_pos i1, if_pos i2]
    simp only [Int.toNat_natCast, Int.ofNat_eq_natCast]
    rw [hf]
  · have q : ¬ b % 2 = 0 := by omega
    rw [if_neg p, if_neg q]
    have i1 : ¬ (0 : Int) < -Int.ofNat (a / 2) := by simp; omega
    have i2 : ¬ (0 : Int) < -Int.ofNat (b / 2) := by simp; omega
    rw [if_neg i1, if_neg i2]
    simp only [Int.neg_neg, Int.toNat_natCast, Int.ofNat_eq_natCast]
    rw [hf]

theorem cl_ok (τ : Nat → Bool) (f : Nat → Nat) : ∀ (c' c : List Nat), renCl f c' c = true →
    clauseTrue (fun v => τ (f v)) (c'.map decodeLit) = clauseTrue τ (c.map decodeLit)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [renCl] at h
  | _ :: _, [], h => by simp [renCl] at h
  | a :: as, b :: bs, h => by
    simp only [renCl, Bool.and_eq_true] at h
    have ih := cl_ok τ f as bs h.2
    simp only [clauseTrue] at ih ⊢
    simp only [List.map_cons, List.any_cons, lit_ok τ f a b h.1, ih]

theorem cnf_ok (τ : Nat → Bool) (f : Nat → Nat) : ∀ (a b : List (List Nat)), renN f a b = true →
    cnfTrue (fun v => τ (f v)) (a.map (·.map decodeLit)) = cnfTrue τ (b.map (·.map decodeLit))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [renN] at h
  | _ :: _, [], h => by simp [renN] at h
  | c' :: cs', c :: cs, h => by
    simp only [renN, Bool.and_eq_true] at h
    have ih := cnf_ok τ f cs' cs h.2
    simp only [cnfTrue] at ih ⊢
    simp only [List.map_cons, List.all_cons, cl_ok τ f c' c h.1, ih]

theorem unsat_of_renN (f : Nat → Nat) (a b : List (List Nat)) (h : renN f a b = true)
    (hU : Unsat (a.map (·.map decodeLit))) : Unsat (b.map (·.map decodeLit)) := by
  intro τ; rw [← cnf_ok τ f a b h]; exact hU _

theorem renN_app (f : Nat → Nat) : ∀ {a b c d : List (List Nat)}, renN f a c = true → renN f b d = true →
    renN f (a ++ b) (c ++ d) = true
  | [], _, [], _, _, h2 => by simpa using h2
  | [], _, _ :: _, _, h1, _ => by simp [renN] at h1
  | _ :: _, _, [], _, h1, _ => by simp [renN] at h1
  | x :: xs, _, y :: ys, _, h1, h2 => by
    simp only [renN, Bool.and_eq_true] at h1
    simp only [List.cons_append, renN, Bool.and_eq_true]
    exact ⟨h1.1, renN_app f h1.2 h2⟩

end Dim8Lift.RenN
