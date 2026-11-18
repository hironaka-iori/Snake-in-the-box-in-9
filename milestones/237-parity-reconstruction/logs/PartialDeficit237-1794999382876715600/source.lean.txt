import ContractedDegrees237

set_option Elab.async false

namespace PartialDeficit237
open LayerJoining ContractedDegrees237

/-- keep(i+1) records membership of path position i in the partial
majority set. The extra positions 0 and k+2 are outside the path. -/
def PartialPartner {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2*k)) (keep : Nat → Bool) (a b : Nat) : Prop :=
  a ≤ k ∧ b ≤ k ∧ a ≠ b ∧ keep (a+1) = true ∧ keep (b+1) = true ∧
  ∃ z : V, ∀ i : Fin (k+1), keep (i.val+1) = true →
    (R (p.vertex ⟨2*i.val, by have h := i.isLt; omega⟩) z ↔
      i.val = a ∨ i.val = b)

theorem partial_symmetric {V : Type} {R : V → V → Prop} {k : Nat}
    {p : InducedPath V R (2*k)} {keep : Nat → Bool} {a b : Nat} :
    PartialPartner p keep a b → PartialPartner p keep b a := by
  rintro ⟨ha, hb, distinct, ka, kb, z, hz⟩
  exact ⟨hb, ha, Ne.symm distinct, kb, ka, z, fun i hi => (hz i hi).trans or_comm⟩

/-- The same label still sees exactly the same two vertices after every
other deleted path position has been discarded. -/
theorem restrict_partner {V : Type} {R : V → V → Prop} {k : Nat}
    {p : InducedPath V R (2*k)} {keep : Nat → Bool} {a b : Nat}
    (full : Partner p a b) (ka : keep (a+1) = true) (kb : keep (b+1) = true) :
    PartialPartner p keep a b := by
  obtain ⟨ha, hb, distinct, z, hz⟩ := full
  exact ⟨ha, hb, distinct, ka, kb, z, fun i _ => hz i⟩

def total (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k+1 => total k f + f k

def missing (b : Bool) : Nat := if b then 0 else 1

def Isolated (G : Nat → Nat → Prop) (i : Nat) : Prop := ∀ j, ¬ G i j

noncomputable def deficiency (G : Nat → Nat → Prop) (keep : Nat → Bool) (i : Nat) : Nat := by
  classical
  exact if keep (i+1) then if Isolated G i then 2 else if AtMostOne G i then 1 else 0 else 0

private theorem local_bound {G : Nat → Nat → Prop} {k : Nat} {keep : Nat → Bool}
    (sym : ∀ {a b}, G a b → G b a)
    (steps : ∀ i, i < k → keep (i+1) = true → keep (i+2) = true → G i (i+1))
    (left : keep 0 = false) (right : keep (k+2) = false)
    (i : Nat) (hi : i ≤ k) :
    deficiency G keep i ≤ missing (keep i) + missing (keep (i+2)) := by
  classical
  by_cases ki : keep (i+1) = true
  · have predEdge (hp : keep i = true) : G i (i-1) := by
      have pos : 0 < i := by
        have nz : i ≠ 0 := by
          intro iz
          rw [iz, left] at hp
          contradiction
        omega
      have qi : i-1+1 = i := by omega
      have qn : i-1+2 = i+1 := by omega
      have e := steps (i-1) (by omega) (by simpa only [qi] using hp) (by simpa only [qn] using ki)
      exact sym (by simpa only [qi] using e)
    have succEdge (hs : keep (i+2) = true) : G i (i+1) := by
      have hk : i ≠ k := by
        intro eq
        rw [eq, right] at hs
        contradiction
      exact steps i (by omega) ki hs
    cases hp : keep i <;> cases hs : keep (i+2)
    · simp [deficiency, ki, missing]
      split <;> (first | omega | split <;> omega)
    · have ni : ¬ Isolated G i := fun h => h _ (succEdge hs)
      simp [deficiency, ki, ni, missing]
      split <;> omega
    · have ni : ¬ Isolated G i := fun h => h _ (predEdge hp)
      simp [deficiency, ki, ni, missing]
      split <;> omega
    · have ni : ¬ Isolated G i := fun h => h _ (succEdge hs)
      have nl : ¬ AtMostOne G i := by
        intro h
        have eq := h _ _ (predEdge hp) (succEdge hs)
        omega
      simp [deficiency, ki, ni, nl, missing]
  · simp [deficiency, ki]

private theorem sum_le {n : Nat} {f g : Nat → Nat}
    (bound : ∀ i, i < n → f i ≤ g i) : total n f ≤ total n g := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
      have p := ih (fun i hi => bound i (by omega))
      have q := bound n (by omega)
      simp only [total]
      omega

theorem shifted_neighbours (n : Nat) (f : Nat → Nat) :
    total n (fun i => f i + f (i+2)) + f 1 + f n =
      2 * total n (fun i => f (i+1)) + f 0 + f (n+1) := by
  induction n with
  | zero => simp [total, Nat.add_comm]
  | succ n ih =>
      simp only [total]
      change total n (fun i => f i + f (i+2)) + (f n + f (n+2)) + f 1 + f (n+1) =
        2 * (total n (fun i => f (i+1)) + f (n+1)) + f 0 + f (n+2)
      omega

/-- The total over the partial induced contraction graph counts exactly
two per isolated retained vertex and one per retained graph leaf.
Each omitted majority position contributes at most two units. -/
theorem partial_deficiency_bound {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2*k)) (sym : ∀ v w, R v w → R w v)
    (keep : Nat → Bool) (left : keep 0 = false) (right : keep (k+2) = false) :
    total (k+1) (deficiency (PartialPartner p keep) keep) ≤
      2 * total (k+1) (fun i => missing (keep (i+1))) + 2 := by
  have sums := sum_le (n := k+1) (f := deficiency (PartialPartner p keep) keep)
    (g := fun i => missing (keep i) + missing (keep (i+2))) (by
      intro i hi
      apply local_bound partial_symmetric _ left right i (by omega)
      intro j hj ja jb
      exact restrict_partner (consecutive_partners p sym j hj) ja jb)
  have shifted := shifted_neighbours (k+1) (fun i => missing (keep i))
  change total (k+1) (fun i => missing (keep i) + missing (keep (i+2))) +
    missing (keep 1) + missing (keep (k+1)) =
    2 * total (k+1) (fun i => missing (keep (i+1))) + missing (keep 0) + missing (keep (k+2)) at shifted
  rw [left, right] at shifted
  change _ + _ + _ = _ + 1 + 1 at shifted
  omega

#print axioms restrict_partner
#print axioms partial_deficiency_bound

end PartialDeficit237
