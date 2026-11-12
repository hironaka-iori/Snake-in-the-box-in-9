import LayerJoining
namespace Pruning194
open LayerJoining

/-- A nonterminal vertex with at most one available neighbour cannot lie on the path. -/
theorem lowDegreeExcluded {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m) (allowed : V → Prop) (v : V)
    (symmetric : ∀ x y, R x y → R y x)
    (covered : ∀ i, allowed (p.vertex i))
    (thin : ∀ x y, allowed x → allowed y → R v x → R v y → x=y)
    (hfirst : v ≠ p.vertex ⟨0,by omega⟩)
    (hlast : v ≠ p.vertex ⟨m,by omega⟩) : ∀ i, p.vertex i ≠ v := by
  intro i he
  have hi0 : 0 < i.val := by
    by_cases hn : 0 < i.val
    · exact hn
    · have hi : i=⟨0,by omega⟩ := by apply Fin.ext; simp only [Fin.val_mk]; omega
      exact False.elim (hfirst (he.symm.trans (congrArg p.vertex hi)))
  have him : i.val < m := by
    by_cases hn : i.val < m
    · exact hn
    · have hi : i=⟨m,by omega⟩ := by apply Fin.ext; simp only [Fin.val_mk]; omega
      exact False.elim (hlast (he.symm.trans (congrArg p.vertex hi)))
  let prev : Fin (m+1) := ⟨i.val-1,by omega⟩
  let next : Fin (m+1) := ⟨i.val+1,by omega⟩
  have hp : R (p.vertex prev) (p.vertex i) :=
    (p.induced prev i (by dsimp [prev]; omega)).mpr (by dsimp [prev]; omega)
  have hn : R (p.vertex i) (p.vertex next) :=
    (p.induced i next (by dsimp [next]; omega)).mpr (by dsimp [next])
  rw [he] at hp hn
  have same := thin (p.vertex prev) (p.vertex next) (covered prev) (covered next)
    (symmetric _ _ hp) hn
  have indices := congrArg Fin.val (p.distinct prev next same)
  dsimp [prev,next] at indices
  omega

theorem adjacentAnchors {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m) (positive : 0<m)
    (adjacent : R (p.vertex ⟨0,by omega⟩) (p.vertex ⟨m,by omega⟩)) : m=1 := by
  have h := (p.induced ⟨0,by omega⟩ ⟨m,by omega⟩ (by simpa using positive)).mp adjacent
  simpa using h.symm

theorem equalColourBound (t start other : Nat)
    (hs : t+1 ≤ start) (ho : t ≤ other) : 2*t ≤ 2*min (start-1) other := by
  have h : t ≤ min (start-1) other := Nat.le_min.mpr ⟨by omega,ho⟩
  omega

theorem oppositeColourBound (t even odd : Nat)
    (he : t+1 ≤ even) (ho : t+1 ≤ odd) : 2*t+1 ≤ 2*min even odd-1 := by
  have h : t+1 ≤ min even odd := Nat.le_min.mpr ⟨he,ho⟩
  omega

/-- Entry and exit from a set through one vertex would repeat that vertex. -/
theorem singleAttachmentObstruction {V : Type} {R : V → V → Prop} {m : Nat}
    (p : InducedPath V R m) (inside : V → Prop) (cut : V)
    (symmetric : ∀ x y, R x y → R y x)
    (boundary : ∀ x y, inside x → ¬ inside y → R x y → y=cut)
    (i j : Fin (m+1)) (hi : 0<i.val) (hj : j.val<m) (order : i.val≤j.val)
    (hin : inside (p.vertex i)) (hjn : inside (p.vertex j))
    (hprev : ¬ inside (p.vertex ⟨i.val-1,by omega⟩))
    (hnext : ¬ inside (p.vertex ⟨j.val+1,by omega⟩)) : False := by
  let prev : Fin (m+1) := ⟨i.val-1,by omega⟩
  let next : Fin (m+1) := ⟨j.val+1,by omega⟩
  have hp : R (p.vertex prev) (p.vertex i) :=
    (p.induced prev i (by dsimp [prev]; omega)).mpr (by dsimp [prev]; omega)
  have hn : R (p.vertex j) (p.vertex next) :=
    (p.induced j next (by dsimp [next]; omega)).mpr (by dsimp [next])
  have hpv := boundary (p.vertex i) (p.vertex prev) hin hprev (symmetric _ _ hp)
  have hnv := boundary (p.vertex j) (p.vertex next) hjn hnext hn
  have indices := congrArg Fin.val (p.distinct prev next (hpv.trans hnv.symm))
  dsimp [prev,next] at indices
  omega

#print axioms lowDegreeExcluded
#print axioms adjacentAnchors
#print axioms equalColourBound
#print axioms oppositeColourBound
#print axioms singleAttachmentObstruction
end Pruning194
