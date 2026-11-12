import LayerJoining
namespace CycleCut196
open LayerJoining

theorem finiteMaximum (f : Nat → Nat) (n : Nat) :
    ∃ i, i≤n ∧ ∀ j, j≤n → f j≤f i := by
  induction n with
  | zero =>
    refine ⟨0,by omega,?_⟩
    intro j hj
    have h : j=0 := by omega
    simpa only [h] using (Nat.le_refl (f 0))
  | succ n ih =>
    obtain ⟨i,hi,hmax⟩ := ih
    by_cases top : f (n+1) ≤ f i
    · refine ⟨i,by omega,?_⟩
      intro j hj
      by_cases old : j≤n
      · exact hmax j old
      · have he : j=n+1 := by omega
        simpa only [he] using top
    · refine ⟨n+1,by omega,?_⟩
      intro j hj
      by_cases old : j≤n
      · have lower := hmax j old
        omega
      · have he : j=n+1 := by omega
        simpa only [he] using (Nat.le_refl (f (n+1)))

/-- A finite set with two distinct neighbours at every vertex cannot be
    contained in an induced path. This gives the soundness of cycle cuts. -/
theorem noContainedDegreeTwo {V : Type} {R : V → V → Prop} {m n : Nat}
    (p : InducedPath V R m) (c : Fin (n+1) → V)
    (prev next : Fin (n+1) → Fin (n+1))
    (distinctNeighbours : ∀ i, c (prev i) ≠ c i ∧ c (next i) ≠ c i ∧
      c (prev i) ≠ c (next i))
    (edges : ∀ i, R (c (prev i)) (c i) ∧ R (c (next i)) (c i)) :
    ¬ (∀ i, ∃ j, p.vertex j=c i) := by
  intro contained
  let positions : Fin (n+1) → Fin (m+1) := fun i => Classical.choose (contained i)
  have agree : ∀ i, p.vertex (positions i)=c i := fun i => Classical.choose_spec (contained i)
  let f : Nat → Nat := fun i => if h : i<n+1 then (positions ⟨i,h⟩).val else 0
  obtain ⟨a,ha,hmax⟩ := finiteMaximum f n
  let i : Fin (n+1) := ⟨a,by omega⟩
  have maximum : ∀ j, (positions j).val≤(positions i).val := by
    intro j
    have h := hmax j.val (by omega)
    simpa only [f, dif_pos j.isLt, dif_pos (show a<n+1 by omega)] using h
  have unequal (j : Fin (n+1)) (hne : c j≠c i) : positions j≠positions i := by
    intro he
    apply hne
    rw [← agree j, ← agree i, he]
  have before (j : Fin (n+1)) (hne : c j≠c i) :
      (positions j).val<(positions i).val := by
    have le := maximum j
    have ne := unequal j hne
    have values : (positions j).val≠(positions i).val := by
      intro he;exact ne (Fin.ext he)
    omega
  have ep : R (p.vertex (positions (prev i))) (p.vertex (positions i)) := by
    simpa only [agree] using (edges i).1
  have en : R (p.vertex (positions (next i))) (p.vertex (positions i)) := by
    simpa only [agree] using (edges i).2
  have hp := (p.induced _ _ (before (prev i) (distinctNeighbours i).1)).mp ep
  have hn := (p.induced _ _ (before (next i) (distinctNeighbours i).2.1)).mp en
  have same : positions (prev i)=positions (next i) := by apply Fin.ext;omega
  apply (distinctNeighbours i).2.2
  rw [← agree (prev i), ← agree (next i), same]

#print axioms finiteMaximum
#print axioms noContainedDegreeTwo
end CycleCut196
