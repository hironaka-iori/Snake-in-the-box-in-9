import WindowAlpha
import DfsPrefix

namespace Snake9.Window244
open SquareIncidence
noncomputable section
set_option maxHeartbeats 0

theorem inPath_reverse_iff {m : Nat} (p : Snake m) (v : Vertex) :
    InPath (reverseSnake p) v ↔ InPath p v := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨⟨m-i.val,by omega⟩,hi⟩
  · rintro ⟨i,rfl⟩
    refine ⟨⟨m-i.val,by omega⟩,?_⟩
    change p.vertex ⟨m-(m-i.val),_⟩ = p.vertex i
    congr 1
    apply Fin.ext
    simp only
    omega

theorem singleton_reverse {m : Nat} (p : Snake m) (v : Vertex) (ab : AxisPair) :
    SquareIncidence.singleton (reverseSnake p) ab v = SquareIncidence.singleton p ab v := by
  unfold SquareIncidence.singleton
  congr 1
  apply propext
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    exact ⟨(inPath_reverse_iff p _).mp h0,
      (fun h => h1 ((inPath_reverse_iff p _).mpr h)),
      (fun h => h2 ((inPath_reverse_iff p _).mpr h)),
      (fun h => h3 ((inPath_reverse_iff p _).mpr h))⟩
  · rintro ⟨h0,h1,h2,h3⟩
    exact ⟨(inPath_reverse_iff p _).mpr h0,
      (fun h => h1 ((inPath_reverse_iff p _).mp h)),
      (fun h => h2 ((inPath_reverse_iff p _).mp h)),
      (fun h => h3 ((inPath_reverse_iff p _).mp h))⟩

theorem localAlpha_reverse {m : Nat} (p : Snake m) (i : Fin (m+1)) :
    localAlpha (reverseSnake p) i = localAlpha p ⟨m-i.val,by omega⟩ := by
  unfold localAlpha
  apply Finset.sum_congr rfl
  intro ab _
  exact singleton_reverse p _ ab

/-- Once no-223 holds for every oriented snake, no-322 follows without a
third SAT instance. This lemma does not assume no-223 as a new axiom. -/
theorem no322_of_no223 {m : Nat}
    (hno : ∀ (q : Snake m) (r : Nat) (hr : r+4 ≤ m),
      ¬ (localAlpha q ⟨r+1,by omega⟩ = 2 ∧
         localAlpha q ⟨r+2,by omega⟩ = 2 ∧
         localAlpha q ⟨r+3,by omega⟩ = 3))
    (p : Snake m) (r : Nat) (hr : r+4 ≤ m) :
      ¬ (localAlpha p ⟨r+1,by omega⟩ = 3 ∧
         localAlpha p ⟨r+2,by omega⟩ = 2 ∧
         localAlpha p ⟨r+3,by omega⟩ = 2) := by
  rintro ⟨h1,h2,h3⟩
  apply hno (reverseSnake p) (m-r-4) (by omega)
  have hi1 : (⟨m-(m-r-4+1),by omega⟩ : Fin (m+1)) = ⟨r+3,by omega⟩ := by
    apply Fin.ext; simp only; omega
  have hi2 : (⟨m-(m-r-4+2),by omega⟩ : Fin (m+1)) = ⟨r+2,by omega⟩ := by
    apply Fin.ext; simp only; omega
  have hi3 : (⟨m-(m-r-4+3),by omega⟩ : Fin (m+1)) = ⟨r+1,by omega⟩ := by
    apply Fin.ext; simp only; omega
  simp only [localAlpha_reverse,hi1,hi2,hi3]
  exact ⟨h3,h2,h1⟩

#print axioms inPath_reverse_iff
#print axioms localAlpha_reverse
#print axioms no322_of_no223
end
end Snake9.Window244
