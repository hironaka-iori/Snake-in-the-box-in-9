import PathStructure
import Mathlib.Tactic

namespace Snake9.Contraction

theorem positions_rigid (f : Nat → Nat) (k : Nat)
    (distinct : ∀ i j, i ≤ k → j ≤ k → f i = f j → i = j)
    (step : ∀ i, i < k → f i + 1 = f (i+1) ∨ f (i+1) + 1 = f i) :
    (∀ i, i ≤ k → f i = f 0 + i) ∨
    (∀ i, i ≤ k → f i + i = f 0) := by
  by_cases hk : k = 0
  · left
    intro i hi
    have : i = 0 := by omega
    simp [this]
  rcases step 0 (by omega) with first | first
  · have hs : ∀ i, i < k → f i + 1 = f (i+1) := by
      intro i
      induction i with
      | zero => intro _; exact first
      | succ i ih =>
        intro hi
        have prev := ih (by omega)
        rcases step (i+1) hi with h | h
        · exact h
        · have eq : f (i+1+1) = f i := by omega
          have bad := distinct (i+1+1) i (by omega) (by omega) eq
          omega
    left
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro hi
      have prev := ih (by omega)
      have next := hs i (by omega)
      omega
  · have hs : ∀ i, i < k → f (i+1) + 1 = f i := by
      intro i
      induction i with
      | zero => intro _; exact first
      | succ i ih =>
        intro hi
        have prev := ih (by omega)
        rcases step (i+1) hi with h | h
        · have eq : f (i+1+1) = f i := by omega
          have bad := distinct (i+1+1) i (by omega) (by omega) eq
          omega
        · exact h
    right
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro hi
      have prev := ih (by omega)
      have next := hs i (by omega)
      omega

theorem index_embedding_rigid {m k : Nat} (p : Snake m)
    (e : Fin (k+1) → Fin (m+1)) (he : Function.Injective e)
    (walk : ∀ i : Fin k, Adj (p.vertex (e i.castSucc)) (p.vertex (e i.succ))) :
    (∀ i, (e i).val = (e 0).val + i.val) ∨
    (∀ i, (e i).val + i.val = (e 0).val) := by
  let f : Nat → Nat := fun i => (e ⟨min i k, by omega⟩).val
  have hf (i : Fin (k+1)) : f i.val = (e i).val := by
    simp only [f, Nat.min_eq_left (show i.val ≤ k by omega)]
  have hz : f 0 = (e 0).val := by simpa using hf 0
  have hd : ∀ i j, i ≤ k → j ≤ k → f i = f j → i = j := by
    intro i j hi hj eq
    have ee : e ⟨i,by omega⟩ = e ⟨j,by omega⟩ := by
      apply Fin.ext
      simpa only [f,Nat.min_eq_left hi,Nat.min_eq_left hj] using eq
    have := congrArg Fin.val (he ee)
    exact this
  have hs : ∀ i, i < k → f i + 1 = f (i+1) ∨ f (i+1) + 1 = f i := by
    intro i hi
    have h := (path_adj_iff p _ _).mp (walk ⟨i,hi⟩)
    simpa only [f,Nat.min_eq_left (show i ≤ k by omega),
      Nat.min_eq_left (show i+1 ≤ k by omega)] using h
  rcases positions_rigid f k hd hs with h | h
  · left
    intro i
    simpa only [hf i, hz] using h i.val (by omega)
  · right
    intro i
    simpa only [hf i, hz] using h i.val (by omega)

theorem selected_path_contiguous {m k : Nat} (p : Snake m) (q : Snake k)
    (selected : ∀ i, InPath p (q.vertex i)) :
    ∃ e : Fin (k+1) → Fin (m+1),
      (∀ i, p.vertex (e i) = q.vertex i) ∧
      ((∀ i, (e i).val = (e 0).val + i.val) ∨
       (∀ i, (e i).val + i.val = (e 0).val)) := by
  classical
  let e := fun i => Classical.choose (selected i)
  have hm : ∀ i, p.vertex (e i) = q.vertex i :=
    fun i => Classical.choose_spec (selected i)
  refine ⟨e,hm,index_embedding_rigid p e ?_ ?_⟩
  · intro i j h
    apply q.distinct
    rw [←hm i,←hm j,h]
  · intro i
    rw [hm,hm]
    exact (q.induced i.castSucc i.succ (by simp)).mpr (by simp)

theorem expanded_edge_count (compressed removed : Nat) (h : 0 < compressed) :
    compressed + removed - 1 = (compressed - 1) + removed := by omega

theorem closed_chain_impossible (f : Nat → Nat) (k : Nat) (hk : 2 ≤ k)
    (distinct : ∀ i j, i ≤ k → j ≤ k → f i = f j → i = j)
    (step : ∀ i, i < k → f i + 1 = f (i+1) ∨ f (i+1) + 1 = f i)
    (closing : f 0 + 1 = f k ∨ f k + 1 = f 0) : False := by
  rcases positions_rigid f k distinct step with h | h
  · have := h k (by omega)
    omega
  · have := h k (by omega)
    omega

#print axioms positions_rigid
#print axioms index_embedding_rigid
#print axioms selected_path_contiguous
#print axioms expanded_edge_count
#print axioms closed_chain_impossible
end Snake9.Contraction
