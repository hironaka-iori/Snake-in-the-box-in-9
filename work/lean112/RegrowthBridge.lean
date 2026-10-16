import PathStructure
import BallClauseLogic
import DfsPrefix
import DfsParity

namespace Snake9.Regrowth
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def suffix (p : Snake 192) : Snake 81 where
  vertex i := p.vertex ⟨111+i.val, by omega⟩
  distinct i j h := by
    have he := congrArg Fin.val (p.distinct _ _ h)
    apply Fin.ext
    simp only at he
    omega
  induced i j hij := by
    have h := p.induced ⟨111+i.val, by omega⟩ ⟨111+j.val, by omega⟩ (by simp; omega)
    rw [h]
    simp only
    omega

theorem endpoint_iff {m : Nat} (p : Snake m) (v : Vertex) :
    BallClauseLogic.Endpoint p v ↔ v = p.vertex 0 ∨ v = p.vertex (Fin.last m) := by
  constructor
  · rintro ⟨⟨i,rfl⟩,hi⟩
    rcases low_degree_index_is_endpoint p i hi with h | h
    · left; exact congrArg p.vertex (Fin.ext h)
    · right; exact congrArg p.vertex (Fin.ext h)
  · intro h
    rcases h with rfl | rfl
    · refine ⟨⟨0,rfl⟩,?_⟩
      rintro a b ⟨i,rfl⟩ ⟨j,rfl⟩ ha hb
      have hi := (path_adj_iff p 0 i).mp ha
      have hj := (path_adj_iff p 0 j).mp hb
      apply congrArg p.vertex
      apply Fin.ext
      simp only [Fin.val_zero] at hi hj
      omega
    · refine ⟨⟨Fin.last m,rfl⟩,?_⟩
      rintro a b ⟨i,rfl⟩ ⟨j,rfl⟩ ha hb
      have hi := (path_adj_iff p (Fin.last m) i).mp ha
      have hj := (path_adj_iff p (Fin.last m) j).mp hb
      apply congrArg p.vertex
      apply Fin.ext
      simp only [Fin.val_last] at hi hj
      omega

theorem neighbor_exists {m : Nat} (p : Snake m) (hm : 0 < m)
    (v : Vertex) (hv : InPath p v) : ∃ w, InPath p w ∧ Adj v w := by
  obtain ⟨i,rfl⟩ := hv
  by_cases hi : i.val < m
  · exact ⟨p.vertex ⟨i.val+1,by omega⟩,⟨_,rfl⟩,
      (path_adj_iff p _ _).mpr (Or.inl rfl)⟩
  · refine ⟨p.vertex ⟨i.val-1,by omega⟩,⟨_,rfl⟩,?_⟩
    apply (path_adj_iff p _ _).mpr
    right; simp only; omega

theorem neighbor_cover {m : Nat} (p : Snake m) (hm : 0 < m) (v : Vertex)
    (ns : List Vertex) (hc : ∀ w, InPath p w → Adj v w → w ∈ ns) :
    ¬ InPath p v ∨ ∃ w ∈ ns, InPath p w := by
  classical
  by_cases hv : InPath p v
  · obtain ⟨w,hw,ha⟩ := neighbor_exists p hm v hv
    exact Or.inr ⟨w,hc w hw ha,hw⟩
  · exact Or.inl hv

theorem other_cover {m : Nat} (p : Snake m) (v excluded : Vertex)
    (ns : List Vertex) (hc : ∀ w, InPath p w → Adj v w → w ≠ excluded → w ∈ ns) :
    ¬ InPath p v ∨ BallClauseLogic.Endpoint p v ∨ ∃ w ∈ ns, InPath p w := by
  classical
  by_cases hv : InPath p v
  · rcases BallClauseLogic.other_neighbor_or_low p v excluded with h | ⟨w,he,hw,ha⟩
    · exact Or.inr (Or.inl ⟨hv,h⟩)
    · exact Or.inr (Or.inr ⟨w,hc w hw ha he,hw⟩)
  · exact Or.inl hv

theorem nodup_subset_length {α : Type} [DecidableEq α] (xs ys : List α)
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction ys generalizing xs with
  | nil => have : xs = [] := List.subset_nil.mp hs; simp [this]
  | cons a ys ih =>
    by_cases ha : a ∈ xs
    · have he := List.length_erase_of_mem ha
      have hb := ih (xs.erase a) (hn.erase a) (by
        intro v hv
        obtain ⟨hne,hv⟩ := hn.mem_erase_iff.mp hv
        rcases List.mem_cons.mp (hs hv) with h | h
        · exact False.elim (hne h)
        · exact h)
      have hp := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega
    · have hb := ih xs hn (by
        intro v hv
        rcases List.mem_cons.mp (hs hv) with h | h
        · exact False.elim (ha (h ▸ hv))
        · exact h)
      simp only [List.length_cons]; omega

theorem path_nodup {m : Nat} (p : Snake m) : (List.ofFn p.vertex).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  simp only [List.getElem_ofFn] at he
  have he := congrArg Fin.val (p.distinct _ _ he)
  simp only at he
  omega

theorem map_ofFn {α β : Type} {n : Nat} (f : Fin n → α) (g : α → β) :
    (List.ofFn f).map g = List.ofFn (fun i => g (f i)) := by
  apply List.ext_get
  · simp
  · intro i hi hj; simp

theorem odd_count (p : Snake 81) :
    ((List.ofFn p.vertex).filter (fun v => bitParity v.val)).length = 41 := by
  rw [← List.countP_eq_length_filter]
  have he : (List.ofFn p.vertex).map (fun v => bitParity v.val) =
      List.ofFn (fun i : Fin 82 => bitParity (p.vertex 0).val ^^ (i.val % 2 == 1)) := by
    rw [map_ofFn]
    congr 1
    funext i
    exact parity_along p i.val (by omega)
  have hc : (List.ofFn p.vertex).countP (fun v => bitParity v.val) =
      ((List.ofFn p.vertex).map (fun v => bitParity v.val)).countP id := by
    rw [List.countP_map]
    rfl
  rw [hc,he]
  cases bitParity (p.vertex 0).val <;> decide

theorem filter_partition {α : Type} (xs : List α) (f : α → Bool) :
    (xs.filter f).length + (xs.filter (fun a => !f a)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : f a <;> simp [List.filter_cons,h] <;> omega

theorem absent_bound (p : Snake 81) (side : List Vertex)
    (hcover : ∀ v, InPath p v → bitParity v.val = true → v ∈ side) :
    (side.filter (fun v => !(decide (InPath p v)))).length ≤ side.length - 41 := by
  classical
  have hn := (path_nodup p).sublist (List.filter_sublist (p := fun v => bitParity v.val))
  have hc : ((List.ofFn p.vertex).filter (fun v => bitParity v.val)) ⊆
      side.filter (fun v => decide (InPath p v)) := by
    intro v hv
    obtain ⟨hv,hpar⟩ := List.mem_filter.mp hv
    have hp : InPath p v := List.mem_ofFn.mp hv
    exact List.mem_filter.mpr ⟨hcover v hp hpar,by simp [hp]⟩
  have hb := nodup_subset_length _ _ hn hc
  rw [odd_count] at hb
  have he := filter_partition side (fun v => decide (InPath p v))
  omega

theorem endpoint_count (p : Snake 81) (others : List Vertex) (hn : others.Nodup)
    (hh : p.vertex 0 ∉ others) :
    (others.filter (fun v => decide (BallClauseLogic.Endpoint p v))).length ≤ 1 := by
  classical
  apply Nat.le_trans (nodup_subset_length _ [p.vertex (Fin.last 81)]
    (hn.sublist (List.filter_sublist)) ?_) (by simp only [List.length_cons,List.length_nil]; omega)
  intro v hv
  obtain ⟨hm,he⟩ := List.mem_filter.mp hv
  have he : BallClauseLogic.Endpoint p v := of_decide_eq_true he
  rcases (endpoint_iff p v).mp he with h | h
  · exact False.elim (hh (h ▸ hm))
  · simp [h]

theorem endpoint_parity_exclude (p : Snake 81) (v : Vertex)
    (hne : v ≠ p.vertex 0) (hpar : bitParity v.val = bitParity (p.vertex 0).val) :
    ¬ BallClauseLogic.Endpoint p v := by
  intro he
  rcases (endpoint_iff p v).mp he with h | h
  · exact hne h
  · have hp := endpoint_parity p
    rw [h] at hpar
    rw [hp] at hpar
    cases hbit : bitParity (p.vertex 0).val <;> simp [hbit] at hpar

theorem other_endpoint (p : Snake 81) (others : List Vertex)
    (hc : ∀ v, InPath p v → v ≠ p.vertex 0 → v ∈ others) :
    ∃ v ∈ others, BallClauseLogic.Endpoint p v := by
  refine ⟨p.vertex (Fin.last 81), hc _ ⟨_,rfl⟩ ?_, ?_⟩
  · intro he
    have he := congrArg Fin.val (p.distinct _ _ he)
    contradiction
  · exact (endpoint_iff p _).mpr (Or.inr rfl)

def literal (p : Nat → Bool) (z : Int) : Bool :=
  if z > 0 then p z.toNat else !p (-z).toNat

theorem square_clause {m : Nat} (p : Snake m) (a b c d : Vertex)
    (hab : Adj a b) (hbd : Adj b d) (hdc : Adj d c) (hca : Adj c a)
    (had : a ≠ d) (hbc : b ≠ c) :
    ¬ InPath p a ∨ ¬ InPath p b ∨ ¬ InPath p c ∨ ¬ InPath p d := by
  classical
  by_cases ha : InPath p a
  · by_cases hb : InPath p b
    · by_cases hc : InPath p c
      · exact Or.inr (Or.inr (Or.inr (fun hd =>
          selected_no_four_cycle p ha hb hd hc hab hbd hdc hca had hbc)))
      · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inl hb)
  · exact Or.inl ha

theorem merge_two (a b c : Bool) (A B C i j : Nat)
    (ha : a = decide (i ≤ A)) (hb : b = decide (j ≤ B))
    (hc : c = decide (i+j ≤ C)) (hs : C = A+B) :
    a = false ∨ b = false ∨ c = true := by
  rw [ha,hb,hc]
  simp only [decide_eq_true_eq,decide_eq_false_iff_not]
  omega

theorem merge_left (a c : Bool) (A B C i : Nat)
    (ha : a = decide (i ≤ A)) (hc : c = decide (i ≤ C))
    (hs : C = A+B) : a = false ∨ c = true := by
  rw [ha,hc]
  simp only [decide_eq_true_eq,decide_eq_false_iff_not]
  omega

theorem merge_right (b c : Bool) (A B C j : Nat)
    (hb : b = decide (j ≤ B)) (hc : c = decide (j ≤ C))
    (hs : C = A+B) : b = false ∨ c = true := by
  rw [hb,hc]
  simp only [decide_eq_true_eq,decide_eq_false_iff_not]
  omega

end
end Snake9.Regrowth
