import SingletonSquareLemma
import Mathlib.Tactic

namespace Snake9.LowSingletonArms
open Classical Finset
set_option maxHeartbeats 2000000

/-- Every nonexceptional pair of coordinates outside the two root directions is selected. -/
def ForcedExcept {m : Nat} (p : Snake m) (a b u v : Coord) : Prop :=
  ∀ i j : Coord, i≠a → i≠b → j≠a → j≠b → i≠j →
    ((i≠u ∧ i≠v) ∨ (j≠u ∧ j≠v)) → InPath p (pair i j)

def Internal {m : Nat} (p : Snake m) (v : Vertex) : Prop :=
  ∃ k, p.vertex k=v ∧ 0<k.val ∧ k.val<m

theorem internal_not_low {m : Nat} (p : Snake m) {v : Vertex} (h : Internal p v) :
    ¬ AtMostOneNeighbor p v := by
  obtain ⟨k,rfl,h0,hm⟩ := h
  intro hl
  have he := low_degree_index_is_endpoint p k hl
  omega

theorem four_avoid_two (f : Fin 4 → Coord) (hf : Function.Injective f) (u v : Coord) :
    ∃ k l, k≠l ∧ f k≠u ∧ f k≠v ∧ f l≠u ∧ f l≠v := by
  have hcard : (Finset.univ.image f).card=4 := by rw [Finset.card_image_of_injective _ hf]; simp
  have first : ∃ k, f k≠u ∧ f k≠v := by
    by_contra hn
    have sub : Finset.univ.image f ⊆ {u,v} := by
      intro x hx
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
      by_cases hu : f k=u
      · simp [hu]
      · have hv : f k=v := by by_contra hv; exact hn ⟨k,hu,hv⟩
        simp [hv]
    have hc := Finset.card_le_card sub
    have hb : ({u,v} : Finset Coord).card≤2 := by
      have hh := Finset.card_insert_le u ({v} : Finset Coord)
      simpa using hh
    omega
  obtain ⟨k,hku,hkv⟩ := first
  by_contra hn
  have sub : Finset.univ.image f ⊆ {u,v,f k} := by
    intro x hx
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases hu : f l=u
    · simp [hu]
    by_cases hv : f l=v
    · simp [hv]
    by_cases hkl : k=l
    · simp [hkl]
    · exact False.elim (hn ⟨k,l,hkl,hku,hkv,hu,hv⟩)
  have hc := Finset.card_le_card sub
  have hb : ({u,v,f k} : Finset Coord).card≤3 := by
    have := Finset.card_insert_le u ({v,f k} : Finset Coord)
    have hh := Finset.card_insert_le v ({f k} : Finset Coord)
    simp only [Finset.card_singleton] at hh
    omega
  omega

theorem outside_pair_low {m : Nat} (p : Snake m)
    (a b u v i j : Coord) (hia : i≠a) (hib : i≠b) (hja : j≠a) (hjb : j≠b) (hij : i≠j)
    (hi : i≠u ∧ i≠v) (hj : j≠u ∧ j≠v)
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedExcept p a b u v) (missing : ¬ InPath p (triple a i j)) :
    AtMostOneNeighbor p (pair i j) := by
  have absent (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
    intro hk
    rcases cover k hk with h | h
    · exact hka h
    · exact hkb h
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair i j) w) : w=triple i j b := by
    obtain ⟨k,rfl⟩ := neighbor_pair i j hadj
    by_cases hki : k=i
    · subst k
      rw [triple_cancel_left] at hw
      exact False.elim (absent j hja hjb hw)
    by_cases hkj : k=j
    · subst k
      rw [triple_cancel_right] at hw
      exact False.elim (absent i hia hib hw)
    by_cases hka : k=a
    · subst k
      rw [triple_rotate] at hw
      exact False.elim (missing hw)
    by_cases hkb : k=b
    · exact congrArg (triple i j) hkb
    exact False.elim (selected_triple_forbidden p i j k hij (Ne.symm hki) (Ne.symm hkj)
      (forced i j hia hib hja hjb hij (Or.inl hi))
      (forced i k hia hib hka hkb (Ne.symm hki) (Or.inl hi))
      (forced j k hja hjb hka hkb (Ne.symm hkj) (Or.inl hj)) hw)
  intro w z hw hz haw haz
  exact (unique w hw haw).trans (unique z hz haz).symm

theorem arm_uses_exception {m : Nat} (p : Snake m) (a b u v i : Coord)
    (hia : i≠a) (hib : i≠b) (ha : InPath p (unit a)) (hc : InPath p (pair a i))
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedExcept p a b u v)
    (interior : ∀ j k : Coord, j≠a → j≠b → k≠a → k≠b → j≠k →
      InPath p (pair j k) → Internal p (pair j k)) : i=u ∨ i=v := by
  by_contra hn
  have hi : i≠u ∧ i≠v := ⟨fun h => hn (Or.inl h),fun h => hn (Or.inr h)⟩
  let f := freshCoords a b i
  have outside := (freshCoords_spec a b i).1
  have inj := (freshCoords_spec a b i).2
  obtain ⟨k,l,hkl,hku,hkv,hlu,hlv⟩ := four_avoid_two f inj u v
  have selected (t : Fin 4) (htu : f t≠u) (htv : f t≠v) : InPath p (triple a i (f t)) := by
    by_contra hmiss
    have hp := forced i (f t) hia hib (outside t).1 (outside t).2.1 (Ne.symm (outside t).2.2) (Or.inl hi)
    have hint := interior i (f t) hia hib (outside t).1 (outside t).2.1 (Ne.symm (outside t).2.2) hp
    exact internal_not_low p hint (outside_pair_low p a b u v i (f t) hia hib
      (outside t).1 (outside t).2.1 (Ne.symm (outside t).2.2) hi ⟨htu,htv⟩ cover forced hmiss)
  rcases selected_three_neighbors_repeat p hc ha (selected k hku hkv) (selected l hlu hlv)
    (adj_symmetric (unit_pair_adj a i)) (pair_triple_adj a i (f k)) (pair_triple_adj a i (f l)) with h | h | h
  · exact triple_ne_unit a i (f k) (Ne.symm (outside k).2.2) h.symm
  · exact triple_ne_unit a i (f l) (Ne.symm (outside l).2.2) h.symm
  · exact hkl (inj k l (triple_injective_right a i (f k) (f l) h))


theorem one_exception_pair_low {m : Nat} (p : Snake m) (a b u v j : Coord)
    (hua : u≠a) (hub : u≠b) (hja : j≠a) (hjb : j≠b) (hju : j≠u) (hjv : j≠v)
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedExcept p a b u v)
    (ma : ¬ InPath p (triple a u j)) (mb : ¬ InPath p (triple b u j)) :
    AtMostOneNeighbor p (pair u j) := by
  have absent (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
    intro hk
    rcases cover k hk with h | h
    · exact hka h
    · exact hkb h
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair u j) w) : w=triple u j v := by
    obtain ⟨k,rfl⟩ := neighbor_pair u j hadj
    by_cases hku : k=u
    · subst k
      rw [triple_cancel_left] at hw
      exact False.elim (absent j hja hjb hw)
    by_cases hkj : k=j
    · subst k
      rw [triple_cancel_right] at hw
      exact False.elim (absent u hua hub hw)
    by_cases hka : k=a
    · subst k
      rw [triple_rotate] at hw
      exact False.elim (ma hw)
    by_cases hkb : k=b
    · subst k
      rw [triple_rotate] at hw
      exact False.elim (mb hw)
    by_cases hkv : k=v
    · exact congrArg (triple u j) hkv
    exact False.elim (selected_triple_forbidden p u j k (Ne.symm hju) (Ne.symm hku) (Ne.symm hkj)
      (forced u j hua hub hja hjb (Ne.symm hju) (Or.inr ⟨hju,hjv⟩))
      (forced u k hua hub hka hkb (Ne.symm hku) (Or.inr ⟨hku,hkv⟩))
      (forced j k hja hjb hka hkb (Ne.symm hkj) (Or.inl ⟨hju,hjv⟩)) hw)
  intro w z hw hz haw haz
  exact (unique w hw haw).trans (unique z hz haz).symm

theorem same_exception_arm_impossible {m : Nat} (p : Snake m) (a b u v : Coord)
    (hua : u≠a) (hub : u≠b) (ha : InPath p (unit a)) (hb : InPath p (unit b))
    (hca : InPath p (pair a u)) (hcb : InPath p (pair b u))
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedExcept p a b u v)
    (interior : ∀ j k : Coord, j≠a → j≠b → k≠a → k≠b → j≠k →
      InPath p (pair j k) → Internal p (pair j k)) : False := by
  let f := freshCoords a b u
  have outside := (freshCoords_spec a b u).1
  have inj := (freshCoords_spec a b u).2
  let A := Finset.univ.filter (fun k : Fin 4 => InPath p (triple a u (f k)))
  let B := Finset.univ.filter (fun k : Fin 4 => InPath p (triple b u (f k)))
  let V := Finset.univ.filter (fun k : Fin 4 => f k=v)
  have capacity (c : Coord) (hc : InPath p (unit c)) (hpc : InPath p (pair c u)) :
      (Finset.univ.filter (fun k : Fin 4 => InPath p (triple c u (f k)))).card≤1 := by
    apply Finset.card_le_one.mpr
    intro k hk l hl
    rcases selected_three_neighbors_repeat p hpc hc (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2
      (adj_symmetric (unit_pair_adj c u)) (pair_triple_adj c u (f k)) (pair_triple_adj c u (f l)) with h | h | h
    · exact False.elim (triple_ne_unit c u (f k) (Ne.symm (outside k).2.2) h.symm)
    · exact False.elim (triple_ne_unit c u (f l) (Ne.symm (outside l).2.2) h.symm)
    · exact inj k l (triple_injective_right c u (f k) (f l) h)
  have ca : A.card≤1 := capacity a ha hca
  have cb : B.card≤1 := capacity b hb hcb
  have cv : V.card≤1 := by
    apply Finset.card_le_one.mpr
    intro k hk l hl
    exact inj k l ((Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm)
  have all : (Finset.univ : Finset (Fin 4)) ⊆ A ∪ B ∪ V := by
    intro k _
    by_cases hv : f k=v
    · simp [A,B,V,hv]
    by_cases hqa : InPath p (triple a u (f k))
    · simp [A,B,V,hqa]
    by_cases hqb : InPath p (triple b u (f k))
    · simp [A,B,V,hqb]
    have hp := forced u (f k) hua hub (outside k).1 (outside k).2.1 (Ne.symm (outside k).2.2)
      (Or.inr ⟨(outside k).2.2,hv⟩)
    have hint := interior u (f k) hua hub (outside k).1 (outside k).2.1 (Ne.symm (outside k).2.2) hp
    exact False.elim (internal_not_low p hint (one_exception_pair_low p a b u v (f k)
      hua hub (outside k).1 (outside k).2.1 (outside k).2.2 hv cover forced hqa hqb))
  have hcard := Finset.card_le_card all
  have h1 := Finset.card_union_le A B
  have h2 := Finset.card_union_le (A ∪ B) V
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  omega

theorem forced_swap_root {m : Nat} (p : Snake m) (a b u v : Coord)
    (h : ForcedExcept p a b u v) : ForcedExcept p b a u v := by
  intro i j h1 h2 h3 h4 h5 h6
  exact h i j h2 h1 h4 h3 h5 h6

theorem forced_swap_exception {m : Nat} (p : Snake m) (a b u v : Coord)
    (h : ForcedExcept p a b u v) : ForcedExcept p a b v u := by
  intro i j h1 h2 h3 h4 h5 h6
  exact h i j h1 h2 h3 h4 h5 (h6.imp And.symm And.symm)

theorem arms_split_exception {m : Nat} (p : Snake m) (a b u v i j : Coord)
    (hia : i≠a) (hib : i≠b) (hja : j≠a) (hjb : j≠b)
    (ha : InPath p (unit a)) (hb : InPath p (unit b))
    (hca : InPath p (pair a i)) (hcb : InPath p (pair b j))
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedExcept p a b u v)
    (interior : ∀ s t : Coord, s≠a → s≠b → t≠a → t≠b → s≠t →
      InPath p (pair s t) → Internal p (pair s t)) :
    (i=u ∧ j=v) ∨ (i=v ∧ j=u) := by
  have hi := arm_uses_exception p a b u v i hia hib ha hca cover forced interior
  have hj := arm_uses_exception p b a u v j hjb hja hb hcb
    (fun k hk => (cover k hk).symm) (forced_swap_root p a b u v forced)
    (fun s t h1 h2 h3 h4 h5 h6 => interior s t h2 h1 h4 h3 h5 h6)
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · subst i; subst j
    exact False.elim (same_exception_arm_impossible p a b u v hia hib ha hb hca hcb cover forced interior)
  · exact Or.inl ⟨hi,hj⟩
  · exact Or.inr ⟨hi,hj⟩
  · subst i; subst j
    exact False.elim (same_exception_arm_impossible p a b v u hia hib ha hb hca hcb cover
      (forced_swap_exception p a b u v forced) interior)

#print axioms same_exception_arm_impossible
#print axioms arms_split_exception
#print axioms arm_uses_exception
end Snake9.LowSingletonArms
