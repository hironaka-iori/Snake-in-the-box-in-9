import SingletonSquareLemma
import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Fin

namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset
open Classical
noncomputable section
set_option maxHeartbeats 2000000

abbrev AxisPair := {ab : Coord × Coord // ab.1.val < ab.2.val}

theorem axis_pair_count : Fintype.card AxisPair = 36 := by decide

def flip (a : Coord) (v : Vertex) : Vertex := vxor v (unit a)

theorem flip_twice (a : Coord) (v : Vertex) : flip a (flip a v)=v := by
  apply Fin.ext
  change (v.val ^^^ (unit a).val) ^^^ (unit a).val = v.val
  rw [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem flip_commute (a b : Coord) (v : Vertex) : flip a (flip b v)=flip b (flip a v) := by
  apply Fin.ext
  change (v.val ^^^ (unit b).val) ^^^ (unit a).val = (v.val ^^^ (unit a).val) ^^^ (unit b).val
  rw [Nat.xor_assoc,Nat.xor_assoc,Nat.xor_comm (unit b).val (unit a).val]

def flipEquiv (a : Coord) : Vertex ≃ Vertex where
  toFun := flip a
  invFun := flip a
  left_inv := flip_twice a
  right_inv := flip_twice a

theorem sum_flip (a : Coord) (f : Vertex → Nat) : (∑ v, f (flip a v)) = ∑ v, f v := by
  exact Equiv.sum_comp (flipEquiv a) f

theorem sum_flip_both (a b : Coord) (f : Vertex → Nat) :
    (∑ v, f (flip b (flip a v))) = ∑ v, f v := by
  calc
    _ = ∑ v, f (flip b v) := sum_flip a (fun v => f (flip b v))
    _ = ∑ v, f v := sum_flip b f

theorem flip_adj (a : Coord) (v : Vertex) : Adj v (flip a v) := by
  exact (adj_iff_coordinate_flip _ _).mpr ⟨a.val,a.isLt,rfl⟩

theorem flip_inj_coord (v : Vertex) {a b : Coord} (h : flip a v=flip b v) : a=b :=
  unit_injective a b (vxor_injective v h)

theorem flip_both_ne (v : Vertex) {a b : Coord} (hab : a≠b) : flip b (flip a v) ≠ v := by
  intro h
  have hh := congrArg (flip b) h
  rw [flip_twice] at hh
  exact hab (flip_inj_coord v hh)

theorem no_full_square {m : Nat} (p : Snake m) (v : Vertex) (ab : AxisPair) :
    ¬ (InPath p v ∧ InPath p (flip ab.val.1 v) ∧ InPath p (flip ab.val.2 v) ∧
        InPath p (flip ab.val.2 (flip ab.val.1 v))) := by
  rintro ⟨hv,ha,hb,hc⟩
  have hab : ab.val.1 ≠ ab.val.2 := fun h => (ne_of_lt ab.property) (congrArg Fin.val h)
  exact selected_no_four_cycle p hv ha hc hb
    (flip_adj _ _) (flip_adj _ _)
    (by rw [flip_commute]; exact adj_symmetric (flip_adj _ _))
    (adj_symmetric (flip_adj _ _))
    (Ne.symm (flip_both_ne v hab)) (fun h => hab (flip_inj_coord v h))

def selected {m : Nat} (p : Snake m) (v : Vertex) : Nat := if InPath p v then 1 else 0

def singleton {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) : Nat :=
  if InPath p v ∧ ¬ InPath p (flip ab.val.1 v) ∧ ¬ InPath p (flip ab.val.2 v) ∧
    ¬ InPath p (flip ab.val.2 (flip ab.val.1 v)) then 1 else 0

def wedge {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) : Nat :=
  if InPath p v ∧ InPath p (flip ab.val.1 v) ∧ InPath p (flip ab.val.2 v) then 1 else 0

def empty {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) : Nat :=
  if ¬ InPath p v ∧ ¬ InPath p (flip ab.val.1 v) ∧ ¬ InPath p (flip ab.val.2 v) ∧
    ¬ InPath p (flip ab.val.2 (flip ab.val.1 v)) then 1 else 0

theorem local_identity {m : Nat} (p : Snake m) (ab : AxisPair) (v : Vertex) :
    2 * empty p ab v +
    (singleton p ab v + singleton p ab (flip ab.val.1 v) + singleton p ab (flip ab.val.2 v) +
      singleton p ab (flip ab.val.2 (flip ab.val.1 v))) +
    (selected p v + selected p (flip ab.val.1 v) + selected p (flip ab.val.2 v) +
      selected p (flip ab.val.2 (flip ab.val.1 v))) =
    2 + (wedge p ab v + wedge p ab (flip ab.val.1 v) + wedge p ab (flip ab.val.2 v) +
      wedge p ab (flip ab.val.2 (flip ab.val.1 v))) := by
  classical
  have h := no_full_square p v ab
  unfold empty singleton selected wedge
  simp only [flip_twice, flip_commute ab.val.1 ab.val.2, flip_twice]
  by_cases h0 : InPath p v <;>
    by_cases h1 : InPath p (flip ab.val.1 v) <;>
    by_cases h2 : InPath p (flip ab.val.2 v) <;>
    by_cases h3 : InPath p (flip ab.val.2 (flip ab.val.1 v)) <;> simp_all


theorem summed_local_identity {m : Nat} (p : Snake m) (ab : AxisPair) :
    2 * (∑ v, empty p ab v) + 4 * (∑ v, singleton p ab v) + 4 * (∑ v, selected p v) =
      1024 + 4 * (∑ v, wedge p ab v) := by
  have h := congrArg (fun f : Vertex → Nat => ∑ v, f v)
    (funext (fun v => local_identity p ab v))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_flip_both, sum_flip,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

def totalSingleton {m : Nat} (p : Snake m) : Nat := ∑ ab : AxisPair, ∑ v, singleton p ab v
def totalWedge {m : Nat} (p : Snake m) : Nat := ∑ ab : AxisPair, ∑ v, wedge p ab v
def totalEmptyAnchored {m : Nat} (p : Snake m) : Nat := ∑ ab : AxisPair, ∑ v, empty p ab v

theorem global_identity {m : Nat} (p : Snake m) :
    2 * totalEmptyAnchored p + 4 * totalSingleton p + 144 * (∑ v, selected p v) =
      36864 + 4 * totalWedge p := by
  have h := congrArg (fun f : AxisPair → Nat => ∑ ab, f ab)
    (funext (fun ab => summed_local_identity p ab))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, axis_pair_count, smul_eq_mul] at h
  dsimp [totalSingleton,totalWedge,totalEmptyAnchored]
  omega

theorem selected_total {m : Nat} (p : Snake m) : (∑ v, selected p v)=m+1 := by
  have he : Finset.univ.filter (InPath p) = Finset.univ.image p.vertex := by
    ext v
    simp [InPath]
  unfold selected
  rw [← Finset.sum_filter, he, Finset.sum_const, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact p.distinct i j h


theorem singleton_at_vertex {m : Nat} (p : Snake m) (i : Fin (m+1)) :
    1 ≤ ∑ ab : AxisPair, singleton p ab (p.vertex i) := by
  obtain ⟨a,b,h⟩ := singleton_square_exists p i
  let ab : AxisPair := ⟨(⟨a,h.1⟩,⟨b,h.2.1⟩),h.2.2.1⟩
  have cond : InPath p (p.vertex i) ∧ ¬ InPath p (flip ab.val.1 (p.vertex i)) ∧
      ¬ InPath p (flip ab.val.2 (p.vertex i)) ∧
      ¬ InPath p (flip ab.val.2 (flip ab.val.1 (p.vertex i))) := by
    refine ⟨⟨i,rfl⟩,?_,?_,?_⟩
    · rintro ⟨j,hj⟩
      exact (h.2.2.2 j).1 (congrArg Fin.val hj)
    · rintro ⟨j,hj⟩
      exact (h.2.2.2 j).2.1 (congrArg Fin.val hj)
    · rintro ⟨j,hj⟩
      exact (h.2.2.2 j).2.2 (congrArg Fin.val hj)
  have hs : singleton p ab (p.vertex i)=1 := if_pos cond
  rw [← hs]
  exact Finset.single_le_sum (fun ab _ => Nat.zero_le (singleton p ab (p.vertex i))) (Finset.mem_univ ab)

theorem singleton_total_lower {m : Nat} (p : Snake m) : m+1 ≤ totalSingleton p := by
  have local_bound (v : Vertex) : selected p v ≤ ∑ ab : AxisPair, singleton p ab v := by
    by_cases hv : InPath p v
    · obtain ⟨i,rfl⟩ := hv
      rw [selected,if_pos ⟨i,rfl⟩]
      exact singleton_at_vertex p i
    · simp [selected,hv]
  calc
    m+1 = ∑ v, selected p v := (selected_total p).symm
    _ ≤ ∑ v : Vertex, ∑ ab : AxisPair, singleton p ab v := Finset.sum_le_sum (fun v _ => local_bound v)
    _ = totalSingleton p := by unfold totalSingleton; rw [Finset.sum_comm]


theorem wedge_unique {m : Nat} (p : Snake m) (v : Vertex) (ab cd : AxisPair)
    (h : InPath p v ∧ InPath p (flip ab.val.1 v) ∧ InPath p (flip ab.val.2 v))
    (g : InPath p v ∧ InPath p (flip cd.val.1 v) ∧ InPath p (flip cd.val.2 v)) : ab=cd := by
  have hab : ab.val.1 ≠ ab.val.2 := fun h => (ne_of_lt ab.property) (congrArg Fin.val h)
  have cover (c : Coord) (hc : InPath p (flip c v)) : c=ab.val.1 ∨ c=ab.val.2 := by
    rcases selected_three_neighbors_repeat p h.1 h.2.1 h.2.2 hc
      (flip_adj _ _) (flip_adj _ _) (flip_adj _ _) with he | he | he
    · exact False.elim (hab (flip_inj_coord v he))
    · exact Or.inl (flip_inj_coord v he).symm
    · exact Or.inr (flip_inj_coord v he).symm
  have h1 := cover cd.val.1 g.2.1
  have h2 := cover cd.val.2 g.2.2
  have h1v : cd.val.1.val=ab.val.1.val ∨ cd.val.1.val=ab.val.2.val :=
    h1.imp (congrArg Fin.val) (congrArg Fin.val)
  have h2v : cd.val.2.val=ab.val.1.val ∨ cd.val.2.val=ab.val.2.val :=
    h2.imp (congrArg Fin.val) (congrArg Fin.val)
  have ho := ab.property
  have hp := cd.property
  apply Subtype.ext
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

def internalIndices (m : Nat) : Finset (Fin (m+1)) := Finset.Ioo 0 (Fin.last m)
def internalSet {m : Nat} (p : Snake m) : Finset Vertex := (internalIndices m).image p.vertex

theorem internal_count {m : Nat} (p : Snake m) : (internalSet p).card=m-1 := by
  rw [internalSet,Finset.card_image_of_injective]
  · simp [internalIndices,Fin.card_Ioo]
  · intro i j h
    exact p.distinct i j h

theorem wedge_internal {m : Nat} (p : Snake m) (v : Vertex) (ab : AxisPair)
    (h : InPath p v ∧ InPath p (flip ab.val.1 v) ∧ InPath p (flip ab.val.2 v)) :
    v ∈ internalSet p := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩⟩ := h
  have ha : Adj (p.vertex i) (p.vertex j) := by rw [hi,hj]; exact flip_adj _ _
  have hb : Adj (p.vertex i) (p.vertex k) := by rw [hi,hk]; exact flip_adj _ _
  have hjk : j.val ≠ k.val := by
    intro he
    have hv := hj.symm.trans ((congrArg p.vertex (Fin.ext he)).trans hk)
    have hc := congrArg Fin.val (flip_inj_coord v hv)
    have ho := ab.property
    omega
  have hia := (path_adj_iff p i j).mp ha
  have hib := (path_adj_iff p i k).mp hb
  have h0 : 0 < i.val := by omega
  have hm : i.val < m := by omega
  apply Finset.mem_image.mpr
  refine ⟨i,?_,hi⟩
  exact Finset.mem_Ioo.mpr ⟨h0,hm⟩

theorem wedge_at_vertex_le {m : Nat} (p : Snake m) (v : Vertex) :
    (∑ ab : AxisPair, wedge p ab v) ≤ if v ∈ internalSet p then 1 else 0 := by
  let W := Finset.univ.filter (fun ab : AxisPair =>
    InPath p v ∧ InPath p (flip ab.val.1 v) ∧ InPath p (flip ab.val.2 v))
  have he : (∑ ab : AxisPair, wedge p ab v)=W.card := by
    simp only [wedge,W,Finset.card_filter]
  rw [he]
  by_cases hv : v ∈ internalSet p
  · rw [if_pos hv]
    apply Finset.card_le_one.mpr
    intro ab hab cd hcd
    exact wedge_unique p v ab cd (Finset.mem_filter.mp hab).2 (Finset.mem_filter.mp hcd).2
  · rw [if_neg hv]
    have hW : W=∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro ab hab
      exact hv (wedge_internal p v ab (Finset.mem_filter.mp hab).2)
    simp [hW]

theorem wedge_total_upper {m : Nat} (p : Snake m) : totalWedge p ≤ m-1 := by
  calc
    totalWedge p = ∑ v : Vertex, ∑ ab : AxisPair, wedge p ab v := by
      unfold totalWedge
      rw [Finset.sum_comm]
    _ ≤ ∑ v : Vertex, if v ∈ internalSet p then 1 else 0 :=
      Finset.sum_le_sum (fun v _ => wedge_at_vertex_le p v)
    _ = (internalSet p).card := by simp
    _ = m-1 := internal_count p

theorem universal_upper_bound_254 {m : Nat} (p : Snake m) : m≤254 := by
  have hid := global_identity p
  rw [selected_total p] at hid
  have hs := singleton_total_lower p
  have hw := wedge_total_upper p
  omega

theorem verified_bounds_254 : Nonempty (Snake 191) ∧ (∀ m, Nonempty (Snake m) → m≤254) :=
  ⟨lower_bound,fun _ ⟨p⟩ => universal_upper_bound_254 p⟩

#print axioms universal_upper_bound_254
#print axioms verified_bounds_254
#print axioms singleton_total_lower
#print axioms local_identity
#print axioms global_identity
#print axioms selected_total
end
end Snake9.SquareIncidence
