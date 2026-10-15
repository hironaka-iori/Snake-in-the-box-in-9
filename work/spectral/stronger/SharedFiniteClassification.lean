import OrdinaryOuterCountingDefs

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem finite_pair_eq_iff {α : Type} [DecidableEq α] (a b c d : α) :
    ({a,b}:Finset α)={c,d} ↔ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  constructor
  · intro he
    have ha : a=c ∨ a=d := by simpa only [mem_insert,mem_singleton] using (show a∈({c,d}:Finset α) from he ▸ (by simp : a∈({a,b}:Finset α)))
    have hb : b=c ∨ b=d := by simpa only [mem_insert,mem_singleton] using (show b∈({c,d}:Finset α) from he ▸ (by simp : b∈({a,b}:Finset α)))
    have hc : c=a ∨ c=b := by simpa only [mem_insert,mem_singleton] using (show c∈({a,b}:Finset α) from he.symm ▸ (by simp : c∈({c,d}:Finset α)))
    have hd : d=a ∨ d=b := by simpa only [mem_insert,mem_singleton] using (show d∈({a,b}:Finset α) from he.symm ▸ (by simp : d∈({c,d}:Finset α)))
    aesop
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

theorem finite_singleton_pair_eq_iff {α : Type} [DecidableEq α] (a b c : α) :
    ({a}:Finset α)={b,c} ↔ a=b ∧ a=c := by
  have hh := finite_pair_eq_iff a a b c
  simp only [Finset.pair_eq_singleton] at hh
  rw [hh]
  tauto

def sharedFiniteR (v : Fin 7 → Coord) : Finset Coord := {v 2,v 3,v 4,v 5,v 6}
def sharedFiniteEdges (v : Fin 7 → Coord) : Finset (Finset Coord) :=
  {{v 0,v 1},{v 0,v 2},{v 0,v 3},{v 0,v 4},{v 0,v 5},{v 0,v 6},{v 1,v 2},{v 1,v 3},{v 1,v 4},{v 1,v 5},{v 1,v 6},{v 2,v 3},{v 2,v 4},{v 2,v 5},{v 2,v 6},{v 3,v 4},{v 3,v 5},{v 3,v 6},{v 4,v 5},{v 4,v 6},{v 5,v 6}}

def SharedFiniteResidual (F : Finset (Finset Coord)) (v : Fin 7 → Coord) : Prop :=
  F={{v 0,v 1},{v 0,v 2}} ∨
  F={{v 0,v 1},{v 1,v 2}} ∨
  F={{v 0,v 2},{v 1,v 2}} ∨
  F={{v 0,v 3},{v 1,v 4}} ∨
  F={{v 0,v 4},{v 1,v 3}} ∨
  F={{v 0,v 3},{v 2,v 4}} ∨
  F={{v 1,v 3},{v 2,v 4}} ∨
  F={{v 0,v 4},{v 2,v 3}} ∨
  F={{v 1,v 4},{v 2,v 3}} ∨
  F={{v 0,v 2},{v 3,v 4}} ∨
  F={{v 0,v 5},{v 3,v 4}} ∨
  F={{v 0,v 6},{v 3,v 4}} ∨
  F={{v 1,v 2},{v 3,v 4}} ∨
  F={{v 1,v 5},{v 3,v 4}} ∨
  F={{v 1,v 6},{v 3,v 4}} ∨
  F={{v 2,v 3},{v 2,v 4}} ∨
  F={{v 2,v 3},{v 3,v 4}} ∨
  F={{v 2,v 4},{v 3,v 4}} ∨
  F={{v 2,v 5},{v 3,v 4}} ∨
  F={{v 2,v 6},{v 3,v 4}}

private theorem shared_finite_row_0 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 0,v 1}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 0,v 1},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 0,v 1},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_1 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 0,v 2}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 0,v 2},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 0,v 2},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_2 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 0,v 3}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 0,v 3},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 0,v 3},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_3 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 0,v 4}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 0,v 4},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 0,v 4},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_4 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 0,v 5}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 0,v 5},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 0,v 5},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_5 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 0,v 6}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 0,v 6},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 0,v 6},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_6 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 1,v 2}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 1,v 2},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 1,v 2},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_7 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 1,v 3}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 1,v 3},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 1,v 3},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_8 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 1,v 4}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 1,v 4},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 1,v 4},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_9 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 1,v 5}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 1,v 5},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 1,v 5},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_10 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 1,v 6}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 1,v 6},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 1,v 6},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_11 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 2,v 3}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 2,v 3},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 2,v 3},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_12 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 2,v 4}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 2,v 4},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 2,v 4},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_13 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 2,v 5}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 2,v 5},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 2,v 5},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_14 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 2,v 6}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 2,v 6},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 2,v 6},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_15 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 3,v 4}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 3,v 4},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 3,v 4},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_16 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 3,v 5}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 3,v 5},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 3,v 5},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_17 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 3,v 6}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 3,v 6},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 3,v 6},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_18 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 4,v 5}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 4,v 5},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 4,v 5},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_19 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 4,v 6}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 4,v 6},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 4,v 6},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

private theorem shared_finite_row_20 (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (t : Finset Coord) (ht : t∈sharedFiniteEdges v) (hst : ({v 5,v 6}:Finset Coord)≠t)
    (hcount : ordinaryEndpointDemand {{v 5,v 6},t} (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual {{v 5,v 6},t} v := by
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [ordinaryEndpointDemand,ordinaryGoodIndices,OrdinaryGoodRow,OrdinaryPartnerClear,
    PairIsolated,OrdinaryHoleGood,sharedFiniteR,SharedFiniteResidual,Finset.filter_insert,
    Finset.filter_singleton,finite_pair_eq_iff,finite_singleton_pair_eq_iff,
    Finset.subset_iff,Finset.disjoint_left,hinj.eq_iff] at hst hcount ⊢

theorem shared_finite_classification (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (F : Finset (Finset Coord)) (hF : F.card=2) (hspan : F⊆sharedFiniteEdges v)
    (hcount : ordinaryEndpointDemand F (sharedFiniteR v) {v 2,v 3} {v 2,v 4} (v 0) (v 1)≤2) :
    SharedFiniteResidual F v := by
  obtain ⟨s,t,hst,hFst⟩ := Finset.card_eq_two.mp hF
  have hs : s∈sharedFiniteEdges v := hspan (by rw [hFst]; simp)
  have ht : t∈sharedFiniteEdges v := hspan (by rw [hFst]; simp)
  rw [hFst] at hcount ⊢
  simp only [sharedFiniteEdges,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact shared_finite_row_0 v hinj t ht hst hcount
  · exact shared_finite_row_1 v hinj t ht hst hcount
  · exact shared_finite_row_2 v hinj t ht hst hcount
  · exact shared_finite_row_3 v hinj t ht hst hcount
  · exact shared_finite_row_4 v hinj t ht hst hcount
  · exact shared_finite_row_5 v hinj t ht hst hcount
  · exact shared_finite_row_6 v hinj t ht hst hcount
  · exact shared_finite_row_7 v hinj t ht hst hcount
  · exact shared_finite_row_8 v hinj t ht hst hcount
  · exact shared_finite_row_9 v hinj t ht hst hcount
  · exact shared_finite_row_10 v hinj t ht hst hcount
  · exact shared_finite_row_11 v hinj t ht hst hcount
  · exact shared_finite_row_12 v hinj t ht hst hcount
  · exact shared_finite_row_13 v hinj t ht hst hcount
  · exact shared_finite_row_14 v hinj t ht hst hcount
  · exact shared_finite_row_15 v hinj t ht hst hcount
  · exact shared_finite_row_16 v hinj t ht hst hcount
  · exact shared_finite_row_17 v hinj t ht hst hcount
  · exact shared_finite_row_18 v hinj t ht hst hcount
  · exact shared_finite_row_19 v hinj t ht hst hcount
  · exact shared_finite_row_20 v hinj t ht hst hcount

#print axioms shared_finite_classification
end
end Snake9


