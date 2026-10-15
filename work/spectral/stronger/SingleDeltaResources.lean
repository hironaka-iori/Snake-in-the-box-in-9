import MiddleMatchingGeometry

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1000000

/-- Two distinct selected neighbors consume distinct members of a two-element family. -/
theorem two_neighbors_exhaust_resources {m : Nat} (p : Snake m)
    (F : Finset (Finset Coord)) (hF : F.card=2) (v : Vertex)
    (hn : ¬AtMostOneNeighbor p v) (P : Finset Coord → Prop)
    (R : Vertex → Finset Coord → Prop)
    (cover : ∀w,InPath p w → Adj v w → ∃s∈F,P s ∧ R w s)
    (unique : ∀w z s,R w s → R z s → w=z) : ∀s∈F,P s := by
  unfold AtMostOneNeighbor at hn
  push_neg at hn
  obtain ⟨w,z,hw,hz,ha,hb,hne⟩ := hn
  obtain ⟨s,hs,hps,hrs⟩ := cover w hw ha
  obtain ⟨t,ht,hpt,hrt⟩ := cover z hz hb
  have hst : s≠t := by
    intro he
    subst t
    exact hne (unique w z s hrs hrt)
  have he : F={s,t} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hs
      · exact ht
    · simpa [hst] using hF.le
  intro e he'
  rw [he] at he'
  simp only [Finset.mem_insert,Finset.mem_singleton] at he'
  rcases he' with rfl | rfl
  · exact hps
  · exact hpt

def SingleDeltaResource (c d k : Coord) (s : Finset Coord) : Prop :=
  k∈s ∨ s={c,d}

def SingleDeltaResourceUse (a c d k : Coord) (w : Vertex) (s : Finset Coord) : Prop :=
  (w=quad a c k d ∧ (s={c,d} ∨ s={d,k})) ∨
  ∃r,r≠c ∧ r≠d ∧ r≠k ∧ s={k,r} ∧ w=quad a c k r

theorem single_delta_resource_use_unique (a c d k : Coord) (hkc : k≠c) (hkd : k≠d)
    (w z : Vertex) (s : Finset Coord)
    (hw : SingleDeltaResourceUse a c d k w s) (hz : SingleDeltaResourceUse a c d k z s) : w=z := by
  rcases hw with ⟨hw,hs⟩ | ⟨r,hrc,hrd,hrk,hs,hw⟩
  · rcases hz with ⟨hz,_⟩ | ⟨r,hrc,hrd,hrk,ht,hz⟩
    · exact hw.trans hz.symm
    · rcases hs with hs | hs
      · have hh : k=c ∨ k=d := by
          have hm : k∈({c,d}:Finset Coord) := (ht.symm.trans hs) ▸ (by simp : k∈({k,r}:Finset Coord))
          simpa using hm
        exact False.elim (hh.elim hkc hkd)
      · have hh : r=d ∨ r=k := by
          have hm : r∈({d,k}:Finset Coord) := (ht.symm.trans hs) ▸ (by simp : r∈({k,r}:Finset Coord))
          simpa using hm
        exact False.elim (hh.elim hrd hrk)
  · rcases hz with ⟨hz,ht⟩ | ⟨t,htc,htd,htk,ht,hz⟩
    · rcases ht with ht | ht
      · have hh : k=c ∨ k=d := by
          have hm : k∈({c,d}:Finset Coord) := (hs.symm.trans ht) ▸ (by simp : k∈({k,r}:Finset Coord))
          simpa using hm
        exact False.elim (hh.elim hkc hkd)
      · have hh : r=d ∨ r=k := by
          have hm : r∈({d,k}:Finset Coord) := (hs.symm.trans ht) ▸ (by simp : r∈({k,r}:Finset Coord))
          simpa using hm
        exact False.elim (hh.elim hrd hrk)
    · have hh : r=k ∨ r=t := by
        have hm : r∈({k,t}:Finset Coord) := (hs.symm.trans ht) ▸ (by simp : r∈({k,r}:Finset Coord))
        simpa using hm
      have hrt := hh.resolve_left hrk
      exact hw.trans ((congrArg (quad a c k) hrt).trans hz.symm)

#print axioms two_neighbors_exhaust_resources
#print axioms single_delta_resource_use_unique
end
end Snake9
