import MixedOuterBase
import EqualOuterPairCounting

namespace Snake9
open Finset Classical
noncomputable section

theorem clean_touch_unique_outside (F : Finset (Finset Coord)) (C : Finset Coord)
    (hF : F.card=2) (htouch : ∃s∈F,∃z∈s,z∈C)
    (u v : Finset Coord) (hu : u∈F) (hv : v∈F)
    (huc : Disjoint u C) (hvc : Disjoint v C) : u=v := by
  obtain ⟨s,hs,z,hzs,hzC⟩ := htouch
  obtain ⟨t,hts,ht,hFt⟩ := pair_family_other_edge F s hF hs
  have hne (w : Finset Coord) (hw : Disjoint w C) : w≠s := by
    intro he
    exact Finset.disjoint_left.mp hw (he.symm ▸ hzs) hzC
  have hut : u=t := by
    rw [hFt] at hu
    exact Finset.mem_singleton.mp ((Finset.mem_insert.mp hu).resolve_left (hne u huc))
  have hvt : v=t := by
    rw [hFt] at hv
    exact Finset.mem_singleton.mp ((Finset.mem_insert.mp hv).resolve_left (hne v hvc))
  exact hut.trans hvt.symm

theorem MixedOuterConfig.partner_alternative {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : MixedOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (htouch : ∃s∈f.F,∃z∈s,z∈distinctR a b c d\{h.i,h.j}) (k : Coord) :
    ((∀r∈distinctR a b c d,({k,r}:Finset Coord)={h.i,h.j} → ({c,r}:Finset Coord)∉f.F) ∧
     (∀r∈distinctR a b c d,({k,r}:Finset Coord)={h.i,h.j} → ({d,r}:Finset Coord)∉f.F)) ∨
    (({c,d}:Finset Coord)∉f.F ∧
     ((∀r∈distinctR a b c d,({k,r}:Finset Coord)={h.i,h.j} → ({c,r}:Finset Coord)∉f.F) ∨
      (∀r∈distinctR a b c d,({k,r}:Finset Coord)={h.i,h.j} → ({d,r}:Finset Coord)∉f.F))) := by
  let C := distinctR a b c d\{h.i,h.j}
  have hcn : c∉C := by simp [C,distinctR]
  have hdn : d∉C := by simp [C,distinctR]
  have partner (r : Coord) (he : ({k,r}:Finset Coord)={h.i,h.j}) : r∉C := by
    intro hr
    have hn := (Finset.mem_sdiff.mp hr).2
    exact hn (he ▸ (by simp : r∈({k,r}:Finset Coord)))
  have dis (x y : Coord) (hx : x∉C) (hy : y∉C) : Disjoint ({x,y}:Finset Coord) C := by
    apply Finset.disjoint_left.mpr
    intro z hz hzC
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx hzC
    · exact hy (Finset.mem_singleton.mp hz ▸ hzC)
  have forbid_cd (s r : Coord) (hr : r∈distinctR a b c d)
      (he : ({k,r}:Finset Coord)={h.i,h.j}) (hs : s=c ∨ s=d)
      (hm : ({s,r}:Finset Coord)∈f.F) : ({c,d}:Finset Coord)∉f.F := by
    intro hcd
    have hsC : s∉C := by rcases hs with rfl | rfl <;> assumption
    have heq := clean_touch_unique_outside f.F C hFcard htouch {s,r} {c,d} hm hcd
      (dis s r hsC (partner r he)) (dis c d hcn hdn)
    have hrpair : r∈({c,d}:Finset Coord) := heq ▸ (by simp : r∈({s,r}:Finset Coord))
    have hr' := (mem_distinctR a b c d r).mp hr
    rcases Finset.mem_insert.mp hrpair with hh | hh
    · exact hr'.2.2.1 hh
    · exact hr'.2.2.2 (Finset.mem_singleton.mp hh)
  by_cases hC : ∀r∈distinctR a b c d,({k,r}:Finset Coord)={h.i,h.j} → ({c,r}:Finset Coord)∉f.F
  · by_cases hD : ∀r∈distinctR a b c d,({k,r}:Finset Coord)={h.i,h.j} → ({d,r}:Finset Coord)∉f.F
    · exact Or.inl ⟨hC,hD⟩
    · push_neg at hD
      obtain ⟨r,hr,he,hm⟩ := hD
      exact Or.inr ⟨forbid_cd d r hr he (Or.inr rfl) hm,Or.inl hC⟩
  · push_neg at hC
    obtain ⟨r,hr,he,hm⟩ := hC
    refine Or.inr ⟨forbid_cd c r hr he (Or.inl rfl) hm,Or.inr ?_⟩
    intro t ht het hmt
    have heq := clean_touch_unique_outside f.F C hFcard htouch {c,r} {d,t} hm hmt
      (dis c r hcn (partner r he)) (dis d t hdn (partner t het))
    have hcpair : c∈({d,t}:Finset Coord) := heq ▸ (by simp : c∈({c,r}:Finset Coord))
    rcases Finset.mem_insert.mp hcpair with hc | hc
    · exact h.left.outer.hcd hc
    · exact ((mem_distinctR a b c d t).mp ht).2.2.1 (Finset.mem_singleton.mp hc).symm

#print axioms MixedOuterConfig.partner_alternative
end
end Snake9
