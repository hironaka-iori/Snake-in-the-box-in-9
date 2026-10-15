import SharedFiniteClassification
import SharedOuterBase
import OrdinaryEndpointCount

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sharedFiniteEdges_complete (v : Fin 7 → Coord) (hinj : Function.Injective v)
    (s : Finset Coord) (hs : s.card=2) (hsub : s⊆{v 0,v 1,v 2,v 3,v 4,v 5,v 6}) :
    s∈sharedFiniteEdges v := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hs
  have hx := hsub (by simp : x∈({x,y}:Finset Coord))
  have hy := hsub (by simp : y∈({x,y}:Finset Coord))
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [sharedFiniteEdges,finite_pair_eq_iff,hinj.eq_iff]

theorem SharedOuterConfig.finite_cases {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : SharedOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    ∃u w : Coord,u∈distinctR a b c d\{h.e,h.x,h.y} ∧
      w∈distinctR a b c d\{h.e,h.x,h.y} ∧ u≠w ∧
      SharedFiniteResidual f.F ![c,d,h.e,h.x,h.y,u,w] := by
  let C := distinctR a b c d\{h.e,h.x,h.y}
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.ordinary.outer.hab,
      h.ordinary.outer.hac,h.ordinary.outer.had,h.ordinary.outer.hbc,h.ordinary.outer.hbd,h.ordinary.outer.hcd]
  have hsub : ({h.e,h.x,h.y}:Finset Coord)⊆distinctR a b c d := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact h.he
    · exact h.hx
    · exact h.hy
  have hC : C.card=2 := by simp [C,Finset.card_sdiff hsub,hR,h.hex,h.hey,h.hxy]
  obtain ⟨u,w,huw,hCuw⟩ := Finset.card_eq_two.mp hC
  have hu : u∈C := by rw [hCuw]; simp
  have hw : w∈C := by rw [hCuw]; simp
  have huR := (Finset.mem_sdiff.mp hu).1
  have hwR := (Finset.mem_sdiff.mp hw).1
  have hun : u≠h.e ∧ u≠h.x ∧ u≠h.y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hu).2
  have hwn : w≠h.e ∧ w≠h.x ∧ w≠h.y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hw).2
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have hu' := (mem_distinctR a b c d u).mp huR
  have hw' := (mem_distinctR a b c d w).mp hwR
  let v : Fin 7 → Coord := ![c,d,h.e,h.x,h.y,u,w]
  have hinj : Function.Injective v := by
    intro i j hh
    have hcd := h.ordinary.outer.hcd
    have hex := h.hex
    have hey := h.hey
    have hxy := h.hxy
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have hRe : distinctR a b c d=sharedFiniteR v := by
    ext z
    constructor
    · intro hz
      by_cases hze : z=h.e
      · simp [sharedFiniteR,v,hze]
      by_cases hzx : z=h.x
      · simp [sharedFiniteR,v,hzx]
      by_cases hzy : z=h.y
      · simp [sharedFiniteR,v,hzy]
      have hzC : z∈C := Finset.mem_sdiff.mpr ⟨hz,by simp [hze,hzx,hzy]⟩
      rw [hCuw] at hzC
      rcases Finset.mem_insert.mp hzC with rfl | hzC
      · simp [sharedFiniteR,v]
      · have he := Finset.mem_singleton.mp hzC
        simp [sharedFiniteR,v,he]
    · intro hz
      simp only [sharedFiniteR,v,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact h.he
      · exact h.hx
      · exact h.hy
      · exact huR
      · exact hwR
  have hspan : f.F⊆sharedFiniteEdges v := by
    intro s hs
    apply sharedFiniteEdges_complete v hinj s (f.edge_card s hs)
    intro z hz
    have hzab := f.avoids s hs z hz
    by_cases hzc : z=c
    · simp [v,hzc]
    by_cases hzd : z=d
    · simp [v,hzd]
    have hzR : z∈distinctR a b c d := (mem_distinctR a b c d z).mpr ⟨hzab.1,hzab.2,hzc,hzd⟩
    rw [hRe] at hzR
    simp only [sharedFiniteR,Finset.mem_insert,Finset.mem_singleton] at hzR ⊢
    rcases hzR with hh | hh | hh | hh | hh <;> simp [hh]
  have hcount := h.ordinary.endpoint_demand_bound f
  rw [hRe,h.Aeq,h.Beq] at hcount
  have hres := shared_finite_classification v hinj f.F hFcard hspan hcount
  exact ⟨u,w,hu,hw,huw,hres⟩

#print axioms SharedOuterConfig.finite_cases
end
end Snake9
