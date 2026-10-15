import LocalDenseRows
import CommonHolePairs

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

structure StarLeftConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  e : Coord
  he : e∈distinctR a b c d
  left_eq : outer.left.F={{b,d},{d,e}}

namespace StarLeftConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : StarLeftConfig p a b c d)
include h

theorem ordinary_pair (i j : Coord) (hi : i∈distinctR a b c d)
    (hj : j∈distinctR a b c d) (hij : i≠j) : InPath p (pair i j) := by
  obtain ⟨hia,hib,hic,hid⟩ := (mem_distinctR a b c d i).mp hi
  obtain ⟨hja,hjb,hjc,hjd⟩ := (mem_distinctR a b c d j).mp hj
  apply (h.outer.left.selected_iff i j hij hia hic hja hjc).mpr
  rw [h.left_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  constructor
  · exact delta_pair_ne i j b d hib hid
  · intro he
    have hm : d∈({i,j}:Finset Coord) := he.symm ▸ (by simp : d∈({d,h.e}:Finset Coord))
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    exact hm.elim (Ne.symm hid) (Ne.symm hjd)

theorem row_selected (k : Coord) (hk : k∈distinctR a b c d) : InPath p (pair b k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have he := (mem_distinctR a b c d h.e).mp h.he
  apply (h.outer.left.selected_iff b k (Ne.symm hkb) (Ne.symm h.outer.hab) h.outer.hbc hka hkc).mpr
  rw [h.left_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨delta_pair_ne_right b k b d hkb hkd,delta_pair_ne b k d h.e h.outer.hbd (Ne.symm he.2.1)⟩

theorem side_pair (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) : InPath p (pair d k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  apply (h.outer.left.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
    (Ne.symm h.outer.hcd) hka hkc).mpr
  rw [h.left_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨delta_pair_ne_right d k b d hkb hkd,delta_pair_ne_right d k d h.e hkd hke⟩

theorem ordinary_b_absent (i j : Coord) (hi : i∈distinctR a b c d)
    (hj : j∈distinctR a b c d) (hij : i≠j) : ¬InPath p (triple b i j) := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  exact selected_triple_forbidden p b i j (Ne.symm hhi.2.1) (Ne.symm hhj.2.1) hij
    (h.row_selected i hi) (h.row_selected j hj) (h.ordinary_pair i j hi hj hij)

theorem row_cover (k : Coord) (hk : k∈distinctR a b c d) :
    ∀w,InPath p w → Adj (pair b k) w → w=triple b k c ∨ w=triple b k d := by
  intro w hw hadj
  rcases h.outer.row_neighbor_cover k hk w hw hadj with he | he | ⟨l,hl,hlk,he⟩
  · exact Or.inl he
  · exact Or.inr he
  · exact False.elim (h.ordinary_b_absent k l hk hl (Ne.symm hlk) (he ▸ hw))

theorem missing_pair_cover (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hm : ({i,j}:Finset Coord)∈f.F) :
    ∀w,InPath p w → Adj (pair i j) w → w=triple i j c ∨ w=triple i j d := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have hs := h.ordinary_pair i j hi hj hij
  have hna : ¬InPath p (triple a i j) := fun ht =>
    (f.selected_iff i j hij hhi.1 hhi.2.1 hhj.1 hhj.2.1).mp ht hm
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair i j hadj
  by_cases hri : r=i
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.outer.absent_unit j hhj.1 hhj.2.2.1 hw)
  by_cases hrj : r=j
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.outer.absent_unit i hhi.1 hhi.2.2.1 hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw; exact False.elim (hna hw)
  by_cases hrb : r=b
  · subst r; rw [triple_rotate] at hw; exact False.elim (h.ordinary_b_absent i j hi hj hij hw)
  by_cases hrc : r=c
  · subst r; exact Or.inl rfl
  by_cases hrd : r=d
  · subst r; exact Or.inr rfl
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  exact False.elim (selected_triple_forbidden p i j r hij (Ne.symm hri) (Ne.symm hrj)
    hs (h.ordinary_pair i r hi hr (Ne.symm hri))
    (h.ordinary_pair j r hj hr (Ne.symm hrj)) hw)

theorem missing_pair_low (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hie : i≠h.e) (hje : j≠h.e) (hm : ({i,j}:Finset Coord)∈f.F) :
    AtMostOneNeighbor p (pair i j) := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair i j) w) : w=triple i j c := by
    rcases h.missing_pair_cover f i j hi hj hij hm w hw hadj with he | he
    · exact he
    · have hdi : InPath p (pair i d) := by simpa only [pair_comm d i] using h.side_pair i hi hie
      have hdj : InPath p (pair j d) := by simpa only [pair_comm d j] using h.side_pair j hj hje
      exact False.elim (selected_triple_forbidden p i j d hij hhi.2.2.2 hhj.2.2.2
        (h.ordinary_pair i j hi hj hij) hdi hdj (he ▸ hw))
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem missing_e_endpoint_group (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (hm : ({h.e,k}:Finset Coord)∈f.F) (hd : ({d,k}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (pair h.e k) := by
  by_contra hn
  push_neg at hn
  have hh := (mem_distinctR a b c d k).mp hk
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hdk := h.side_pair k hk hke
  have hadk := (f.selected_iff d k (Ne.symm hh.2.2.2) (Ne.symm h.outer.had)
    (Ne.symm h.outer.hbd) hh.1 hh.2.1).mpr hd
  have hbdk := (force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn.1 (h.row_cover k hk)).2
  have hde : ¬InPath p (triple h.e k d) := by
    have ha' : InPath p (SquareIncidence.flip a (pair d k)) := by
      change InPath p (triple d k a)
      rw [triple_rotate]
      exact hadk
    have hb' : InPath p (SquareIncidence.flip b (pair d k)) := by
      change InPath p (triple d k b)
      rw [triple_rotate]
      simpa only [triple_swap b k d] using hbdk
    have ht := selected_flip_forbidden p (pair d k) a b h.e h.outer.hab
      (Ne.symm he.1) (Ne.symm he.2.1) hdk ha' hb'
    intro hsel
    apply ht
    change InPath p (triple d k h.e)
    have heq : triple h.e k d=triple d k h.e := by
      apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    exact heq ▸ hsel
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair h.e k) w) :
      w=triple h.e k c := by
    rcases h.missing_pair_cover f h.e k h.he hk (Ne.symm hke) hm w hw hadj with heq | heq
    · exact heq
    · exact False.elim (hde (heq ▸ hw))
  apply hn.2
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

end StarLeftConfig
#print axioms StarLeftConfig.missing_pair_low
#print axioms StarLeftConfig.missing_e_endpoint_group
end
end Snake9
