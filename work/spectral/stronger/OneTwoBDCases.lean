import NormalizeOneTwo

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem exists_three_coords_outside_six (a b c d e f : Coord) :
    ∃ j : Fin 3 → Coord,
      (∀ k, j k≠a ∧ j k≠b ∧ j k≠c ∧ j k≠d ∧ j k≠e ∧ j k≠f) ∧
      Function.Injective j := by
  let forbidden : Finset Coord := {a,b,c,d,e,f}
  let allowed := Finset.univ \ forbidden
  have hsmall : forbidden.card ≤ 6 := by
    have hx : ({b,c,d,e,f} : Finset Coord).card ≤ 5 := Finset.card_le_five
    have hy := Finset.card_insert_le a ({b,c,d,e,f} : Finset Coord)
    dsimp [forbidden]
    omega
  have hcard : allowed.card = 9 - forbidden.card := by
    simp [allowed, Finset.card_sdiff (Finset.subset_univ forbidden), Coord]
  have hlarge : Fintype.card (Fin 3) ≤ allowed.card := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset hlarge
  refine ⟨j,?_,j.injective⟩
  intro k
  have hm : j k ∈ allowed := hj ⟨k,rfl⟩
  simpa only [allowed,forbidden,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton,not_or] using hm

theorem coordinate_mem_of_pair_eq {i j x y : Coord}
    (h : ({i,j} : Finset Coord) = {x,y}) : i=x ∨ i=y := by
  have hm : i ∈ ({i,j} : Finset Coord) := by simp
  rw [h] at hm
  simpa using hm

theorem pair_not_in_two_of_left {i j b d f g : Coord}
    (hib : i≠b) (hid : i≠d) (hif : i≠f) (hig : i≠g) :
    ({i,j} : Finset Coord) ∉ ({({b,d} : Finset Coord),{f,g}} : Finset (Finset Coord)) := by
  intro hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · rcases coordinate_mem_of_pair_eq hm with he | he
    · exact hib he
    · exact hid he
  · rcases coordinate_mem_of_pair_eq hm with he | he
    · exact hif he
    · exact hig he

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord}

theorem bd_nonb_false (h : OneTwoRoot p a b c d) (z : TwoMissingAtNeighbor p a c)
    (f g : Coord) (hbf : b≠f) (hbg : b≠g)
    (hF : z.F = {({b,d} : Finset Coord),{f,g}}) : False := by
  have selected_row (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) :
      InPath p (triple a b k) := by
    apply (z.selected_iff b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc).mpr
    rw [hF]
    intro hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with he | he
    · have hj := coordinate_mem_of_pair_eq (show ({k,b} : Finset Coord) = {b,d} by rw [Finset.pair_comm]; exact he)
      exact hj.elim hkb hkd
    · exact (coordinate_mem_of_pair_eq he).elim hbf hbg
  obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d f g
  let v : Fin 3 → Fin 3 → Vertex := fun i r =>
    if r=0 then triple a b (j i) else if r=1 then pair c (j i) else pair d (j i)
  have hv : ∀ i r, InPath p (v i r) := by
    intro i r
    by_cases hr : r=0
    · simp only [v,hr,if_true]
      exact selected_row (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1
    · simp only [v,hr,if_false]
      by_cases hr1 : r=1
      · rw [if_pos hr1]
        apply h.selected_pair c (j i) (Ne.symm (hj i).2.2.1)
          (Ne.symm h.hac) (Ne.symm h.hbc) (hj i).1 (hj i).2.1
        simp [h.hcd,(hj i).2.2.2.1]
      · rw [if_neg hr1]
        apply h.selected_pair d (j i) (Ne.symm (hj i).2.2.2.1)
          (Ne.symm h.had) (Ne.symm h.hbd) (hj i).1 (hj i).2.1
        simp [Ne.symm h.hcd,(hj i).2.2.1]
  have hd : ∀ i l, i≠l → ∀ r s, v i r ≠ v l s := by
    intro i l hil r s he
    have hli : j l≠j i := fun he => hil (hji he).symm
    have hb := congrArg (fun w : Vertex => w.val.testBit (j i).val) he
    dsimp [v] at hb
    split_ifs at hb <;>
      simp [bit_pair,bit_triple,Ne.symm (hj i).1,Ne.symm (hj i).2.1,
        Ne.symm (hj i).2.2.1,Ne.symm (hj i).2.2.2.1,hli] at hb
  obtain ⟨i,hi⟩ := exists_good_group p v hv hd
  let k := j i
  obtain ⟨hka,hkb,hkc,hkd,hkf,hkg⟩ := hj i
  have ht : InPath p (triple a b k) := selected_row k hka hkb hkc hkd
  have hadk : InPath p (triple a d k) := by
    apply (z.selected_iff d k (Ne.symm hkd) (Ne.symm h.had) (Ne.symm h.hcd) hka hkc).mpr
    rw [hF, Finset.pair_comm d k]
    exact pair_not_in_two_of_left hkb hkd hkf hkg
  have hcvr : ∀ w, InPath p w → Adj (triple a b k) w →
      w=quad a b c k ∨ w=quad a b d k := by
    intro w hw hadj
    rcases h.triple_neighbor_cover_general k hka hkb hkc hkd w hw hadj with he | ⟨l,hla,hlb,hlc,hlk,he⟩
    · exact Or.inl he
    · by_cases hld : l=d
      · right
        rw [hld,quad_swap_last] at he
        exact he
      · have htl := selected_row l hla hlb hlc hld
        have hakl : InPath p (triple a k l) := by
          apply (z.selected_iff k l (Ne.symm hlk) hka hkc hla hlc).mpr
          rw [hF]
          exact pair_not_in_two_of_left hkb hkd hkf hkg
        exact False.elim (ordinary_quad_absent p a b k l h.hab hkb hlb (Ne.symm hlk) ht htl hakl (he ▸ hw))
  have hlow := h.cycle_group_low_degree k hka hkb hkc hkd ht hadk hcvr
  have hnt : ¬ AtMostOneNeighbor p (triple a b k) := by simpa [v,k] using hi 0
  have hnc : ¬ AtMostOneNeighbor p (pair c k) := by simpa [v,k] using hi 1
  have hnd : ¬ AtMostOneNeighbor p (pair d k) := by simpa [v,k] using hi 2
  exact hlow.elim hnt (fun hh => hh.elim hnc hnd)

theorem bd_hole_false (h : OneTwoRoot p a b c d) (z : TwoMissingAtNeighbor p a c)
    (e : Coord) (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (hF : z.F = {({b,d} : Finset Coord),{b,e}}) : False := by
  have selected_row (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c)
      (hkd : k≠d) (hke : k≠e) : InPath p (triple a b k) := by
    apply (z.selected_iff b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc).mpr
    rw [hF,Finset.pair_comm b k]
    exact pair_not_in_two_of_left hkb hkd hkb hke
  obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d e e
  let v : Fin 3 → Fin 4 → Vertex := fun i r =>
    if r=0 then triple a b (j i) else if r=1 then pair c (j i)
      else if r=2 then pair d (j i) else pair e (j i)
  have hv : ∀ i r, InPath p (v i r) := by
    intro i r
    by_cases hr : r=0
    · simp only [v,hr,if_true]
      exact selected_row (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1
        (hj i).2.2.2.1 (hj i).2.2.2.2.1
    · simp only [v,hr,if_false]
      by_cases hr1 : r=1
      · rw [if_pos hr1]
        apply h.selected_pair c (j i) (Ne.symm (hj i).2.2.1)
          (Ne.symm h.hac) (Ne.symm h.hbc) (hj i).1 (hj i).2.1
        simp [h.hcd,(hj i).2.2.2.1]
      · rw [if_neg hr1]
        by_cases hr2 : r=2
        · rw [if_pos hr2]
          apply h.selected_pair d (j i) (Ne.symm (hj i).2.2.2.1)
            (Ne.symm h.had) (Ne.symm h.hbd) (hj i).1 (hj i).2.1
          simp [Ne.symm h.hcd,(hj i).2.2.1]
        · rw [if_neg hr2]
          apply h.selected_pair e (j i) (Ne.symm (hj i).2.2.2.2.1)
            hea heb (hj i).1 (hj i).2.1
          simp [hec,hed]
  have hd : ∀ i l, i≠l → ∀ r s, v i r ≠ v l s := by
    intro i l hil r s he
    have hli : j l≠j i := fun he => hil (hji he).symm
    have hb := congrArg (fun w : Vertex => w.val.testBit (j i).val) he
    dsimp [v] at hb
    split_ifs at hb <;>
      simp [bit_pair,bit_triple,Ne.symm (hj i).1,Ne.symm (hj i).2.1,
        Ne.symm (hj i).2.2.1,Ne.symm (hj i).2.2.2.1,Ne.symm (hj i).2.2.2.2.1,hli] at hb
  obtain ⟨i,hi⟩ := exists_good_group p v hv hd
  let k := j i
  obtain ⟨hka,hkb,hkc,hkd,hke,_⟩ := hj i
  have ht : InPath p (triple a b k) := selected_row k hka hkb hkc hkd hke
  have hadk : InPath p (triple a d k) := by
    apply (z.selected_iff d k (Ne.symm hkd) (Ne.symm h.had) (Ne.symm h.hcd) hka hkc).mpr
    rw [hF, Finset.pair_comm d k]
    exact pair_not_in_two_of_left hkb hkd hkb hke
  have haek : InPath p (triple a e k) := by
    apply (z.selected_iff e k (Ne.symm hke) hea hec hka hkc).mpr
    rw [hF, Finset.pair_comm e k]
    exact pair_not_in_two_of_left hkb hkd hkb hke
  have hne : ¬ AtMostOneNeighbor p (pair e k) := by simpa [v,k] using hi 3
  have hqe : ¬ InPath p (quad a b e k) := by
    intro hq
    exact hne (h.hole_connection_low_degree e k hea heb hec hed hka hkb hkc hkd
      (Ne.symm hke) hq ht haek)
  have hcvr : ∀ w, InPath p w → Adj (triple a b k) w →
      w=quad a b c k ∨ w=quad a b d k := by
    intro w hw hadj
    rcases h.triple_neighbor_cover_general k hka hkb hkc hkd w hw hadj with he | ⟨l,hla,hlb,hlc,hlk,he⟩
    · exact Or.inl he
    · by_cases hld : l=d
      · right
        rw [hld,quad_swap_last] at he
        exact he
      · by_cases hle : l=e
        · rw [hle,quad_swap_last] at he
          exact False.elim (hqe (he ▸ hw))
        · have htl := selected_row l hla hlb hlc hld hle
          have hakl : InPath p (triple a k l) := by
            apply (z.selected_iff k l (Ne.symm hlk) hka hkc hla hlc).mpr
            rw [hF]
            exact pair_not_in_two_of_left hkb hkd hkb hke
          exact False.elim (ordinary_quad_absent p a b k l h.hab hkb hlb (Ne.symm hlk) ht htl hakl (he ▸ hw))
  have hlow := h.cycle_group_low_degree k hka hkb hkc hkd ht hadk hcvr
  have hnt : ¬ AtMostOneNeighbor p (triple a b k) := by simpa [v,k] using hi 0
  have hnc : ¬ AtMostOneNeighbor p (pair c k) := by simpa [v,k] using hi 1
  have hnd : ¬ AtMostOneNeighbor p (pair d k) := by simpa [v,k] using hi 2
  exact hlow.elim hnt (fun hh => hh.elim hnc hnd)

theorem bd_in_missing_false (h : OneTwoRoot p a b c d) (z : TwoMissingAtNeighbor p a c)
    (hbd : ({b,d} : Finset Coord) ∈ z.F) : False := by
  have finish (s : Finset Coord) (hsm : s∈z.F) (hne : s≠({b,d} : Finset Coord))
      (hFs : z.F = {({b,d} : Finset Coord),s}) : False := by
    obtain ⟨u,v,huv,hs⟩ := Finset.card_eq_two.mp (z.edge_card s hsm)
    have hu : u≠a ∧ u≠c := z.avoids s hsm u (by rw [hs]; simp)
    have hv : v≠a ∧ v≠c := z.avoids s hsm v (by rw [hs]; simp)
    by_cases hbu : b=u
    · subst u
      have hvd : v≠d := by intro he; apply hne; simpa only [he] using hs
      apply h.bd_hole_false z v hv.1 (Ne.symm huv) hv.2 hvd
      simpa only [hs] using hFs
    · by_cases hbv : b=v
      · subst v
        have hud : u≠d := by
          intro he
          apply hne
          rw [hs,he,Finset.pair_comm]
        apply h.bd_hole_false z u hu.1 huv hu.2 hud
        simpa only [hs,Finset.pair_comm u b] using hFs
      · apply h.bd_nonb_false z u v hbu hbv
        simpa only [hs] using hFs
  obtain ⟨s,t,hst,hF⟩ := Finset.card_eq_two.mp z.Fcard
  have hm : ({b,d} : Finset Coord)=s ∨ ({b,d} : Finset Coord)=t := by simpa only [hF,Finset.mem_insert,Finset.mem_singleton] using hbd
  rcases hm with he | he
  · subst s
    exact finish t (by rw [hF]; simp) (Ne.symm hst) hF
  · subst t
    apply finish s (by rw [hF]; simp) hst
    rw [hF,Finset.pair_comm]

end OneTwoRoot
#print axioms OneTwoRoot.bd_nonb_false
#print axioms OneTwoRoot.bd_hole_false
#print axioms OneTwoRoot.bd_in_missing_false
end
end Snake9
