import OneTwoNoB
import OneTwoBECases

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem two_element_set_with_member (s : Finset Coord) (b : Coord)
    (hs : s.card = 2) (hb : b∈s) : ∃ e : Coord, e≠b ∧ s={b,e} := by
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp hs
  rcases (show b=u ∨ b=v by simpa only [Finset.mem_insert,Finset.mem_singleton] using hb) with h | h
  · subst u
    exact ⟨v,Ne.symm huv,rfl⟩
  · subst v
    exact ⟨u,huv,Finset.pair_comm _ _⟩

theorem oneTwoRoot_impossible_of_nonb {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : OneTwoRoot p a b c d) (f : TwoMissingAtNeighbor p a c)
    (hnonb : ∀ e x y : Coord, e≠a → e≠b → e≠c → e≠d →
      x≠a → x≠b → x≠c → y≠a → y≠b → y≠c → x≠y →
      f.F={{b,e},{x,y}} → False) : False := by
  by_cases hbd : ({b,d} : Finset Coord) ∈ f.F
  · exact h.bd_in_missing_false f hbd
  by_cases hnob : ∀ s∈f.F, b∉s
  · exact h.no_b_impossible f hnob
  push_neg at hnob
  obtain ⟨s,hs,hbs⟩ := hnob
  obtain ⟨e,heb,hse⟩ := two_element_set_with_member s b (f.edge_card s hs) hbs
  have he : e∈s := by rw [hse]; simp
  have hea := (f.avoids s hs e he).1
  have hec := (f.avoids s hs e he).2
  have hed : e≠d := by
    intro he
    apply hbd
    simpa only [hse,he] using hs
  have finish (t : Finset Coord) (ht : t∈f.F) (hF : f.F={s,t}) : False := by
    by_cases hbt : b∈t
    · obtain ⟨g,hgb,htg⟩ := two_element_set_with_member t b (f.edge_card t ht) hbt
      have hg : g∈t := by rw [htg]; simp
      have hga := (f.avoids t ht g hg).1
      have hgc := (f.avoids t ht g hg).2
      have hgd : g≠d := by
        intro he
        apply hbd
        simpa only [htg,he] using ht
      exact h.be_two_holes_false f e g hea heb hec hed hga hgb hgc hgd (by rw [hF,hse,htg])
    · obtain ⟨x,y,hxy,htxy⟩ := Finset.card_eq_two.mp (f.edge_card t ht)
      have hx : x∈t := by rw [htxy]; simp
      have hy : y∈t := by rw [htxy]; simp
      have hxa := (f.avoids t ht x hx).1
      have hxc := (f.avoids t ht x hx).2
      have hya := (f.avoids t ht y hy).1
      have hyc := (f.avoids t ht y hy).2
      have hxb : x≠b := fun he => hbt (he ▸ hx)
      have hyb : y≠b := fun he => hbt (he ▸ hy)
      exact hnonb e x y hea heb hec hed hxa hxb hxc hya hyb hyc hxy (by rw [hF,hse,htxy])
  obtain ⟨u,v,huv,hF⟩ := Finset.card_eq_two.mp f.Fcard
  have hs' : s=u ∨ s=v := by simpa only [hF,Finset.mem_insert,Finset.mem_singleton] using hs
  rcases hs' with rfl | rfl
  · exact finish v (by rw [hF]; simp) hF
  · exact finish u (by rw [hF]; simp) (hF.trans (Finset.pair_comm _ _))

#print axioms oneTwoRoot_impossible_of_nonb
end
end Snake9
