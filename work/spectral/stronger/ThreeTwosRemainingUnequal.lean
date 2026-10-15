import ThreeTwosRemainingOrdinary
import MixedOuterExclusion
import EqualOuterPairExclusion

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

theorem DistinctOuterConfig.remaining_unequal_ordinary_case {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : DistinctOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    ∃s t : Finset Coord,s.card=2 ∧ t.card=2 ∧
      s⊆distinctR a b c d ∧ t⊆distinctR a b c d ∧ s≠t ∧
      h.left.F=insert {b,d} {s} ∧ h.right.F=insert {a,c} {t} := by
  obtain ⟨s,t,hs,ht,hsR,htR,hbs,hat,hl,hr,hord⟩ := h.remaining_ordinary_case f hFcard
  have hsR' : s⊆distinctR a b c d := by
    by_contra hn
    obtain ⟨e,he,hed,hse⟩ := (pair_supported_insert_cases s (distinctR a b c d) d hs hsR).resolve_left hn
    have htR' := hord.resolve_left hn
    obtain ⟨i,j,hij,htij⟩ := Finset.card_eq_two.mp ht
    have hi := htR' (show i∈t by rw [htij]; simp)
    have hj := htR' (show j∈t by rw [htij]; simp)
    let mh : MixedOuterConfig p a b c d :=
      ⟨⟨h,e,he,by simpa only [hse] using hl⟩,i,j,hi,hj,hij,by simpa only [htij] using hr⟩
    exact mh.impossible f hFcard
  have htR' : t⊆distinctR a b c d := by
    by_contra hn
    obtain ⟨e,he,hec,hte⟩ := (pair_supported_insert_cases t (distinctR a b c d) c ht htR).resolve_left hn
    obtain ⟨i,j,hij,hsij⟩ := Finset.card_eq_two.mp hs
    have hi := hsR' (show i∈s by rw [hsij]; simp)
    have hj := hsR' (show j∈s by rw [hsij]; simp)
    have mirror_mem (x : Coord) (hx : x∈distinctR a b c d) : x∈distinctR b a d c := by
      obtain ⟨hxa,hxb,hxc,hxd⟩ := (mem_distinctR a b c d x).mp hx
      exact (mem_distinctR b a d c x).mpr ⟨hxb,hxa,hxd,hxc⟩
    let mh : MixedOuterConfig (translate p (pair a b)) b a d c :=
      ⟨⟨h.mirror,e,mirror_mem e he,by simpa only [DistinctOuterConfig.mirror,hte] using hr⟩,
        i,j,mirror_mem i hi,mirror_mem j hj,hij,
        by simpa only [DistinctOuterConfig.mirror,hsij] using hl⟩
    exact mh.impossible f.mirror hFcard
  have hst : s≠t := by
    intro he
    obtain ⟨i,j,hij,hsij⟩ := Finset.card_eq_two.mp hs
    have hi := hsR' (show i∈s by rw [hsij]; simp)
    have hj := hsR' (show j∈s by rw [hsij]; simp)
    let eh : EqualOuterPairConfig p a b c d :=
      ⟨h,i,j,hi,hj,hij,by simpa only [hsij] using hl,by simpa only [←he,hsij] using hr⟩
    exact eh.impossible f hFcard
  exact ⟨s,t,hs,ht,hsR',htR',hst,hl,hr⟩

#print axioms DistinctOuterConfig.remaining_unequal_ordinary_case
end
end Snake9
