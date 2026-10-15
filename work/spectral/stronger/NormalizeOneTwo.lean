import TwoMissingPairs
import NormalizeAdjacentSingletons
import OneTwoLocal

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- The two singleton squares at the selected neighbor `a`, recorded as
unordered coordinate pairs.  The geometry proof uses only these fields. -/
structure TwoMissingAtNeighbor {m : Nat} (p : Snake m) (a c : Coord) where
  F : Finset (Finset Coord)
  Fcard : F.card = 2
  edge_card : ∀ s ∈ F, s.card = 2
  avoids : ∀ s ∈ F, ∀ k ∈ s, k ≠ a ∧ k ≠ c
  selected_iff : ∀ i j : Coord, i ≠ j → i ≠ a → i ≠ c → j ≠ a → j ≠ c →
    (InPath p (triple a i j) ↔ ({i,j} : Finset Coord) ∉ F)

theorem twoMissingAtNeighbor_of_alpha_two {m : Nat} (p : Snake m) (a c : Coord)
    (j : Fin (m+1)) (hj : p.vertex j = unit a)
    (hbeta : localAlpha p j = 2) (hza : InPath (translate p (unit a)) (unit a))
    (hzc : InPath (translate p (unit a)) (unit c))
    (cover : ∀ k, InPath (translate p (unit a)) (unit k) → k=a ∨ k=c) :
    Nonempty (TwoMissingAtNeighbor p a c) := by
  let z := translate p (unit a)
  have hzj : z.vertex j = 0 := by change vxor (unit a) (p.vertex j) = 0; rw [hj,vxor_self]
  have hz0 : InPath z 0 := ⟨j,hzj⟩
  have halpha : localAlpha z j = 2 := (localAlpha_translate p (unit a) j).trans hbeta
  have hc : (missingPairSupports z).card = 2 := (missingPairSupports_card z j hzj).trans halpha
  refine ⟨⟨missingPairSupports z,hc,missingPairSupports_edge_card z,?_,?_⟩⟩
  · intro s hs k hk
    exact ⟨missingPairSupports_avoids_selected_unit z a hza s hs k hk,
      missingPairSupports_avoids_selected_unit z c hzc s hs k hk⟩
  · intro i k hik hia hic hka hkc
    have hi : ¬ InPath z (unit i) := by
      intro hi
      rcases cover i hi with h | h
      · exact hia h
      · exact hic h
    have hk : ¬ InPath z (unit k) := by
      intro hk
      rcases cover k hk with h | h
      · exact hka h
      · exact hkc h
    have hm : ({i,k} : Finset Coord) ∈ missingPairSupports z ↔ ¬ InPath z (pair i k) := by
      simpa only [hi,hk,not_false_eq_true,true_and] using mem_missingPairSupports_iff z hz0 i k hik
    rw [hm]
    simpa only [not_not] using (translate_pair_membership p a i k).symm

structure AdjacentOneTwoConfig {m : Nat} (p : Snake m) where
  a : Coord
  b : Coord
  c : Coord
  d : Coord
  root : OneTwoRoot p a b c d
  missing : TwoMissingAtNeighbor p a c

theorem oneTwoConfig_of_adjacent_internal {m : Nat} (p : Snake m) (i j : Fin (m+1))
    (hi0 : 0 < i.val) (him : i.val < m) (hj0 : 0 < j.val) (hjm : j.val < m)
    (hadj : Adj (p.vertex i) (p.vertex j))
    (halpha : localAlpha p i = 1) (hbeta : localAlpha p j = 2) :
    Nonempty (AdjacentOneTwoConfig (translate p (p.vertex i))) := by
  let q := translate p (p.vertex i)
  have hqi : q.vertex i = 0 := vxor_self _
  have hqadj : Adj (q.vertex i) (q.vertex j) := (adj_vxor _ _ _).mpr hadj
  obtain ⟨a, hqa⟩ := (adj_zero_iff (q.vertex j)).mp (hqi ▸ hqadj)
  obtain ⟨k, hki, hjk⟩ := internal_other_neighbor q j i hj0 hjm
  obtain ⟨c, hqac⟩ := neighbor_unit a (hqa ▸ hjk)
  obtain ⟨l, hlj, hil⟩ := internal_other_neighbor q i j hi0 him
  obtain ⟨b, hqb⟩ := (adj_zero_iff (q.vertex l)).mp (hqi ▸ hil)
  have h0 : InPath q 0 := ⟨i,hqi⟩
  have ha : InPath q (unit a) := ⟨j,hqa⟩
  have hb : InPath q (unit b) := ⟨l,hqb⟩
  have hacsel : InPath q (pair a c) := ⟨k,hqac⟩
  have hab : a ≠ b := by
    intro he
    have hv : q.vertex l = q.vertex j := hqb.trans ((congrArg unit he).symm.trans hqa.symm)
    exact hlj (q.distinct l j hv)
  have hac : a ≠ c := by
    intro he
    have hv : q.vertex k = q.vertex i := by rw [hqac, ← he, pair_self, hqi]
    exact hki (q.distinct k i hv)
  have hbc : b ≠ c := by
    intro he
    have hp : InPath q (pair a b) := he ▸ hacsel
    exact selected_no_four_cycle q h0 ha hp hb
      ((adj_zero_iff _).mpr ⟨a,rfl⟩) (unit_pair_adj a b)
      (by rw [pair_comm a b]; exact adj_symmetric (unit_pair_adj b a))
      (adj_symmetric ((adj_zero_iff _).mpr ⟨b,rfl⟩))
      (Ne.symm (pair_nonzero a b hab)) (fun h => hab (unit_injective _ _ h))
  have cover := unit_cover_two q a b h0 ha hb hab
  have halphaq : localAlpha q i = 1 := (localAlpha_translate p _ i).trans halpha
  obtain ⟨r,s,hrs,hr,hs,_,hf⟩ := alpha_one_forced_pairs_zero q i hqi halphaq
  have hcrs : c = r ∨ c = s :=
    arm_coordinate_in_missing q a b r s c hac hbc ha hacsel cover hf
  have hd : ∃ d, c ≠ d ∧ ¬ InPath q (unit c) ∧ ¬ InPath q (unit d) ∧ ForcedPairsExcept q c d := by
    rcases hcrs with he | he
    · subst r
      exact ⟨s,hrs,hr,hs,hf⟩
    · subst s
      exact ⟨r,Ne.symm hrs,hs,hr,forcedPairsExcept_swap q r c hf⟩
  obtain ⟨d,hcd,_,hdu,hforced⟩ := hd
  have had : a ≠ d := fun he => hdu (he ▸ ha)
  have hbd : b ≠ d := fun he => hdu (he ▸ hb)
  let z := translate q (unit a)
  have hzj : z.vertex j = 0 := by change vxor (unit a) (q.vertex j) = 0; rw [hqa,vxor_self]
  have hza : InPath z (unit a) := (inPath_translate_at q (unit a) (unit a)).mpr (by simpa [vxor_self] using h0)
  have hzc : InPath z (unit c) := (inPath_translate_at q (unit a) (unit c)).mpr hacsel
  have hz0 : InPath z 0 := ⟨j,hzj⟩
  have qcover := unit_cover_two z a c hz0 hza hzc hac
  have hbetaq : localAlpha q j = 2 := (localAlpha_translate p _ j).trans hbeta
  obtain ⟨F⟩ := twoMissingAtNeighbor_of_alpha_two q a c j hqa hbetaq hza hzc qcover
  exact ⟨⟨a,b,c,d,⟨hab,hac,hbc,had,hbd,hcd,ha,hb,hacsel,cover,qcover,hforced⟩,F⟩⟩

#print axioms twoMissingAtNeighbor_of_alpha_two
#print axioms oneTwoConfig_of_adjacent_internal
end
end Snake9
