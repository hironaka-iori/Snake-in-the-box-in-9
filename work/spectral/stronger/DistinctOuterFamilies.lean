import DistinctOuterGeometry

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace DistinctOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DistinctOuterConfig p a b c d)

def holes : Finset Coord := (distinctR a b c d).filter (fun k => ({b,k}:Finset Coord)∈h.left.F)
def leftRemainder : Finset (Finset Coord) := nonincidentEdges h.left.F b
def rightRemainder : Finset (Finset Coord) := nonincidentEdges h.right.F a

theorem holes_subset : h.holes⊆distinctR a b c d := Finset.filter_subset _ _

theorem incident_left_erase : (incidentCoordinates h.left.F b).erase d=h.holes := by
  ext k
  constructor
  · intro hk
    obtain ⟨hkd,hk⟩ := Finset.mem_erase.mp hk
    obtain ⟨hkb,hbk⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨hka,hkc⟩ := h.left.avoids {b,k} hbk k (by simp)
    exact Finset.mem_filter.mpr ⟨(mem_distinctR a b c d k).mpr ⟨hka,hkb,hkc,hkd⟩,hbk⟩
  · intro hk
    obtain ⟨hk,hbk⟩ := Finset.mem_filter.mp hk
    obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
    exact Finset.mem_erase.mpr ⟨hkd,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkb,hbk⟩⟩

theorem incident_right_erase : (incidentCoordinates h.right.F a).erase c=h.holes := by
  ext k
  constructor
  · intro hk
    obtain ⟨hkc,hk⟩ := Finset.mem_erase.mp hk
    obtain ⟨hka,hak⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨hkb,hkd⟩ := h.right.avoids {a,k} hak k (by simp)
    have hr := (mem_distinctR a b c d k).mpr ⟨hka,hkb,hkc,hkd⟩
    exact Finset.mem_filter.mpr ⟨hr,(h.same_hole k hr).mpr hak⟩
  · intro hk
    obtain ⟨hk,hbk⟩ := Finset.mem_filter.mp hk
    obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
    exact Finset.mem_erase.mpr ⟨hkc,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hka,(h.same_hole k hk).mp hbk⟩⟩

theorem left_count_absent (hd : ({b,d}:Finset Coord)∉h.left.F) :
    h.leftRemainder.card+h.holes.card=2 := by
  have hdn : d∉incidentCoordinates h.left.F b := by simp [incidentCoordinates,hd]
  have he := h.incident_left_erase
  rw [Finset.erase_eq_of_not_mem hdn] at he
  have hc := pair_family_split_card h.left.F b h.left.edge_card
  rw [he,h.left.Fcard] at hc
  change h.holes.card+h.leftRemainder.card=2 at hc
  omega

theorem left_count_present (hd : ({b,d}:Finset Coord)∈h.left.F) :
    h.leftRemainder.card+h.holes.card+1=2 := by
  have hdm : d∈incidentCoordinates h.left.F b := by simp [incidentCoordinates,Ne.symm h.hbd,hd]
  have hc := pair_family_split_card h.left.F b h.left.edge_card
  have he := Finset.card_erase_add_one hdm
  rw [h.incident_left_erase] at he
  rw [h.left.Fcard] at hc
  change (incidentCoordinates h.left.F b).card+h.leftRemainder.card=2 at hc
  omega

theorem right_count_absent (hc : ({a,c}:Finset Coord)∉h.right.F) :
    h.rightRemainder.card+h.holes.card=2 := by
  have hcn : c∉incidentCoordinates h.right.F a := by simp [incidentCoordinates,hc]
  have he := h.incident_right_erase
  rw [Finset.erase_eq_of_not_mem hcn] at he
  have hz := pair_family_split_card h.right.F a h.right.edge_card
  rw [he,h.right.Fcard] at hz
  change h.holes.card+h.rightRemainder.card=2 at hz
  omega

theorem right_count_present (hc : ({a,c}:Finset Coord)∈h.right.F) :
    h.rightRemainder.card+h.holes.card+1=2 := by
  have hcm : c∈incidentCoordinates h.right.F a := by simp [incidentCoordinates,Ne.symm h.hac,hc]
  have hz := pair_family_split_card h.right.F a h.right.edge_card
  have he := Finset.card_erase_add_one hcm
  rw [h.incident_right_erase] at he
  rw [h.right.Fcard] at hz
  change (incidentCoordinates h.right.F a).card+h.rightRemainder.card=2 at hz
  omega

theorem leftRemainder_edge_card : ∀s∈h.leftRemainder,s.card=2 :=
  fun s hs => h.left.edge_card s (Finset.mem_filter.mp hs).1

theorem rightRemainder_edge_card : ∀s∈h.rightRemainder,s.card=2 :=
  fun s hs => h.right.edge_card s (Finset.mem_filter.mp hs).1

theorem leftRemainder_support : ∀s∈h.leftRemainder,s⊆insert d (distinctR a b c d) := by
  intro s hs k hk
  obtain ⟨hs,hbs⟩ := Finset.mem_filter.mp hs
  obtain ⟨hka,hkc⟩ := h.left.avoids s hs k hk
  by_cases hkd : k=d
  · simp [hkd]
  · exact Finset.mem_insert_of_mem ((mem_distinctR a b c d k).mpr ⟨hka,fun he => hbs (he ▸ hk),hkc,hkd⟩)

theorem rightRemainder_support : ∀s∈h.rightRemainder,s⊆insert c (distinctR a b c d) := by
  intro s hs k hk
  obtain ⟨hs,has⟩ := Finset.mem_filter.mp hs
  obtain ⟨hkb,hkd⟩ := h.right.avoids s hs k hk
  by_cases hkc : k=c
  · simp [hkc]
  · exact Finset.mem_insert_of_mem ((mem_distinctR a b c d k).mpr ⟨fun he => has (he ▸ hk),hkb,hkc,hkd⟩)

theorem selected_row (k : Coord) (hk : k∈distinctR a b c d\h.holes) : InPath p (pair b k) := by
  obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hk
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hr
  apply (h.left.selected_iff b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc).mpr
  intro hb
  exact hn (Finset.mem_filter.mpr ⟨hr,hb⟩)

theorem leftRemainder_pair (k l : Coord) (hkb : k≠b) (hlb : l≠b)
    (hs : ({k,l}:Finset Coord)∈h.left.F) : ({k,l}:Finset Coord)∈h.leftRemainder :=
  Finset.mem_filter.mpr ⟨hs,by simp [Ne.symm hkb,Ne.symm hlb]⟩

theorem rightRemainder_pair (k l : Coord) (hka : k≠a) (hla : l≠a)
    (hs : ({k,l}:Finset Coord)∈h.right.F) : ({k,l}:Finset Coord)∈h.rightRemainder :=
  Finset.mem_filter.mpr ⟨hs,by simp [Ne.symm hka,Ne.symm hla]⟩

end DistinctOuterConfig
#print axioms DistinctOuterConfig.left_count_present
#print axioms DistinctOuterConfig.right_count_present
end
end Snake9
