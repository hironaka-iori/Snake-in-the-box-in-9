import NeighbourChoice
namespace Snake9.LocalWindow.CountPropagation65
open ForcedShare58 ExtendedShare59 SplitShare62 NeighbourChoice64
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem count_complement (S : Nat → Bool) (K : List Nat) :
    cnt S K + cnt (fun x => !S x) K = K.length := by
  induction K with
  | nil => simp [cnt]
  | cons a K ih =>
    cases hs : S a <;> simp_all [cnt,List.filter_cons] <;> omega

theorem known_absent_count (S : Nat → Bool) (D K : List Nat)
    (hD : ∀ v∈D, S v=false) :
    cnt (fun x => D.contains x) K ≤ cnt (fun x => !S x) K := by
  apply count_mono
  intro x _ hx
  simp [hD x (List.contains_iff.mp hx)]

theorem known_selected_count (S : Nat → Bool) (T K : List Nat)
    (hT : ∀ v∈T, S v=true) :
    cnt (fun x => T.contains x) K ≤ cnt S K :=
  count_mono _ S K (fun x _ hx => hT x (List.contains_iff.mp hx))

/-- An exhausted absence allowance forces another corner to be selected. -/
theorem selected_from_upper (S : Nat → Bool) (D K : List Nat) (cap q : Nat)
    (hD : ∀ v∈D, S v=false) (hu : cnt (fun x => !S x) K ≤ cap)
    (hc : cap < cnt (fun x => (q::D).contains x) K) : S q=true := by
  cases hs : S q with
  | true => rfl
  | false =>
    have hm := known_absent_count S (q::D) K (by
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · simpa [hv] using hs
      · exact hD v hv)
    omega

theorem absent_from_lower (S : Nat → Bool) (T K : List Nat) (lo q : Nat)
    (hT : ∀ v∈T, S v=true) (hl : lo ≤ cnt (fun x => !S x) K)
    (hc : K.length < lo + cnt (fun x => (q::T).contains x) K) : S q=false := by
  cases hs : S q with
  | false => rfl
  | true =>
    have hm := known_selected_count S (q::T) K (by
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · simpa [hv] using hs
      · exact hT v hv)
    have hh := count_complement S K
    omega

theorem upper_contradiction (S : Nat → Bool) (D K : List Nat) (cap : Nat)
    (hD : ∀ v∈D, S v=false) (hu : cnt (fun x => !S x) K≤cap)
    (hc : cap < cnt (fun x => D.contains x) K) : False := by
  have := known_absent_count S D K hD
  omega

theorem lower_contradiction (S : Nat → Bool) (T K : List Nat) (lo : Nat)
    (hT : ∀ v∈T, S v=true) (hl : lo≤cnt (fun x => !S x) K)
    (hc : K.length < lo + cnt (fun x => T.contains x) K) : False := by
  have := known_selected_count S T K hT
  have := count_complement S K
  omega

def corners (c : Centre) : List Nat :=
  (freePairs c.d₁ c.d₂).map fun ab => c.v ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2)

theorem corners_count (S : Nat → Bool) (c : Centre) :
    cnt (fun x => !S x) (corners c)=absentCorners S c.v c.d₁ c.d₂ := by
  simp [cnt,corners,absentCorners,List.filter_map,Function.comp_def]

#print axioms count_complement
#print axioms known_absent_count
#print axioms known_selected_count
#print axioms selected_from_upper
#print axioms absent_from_lower
#print axioms upper_contradiction
#print axioms lower_contradiction
#print axioms corners_count
end Snake9.LocalWindow.CountPropagation65
