import LocalWindowShareBridge
import LocalWindowDirBridge
import Mathlib.Tactic

namespace Snake9.LocalWindow.CountPropagation65
set_option maxHeartbeats 2000000

theorem count_mono {α : Type} (S U : α → Bool) (l : List α)
    (h : ∀ x ∈ l, S x = true → U x = true) :
    (l.filter S).length ≤ (l.filter U).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ht := ih (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    cases hs : S a <;> cases hu : U a <;>
      simp_all [List.filter_cons] <;> omega

def forceCheckPlus (W D : List Nat) : Bool :=
  D.all fun q => (q::W).any fun v =>
    decide (3 ≤ cnt (fun t => (q::W).contains t) (nbrs v))

theorem forced_absent_plus (S : Nat → Bool) (W D : List Nat)
    (hW : ∀ v ∈ W, S v = true)
    (hd : ∀ v, S v = true → cnt S (nbrs v) ≤ 2)
    (hc : forceCheckPlus W D = true) : ∀ q ∈ D, S q = false := by
  intro q hq
  cases he : S q with
  | false => rfl
  | true =>
    have hsel : ∀ x ∈ q::W, S x = true := by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · simpa [hx] using he
      · exact hW x hx
    obtain ⟨v,hv,hv3⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc q hq)
    have hv3' : 3 ≤ cnt (fun t => (q::W).contains t) (nbrs v) := of_decide_eq_true hv3
    have hm := count_mono (fun t => (q::W).contains t) S (nbrs v)
      (fun x _ hx => hsel x (List.contains_iff.mp hx))
    have hh := hd v (hsel v hv)
    change cnt (fun t => (q::W).contains t) (nbrs v) ≤ cnt S (nbrs v) at hm
    omega

theorem known_absent_count (S : Nat → Bool) (D K : List Nat)
    (hD : ∀ v∈D, S v=false) :
    cnt (fun x => D.contains x) K ≤ cnt (fun x => !S x) K := by
  apply count_mono
  intro x _ hx
  simp [hD x (List.contains_iff.mp hx)]

def corners (c : Centre) : List Nat :=
  (freePairs c.d₁ c.d₂).map fun ab => c.v ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2)

theorem corners_count (S : Nat → Bool) (c : Centre) :
    cnt (fun x => !S x) (corners c)=absentCorners S c.v c.d₁ c.d₂ := by
  simp [cnt,corners,absentCorners,List.filter_map,Function.comp_def]

def canonicalCentres (W dirs : List Nat) (bounds : List (Nat × Nat)) : List Centre :=
  (List.range bounds.length).map fun i =>
    ⟨W.getD (i+1) 0, dirs.getD i 0, dirs.getD (i+1) 0,
      (bounds.getD i (0,21)).1, (bounds.getD i (0,21)).2⟩

theorem centresOf_canon {W dirs : List Nat} {bounds : List (Nat × Nat)}
    (hc : Canon W dirs) (hlen : bounds.length+1=dirs.length) :
    centresOf W bounds=canonicalCentres W dirs bounds := by
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have h1 : dirOfStep (W.getD i 0) (W.getD (i+1) 0)=dirs.getD i 0 := by
    rw [hc.step i (by omega),dirOfStep_xor]
  have h2 : dirOfStep (W.getD (i+1) 0) (W.getD (i+2) 0)=dirs.getD (i+1) 0 := by
    rw [show i+2=i+1+1 by omega,hc.step (i+1) (by omega),dirOfStep_xor]
  simp only [h1,h2]

#print axioms count_mono
#print axioms forced_absent_plus
#print axioms known_absent_count
#print axioms corners_count
#print axioms centresOf_canon
end Snake9.LocalWindow.CountPropagation65
