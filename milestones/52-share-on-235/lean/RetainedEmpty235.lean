import Mathlib.Tactic
namespace Snake9.RetainedEmpty235

/-- Retain the empty-face term when applying the six-centre count estimate. -/
theorem retained_empty (m T s : Nat)
    (hsquare : T+2*s+35*(m+1)=9214)
    (hcount : 4*m ≤ T+21) : 39*m+2*s ≤ 9200 := by omega

/-- This is the exact extra empty-square target for the recorded 235 estimate. -/
theorem target_234 (m s : Nat) (h : 39*m+2*s ≤ 9200) (hs : 18≤s) :
    m≤234 := by omega

theorem target_is_tight : 39*235+2*17≤9200 ∧ ¬(39*235+2*18≤9200) := by decide

/-- A disjoint family is represented by its already-established share budget. -/
theorem eighteen_share_windows (N S s : Nat)
    (hl : 48*N≤S) (hu : S≤48*s) (hn : 18≤N) : 18≤s := by omega

theorem fivefold_overlap_target (N S s : Nat)
    (hl : 48*N≤5*S) (hu : S≤48*s) (hn : 86≤N) : 18≤s := by omega

theorem nine_share96_windows (N S s : Nat)
    (hl : 96*N≤S) (hu : S≤48*s) (hn : 9≤N) : 18≤s := by omega

theorem forty_three_share96_windows (N S s : Nat)
    (hl : 96*N≤5*S) (hu : S≤48*s) (hn : 43≤N) : 18≤s := by omega

#print axioms retained_empty
#print axioms target_234
#print axioms target_is_tight
#print axioms eighteen_share_windows
#print axioms fivefold_overlap_target
#print axioms nine_share96_windows
#print axioms forty_three_share96_windows
end Snake9.RetainedEmpty235
