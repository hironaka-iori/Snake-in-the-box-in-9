import BoundarySlack187
namespace Combined187

theorem five_slack_requires_small_loss (m W L : Nat) (hm : 234 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (ht : 520*(m-7) ≤ W+1023) : L ≤ 31 := by omega

theorem five_slack_with_loss (m W L : Nat) (hm : 7 ≤ m)
    (hb : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (ht : 520*(m-7) ≤ W+1023)
    (hloss : 234 ≤ m → 32 ≤ L) : m ≤ 233 := by
  by_cases hlarge : 234 ≤ m
  · have := five_slack_requires_small_loss m W L hlarge hb ht
    have := hloss hlarge
    omega
  · omega

theorem four_slack_only_at_small_loss (m W L : Nat) (hm : 7 ≤ m)
    (hb5 : W+4200*m+5*L ≤ 1098840+5*(m-7))
    (hb4 : L ≤ 31 → W+4200*m+5*L ≤ 1098840+4*(m-7))
    (ht : 520*(m-7) ≤ W+1023) : m ≤ 233 := by
  by_cases hlarge : 234 ≤ m
  · have hl := five_slack_requires_small_loss m W L hlarge hb5 ht
    have := (four_point_slack m W L hm (hb4 hl) ht).2
    omega
  · omega

#print axioms five_slack_requires_small_loss
#print axioms five_slack_with_loss
#print axioms four_slack_only_at_small_loss
end Combined187
