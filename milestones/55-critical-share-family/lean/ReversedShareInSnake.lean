import ShareInSnake6
import ReverseShareRule

namespace Snake9.LocalWindow.ShareObstruction556

theorem reversed_share_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → P.fwd (dir p (r+5-j)) = directions.getD j 0)
    (hb : ∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+5-i) ∧
      coreAlpha p (r+5-i) ≤ (bounds.getD i (0,21)).2) :
    96 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  exact ReverseShareRule.reverse_rule directions bounds 96
    (fun q P t hr hd hb => share_in_snake q P t hr hd hb) p P r hr hd hb

#print axioms reversed_share_in_snake
end Snake9.LocalWindow.ShareObstruction556
