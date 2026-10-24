import SumWindow411
import JointExcess

namespace Snake9.LocalWindow.JointIntervening411

theorem excess_in_snake {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) (h7 : coreAlpha p (r+7) ≤ 3)
    (hcoarse : min 6 (coreAlpha p (r+3)) + min 6 (coreAlpha p (r+6)) ≤ 11) :
    1 ≤ (coreAlpha p (r+3)-min 6 (coreAlpha p (r+3))) +
        (coreAlpha p (r+6)-min 6 (coreAlpha p (r+6))) :=
  JointInterveningAccounting.forced_excess _ _
    (joint_intervening_sum p r a b c d e hn h9 hr hd h1 h7) hcoarse

#print axioms excess_in_snake
end Snake9.LocalWindow.JointIntervening411
