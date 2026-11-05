import Std
namespace Snake9.CriticalArithmetic173

theorem loss_threshold (m W G L : Nat) (hm : 235 ≤ m)
    (hp : W + 2520 ≤ 5 * G)
    (hb : G + 840 * (m+1) + L ≤ 221136)
    (hw : 4462 * (m-8) ≤ 9 * W + 5411) : m = 235 ∧ L ≤ 3 := by omega

theorem positive_loss_excludes_235 (m W G L : Nat) (hm : 1 ≤ m)
    (hp : W + 2520 ≤ 5 * G)
    (hb : G + 840 * (m+1) + L ≤ 221136)
    (hw : 4462 * (m-8) ≤ 9 * W + 5411) (hl : 4 ≤ L) : m ≤ 234 := by omega

#print axioms loss_threshold
#print axioms positive_loss_excludes_235
end Snake9.CriticalArithmetic173
