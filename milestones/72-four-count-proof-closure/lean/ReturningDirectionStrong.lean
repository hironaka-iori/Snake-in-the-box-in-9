import FourCount7219

namespace Snake9.LocalWindow.ReturningDirection72

theorem three_of_first_one {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+5 ≤ m)
    (hd : ∀ j, j<5 → dir p (r+j) = ([a,b,c,d,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 1) : 3 ≤ coreAlpha p (r+4) := by
  by_contra h
  have hlast : coreAlpha p (r+4) ≤ 2 := by omega
  apply FourCount7219.exclusion p r a b c d hn h9 hr hd
  have h2 := coreAlpha_le_21 p (k := r+2) (by omega) (by omega)
  have h3 := coreAlpha_le_21 p (k := r+3) (by omega) (by omega)
  intro i hi
  interval_cases i <;> norm_num [Nat.add_assoc] <;> omega

#print axioms three_of_first_one
end Snake9.LocalWindow.ReturningDirection72
