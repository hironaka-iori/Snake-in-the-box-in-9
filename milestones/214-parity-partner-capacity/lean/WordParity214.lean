import IndexedCriterion206

namespace WordParity214
open IndexedCriterion206

def parity : List Bool → Bool
  | [] => false
  | b :: bs => Bool.xor b (parity bs)

theorem adjacent_parity (u v : List Bool)
    (hlen : u.length = v.length) (hd : hamming u v = 1) :
    parity v = !(parity u) := by
  induction u generalizing v with
  | nil =>
      cases v <;> simp_all [hamming]
  | cons a us ih =>
      cases v with
      | nil => simp at hlen
      | cons b vs =>
          have ht : us.length = vs.length := Nat.succ.inj hlen
          by_cases hab : a = b
          · subst b
            have hd' : hamming us vs = 1 := by simpa [hamming] using hd
            have hp := ih vs ht hd'
            cases a <;> simp [parity, hp]
          · have hd' : hamming us vs = 0 := by
              simp only [hamming, if_neg hab] at hd
              omega
            have heq := (hamming_eq_zero_iff us vs).mp hd'
            subst vs
            cases a <;> cases b <;> simp_all [parity]

theorem index_parity_step (g : Nat) :
    decide ((g+1)%2=1) = !(decide (g%2=1)) := by
  by_cases h : g%2=1
  · have hn : (g+1)%2≠1 := by omega
    simp [h,hn]
  · have hn : (g+1)%2=1 := by omega
    simp [h,hn]

#print axioms adjacent_parity
#print axioms index_parity_step
end WordParity214
