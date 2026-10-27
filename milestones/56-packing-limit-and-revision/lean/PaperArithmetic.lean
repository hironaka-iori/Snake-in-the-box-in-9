import Mathlib.Tactic
namespace Snake9.PaperArithmetic56

theorem retained_empty (m T s : Nat)
    (hc : 4*m ≤ T+21) (hi : T+2*s+35*(m+1)=9214) :
    39*m+2*s ≤ 9200 := by omega

theorem eighteen_empty (m s : Nat) (h : 39*m+2*s ≤ 9200)
    (hs : 18≤s) : m≤234 := by omega

theorem five_potential (m p d W R : Int) (hd : 0≤d)
    (hb : W+4200*m ≤ 1099800) (hp : p*(m-7)≤d*W+R) :
    (p+4200*d)*m ≤ 1099800*d+7*p+R := by
  have h := mul_le_mul_of_nonneg_left hb hd
  nlinarith

theorem current_model (m : Nat) (h : 977*m≤229973) : m≤235 := by omega

theorem finite_blocks (v p T S : Nat) (hp : 1≤p)
    (ht : v+49*p+6≤T) (hs : 96*(2*p-1)≤S)
    (hg : 24*T+S+840*v≤221136) : 864*v+1368*p≤221088 := by omega

#print axioms retained_empty
#print axioms eighteen_empty
#print axioms five_potential
#print axioms current_model
#print axioms finite_blocks
end Snake9.PaperArithmetic56
