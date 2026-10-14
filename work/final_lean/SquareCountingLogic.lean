import Std

namespace SquareCountingLogic

/- These lemmas check the arithmetic of the proposed square-face proof.
   They do not prove that every cube path satisfies the census premises.
   The geometric derivation of those premises remains a separate obligation. -/

theorem square_count_identity (v a0 a1 a2 a3 : Nat)
    (total : a0+a1+a2+a3=4608)
    (incidences : a1+2*a2+3*a3=36*v)
    (triples : a3+2=v) :
    2*a0+a1+35*v+2=9216 := by omega

theorem upper_254_of_census (length a0 a1 a2 a3 : Nat)
    (total : a0+a1+a2+a3=4608)
    (incidences : a1+2*a2+3*a3=36*(length+1))
    (triples : a3+2=length+1)
    (singleton_lower : length+1 ≤ a1) : length ≤ 254 := by
  have h := square_count_identity (length+1) a0 a1 a2 a3 total incidences triples
  omega

theorem six_candidates_exceed_two_endpoints (selected missing : Nat)
    (partition : selected+missing=6) (at_most_one : selected ≤ 1)
    (at_most_two : missing ≤ 2) : False := by omega

theorem twenty_eight_pairs_exceed_two_endpoints (endpoints : Nat)
    (many : 28 ≤ endpoints) (only_two : endpoints ≤ 2) : False := by omega

#print axioms square_count_identity
#print axioms upper_254_of_census
#print axioms six_candidates_exceed_two_endpoints
end SquareCountingLogic
