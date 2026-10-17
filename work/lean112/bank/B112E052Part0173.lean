import B112E052Part0172
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c13062 : List Lit := [(27, false), (100, false), (122, false)]
theorem step13062 (p : Nat → Bool) (h : Constraints p) : clause p c13062 = true :=
  Snake9.LocalRup.prove_clause [c12139, c672] c13062 (by decide) p (sat_cons (step12139 p h) (sat_cons (step672 p h) (sat_nil p)))
def c13063 : List Lit := [(98, false), (99, false), (100, false)]
theorem step13063 (p : Nat → Bool) (h : Constraints p) : clause p c13063 = true :=
  Snake9.LocalRup.prove_clause [c12139, c1974] c13063 (by decide) p (sat_cons (step12139 p h) (sat_cons (step1974 p h) (sat_nil p)))
def c13064 : List Lit := [(44, false), (31, false), (27, false)]
theorem step13064 (p : Nat → Bool) (h : Constraints p) : clause p c13064 = true :=
  Snake9.LocalRup.prove_clause [c12139, c103] c13064 (by decide) p (sat_cons (step12139 p h) (sat_cons (step103 p h) (sat_nil p)))
def c13065 : List Lit := [(31, false), (104, false), (107, false)]
theorem step13065 (p : Nat → Bool) (h : Constraints p) : clause p c13065 = true :=
  Snake9.LocalRup.prove_clause [c12139, c770] c13065 (by decide) p (sat_cons (step12139 p h) (sat_cons (step770 p h) (sat_nil p)))
def c13066 : List Lit := [(113, false), (79, false), (122, false)]
theorem step13066 (p : Nat → Bool) (h : Constraints p) : clause p c13066 = true :=
  Snake9.LocalRup.prove_clause [c12139, c916] c13066 (by decide) p (sat_cons (step12139 p h) (sat_cons (step916 p h) (sat_nil p)))
def c13067 : List Lit := [(79, false), (62, false), (122, false)]
theorem step13067 (p : Nat → Bool) (h : Constraints p) : clause p c13067 = true :=
  Snake9.LocalRup.prove_clause [c12139, c1946] c13067 (by decide) p (sat_cons (step12139 p h) (sat_cons (step1946 p h) (sat_nil p)))
def c13068 : List Lit := [(107, false), (106, false), (100, false)]
theorem step13068 (p : Nat → Bool) (h : Constraints p) : clause p c13068 = true :=
  Snake9.LocalRup.prove_clause [c12139, c1976] c13068 (by decide) p (sat_cons (step12139 p h) (sat_cons (step1976 p h) (sat_nil p)))
def c13069 : List Lit := [(105, false), (99, false), (107, false)]
theorem step13069 (p : Nat → Bool) (h : Constraints p) : clause p c13069 = true :=
  Snake9.LocalRup.prove_clause [c12139, c1975] c13069 (by decide) p (sat_cons (step12139 p h) (sat_cons (step1975 p h) (sat_nil p)))
def c13070 : List Lit := [(107, false), (62, false), (122, false)]
theorem step13070 (p : Nat → Bool) (h : Constraints p) : clause p c13070 = true :=
  Snake9.LocalRup.prove_clause [c12139, c683] c13070 (by decide) p (sat_cons (step12139 p h) (sat_cons (step683 p h) (sat_nil p)))
def c13071 : List Lit := [(27, false), (107, false), (122, false)]
theorem step13071 (p : Nat → Bool) (h : Constraints p) : clause p c13071 = true :=
  Snake9.LocalRup.prove_clause [c12139, c673] c13071 (by decide) p (sat_cons (step12139 p h) (sat_cons (step673 p h) (sat_nil p)))
def c13072 : List Lit := [(107, false), (100, false), (90, false)]
theorem step13072 (p : Nat → Bool) (h : Constraints p) : clause p c13072 = true :=
  Snake9.LocalRup.prove_clause [c12139, c687] c13072 (by decide) p (sat_cons (step12139 p h) (sat_cons (step687 p h) (sat_nil p)))
def c13073 : List Lit := [(107, false), (122, false), (90, false)]
theorem step13073 (p : Nat → Bool) (h : Constraints p) : clause p c13073 = true :=
  Snake9.LocalRup.prove_clause [c12139, c689] c13073 (by decide) p (sat_cons (step12139 p h) (sat_cons (step689 p h) (sat_nil p)))
def c13074 : List Lit := [(107, false), (62, false), (90, false)]
theorem step13074 (p : Nat → Bool) (h : Constraints p) : clause p c13074 = true :=
  Snake9.LocalRup.prove_clause [c12139, c676] c13074 (by decide) p (sat_cons (step12139 p h) (sat_cons (step676 p h) (sat_nil p)))
def c13075 : List Lit := [(107, false), (27, false), (90, false)]
theorem step13075 (p : Nat → Bool) (h : Constraints p) : clause p c13075 = true :=
  Snake9.LocalRup.prove_clause [c12139, c666] c13075 (by decide) p (sat_cons (step12139 p h) (sat_cons (step666 p h) (sat_nil p)))
def c13076 : List Lit := [(27, false), (62, false), (107, false)]
theorem step13076 (p : Nat → Bool) (h : Constraints p) : clause p c13076 = true :=
  Snake9.LocalRup.prove_clause [c12139, c662] c13076 (by decide) p (sat_cons (step12139 p h) (sat_cons (step662 p h) (sat_nil p)))
def c13077 : List Lit := [(99, false), (107, false), (90, false)]
theorem step13077 (p : Nat → Bool) (h : Constraints p) : clause p c13077 = true :=
  Snake9.LocalRup.prove_clause [c12139, c685] c13077 (by decide) p (sat_cons (step12139 p h) (sat_cons (step685 p h) (sat_nil p)))
def c13078 : List Lit := [(100, false), (122, false), (90, false)]
theorem step13078 (p : Nat → Bool) (h : Constraints p) : clause p c13078 = true :=
  Snake9.LocalRup.prove_clause [c12139, c688] c13078 (by decide) p (sat_cons (step12139 p h) (sat_cons (step688 p h) (sat_nil p)))
def c13079 : List Lit := [(62, false), (122, false), (90, false)]
theorem step13079 (p : Nat → Bool) (h : Constraints p) : clause p c13079 = true :=
  Snake9.LocalRup.prove_clause [c12139, c677] c13079 (by decide) p (sat_cons (step12139 p h) (sat_cons (step677 p h) (sat_nil p)))
def c13080 : List Lit := [(113, false), (122, false), (90, false)]
theorem step13080 (p : Nat → Bool) (h : Constraints p) : clause p c13080 = true :=
  Snake9.LocalRup.prove_clause [c12139, c1966] c13080 (by decide) p (sat_cons (step12139 p h) (sat_cons (step1966 p h) (sat_nil p)))
def c13081 : List Lit := [(27, false), (122, false), (90, false)]
theorem step13081 (p : Nat → Bool) (h : Constraints p) : clause p c13081 = true :=
  Snake9.LocalRup.prove_clause [c12139, c667] c13081 (by decide) p (sat_cons (step12139 p h) (sat_cons (step667 p h) (sat_nil p)))
def c13082 : List Lit := [(27, false), (62, false), (90, false)]
theorem step13082 (p : Nat → Bool) (h : Constraints p) : clause p c13082 = true :=
  Snake9.LocalRup.prove_clause [c12139, c659] c13082 (by decide) p (sat_cons (step12139 p h) (sat_cons (step659 p h) (sat_nil p)))
def c13083 : List Lit := [(89, false), (100, false), (90, false)]
theorem step13083 (p : Nat → Bool) (h : Constraints p) : clause p c13083 = true :=
  Snake9.LocalRup.prove_clause [c12139, c1964] c13083 (by decide) p (sat_cons (step12139 p h) (sat_cons (step1964 p h) (sat_nil p)))
def c13084 : List Lit := [(89, false), (88, false), (90, false)]
theorem step13084 (p : Nat → Bool) (h : Constraints p) : clause p c13084 = true :=
  Snake9.LocalRup.prove_clause [c12139, c526] c13084 (by decide) p (sat_cons (step12139 p h) (sat_cons (step526 p h) (sat_nil p)))
def c13085 : List Lit := [(27, false), (44, false), (122, false)]
theorem step13085 (p : Nat → Bool) (h : Constraints p) : clause p c13085 = true :=
  Snake9.LocalRup.prove_clause [c12139, c1928] c13085 (by decide) p (sat_cons (step12139 p h) (sat_cons (step1928 p h) (sat_nil p)))
def c13086 : List Lit := [(121, false), (113, false), (122, false)]
theorem step13086 (p : Nat → Bool) (h : Constraints p) : clause p c13086 = true :=
  Snake9.LocalRup.prove_clause [c12139, c919] c13086 (by decide) p (sat_cons (step12139 p h) (sat_cons (step919 p h) (sat_nil p)))
def c13087 : List Lit := [(121, false), (79, false), (122, false)]
theorem step13087 (p : Nat → Bool) (h : Constraints p) : clause p c13087 = true :=
  Snake9.LocalRup.prove_clause [c12139, c917] c13087 (by decide) p (sat_cons (step12139 p h) (sat_cons (step917 p h) (sat_nil p)))
def c13088 : List Lit := [(27, false), (62, false), (122, false)]
theorem step13088 (p : Nat → Bool) (h : Constraints p) : clause p c13088 = true :=
  Snake9.LocalRup.prove_clause [c12139, c663] c13088 (by decide) p (sat_cons (step12139 p h) (sat_cons (step663 p h) (sat_nil p)))
def c13089 : List Lit := [(89, false), (100, false), (106, false)]
theorem step13089 (p : Nat → Bool) (h : Constraints p) : clause p c13089 = true :=
  Snake9.LocalRup.prove_clause [c12139, c653] c13089 (by decide) p (sat_cons (step12139 p h) (sat_cons (step653 p h) (sat_nil p)))
def c13090 : List Lit := [(98, false), (100, false), (106, false)]
theorem step13090 (p : Nat → Bool) (h : Constraints p) : clause p c13090 = true :=
  Snake9.LocalRup.prove_clause [c12139, c654] c13090 (by decide) p (sat_cons (step12139 p h) (sat_cons (step654 p h) (sat_nil p)))
def c13091 : List Lit := [(104, false), (106, false), (107, false)]
theorem step13091 (p : Nat → Bool) (h : Constraints p) : clause p c13091 = true :=
  Snake9.LocalRup.prove_clause [c12139, c780] c13091 (by decide) p (sat_cons (step12139 p h) (sat_cons (step780 p h) (sat_nil p)))
def c13092 : List Lit := [(105, false), (106, false), (107, false)]
theorem step13092 (p : Nat → Bool) (h : Constraints p) : clause p c13092 = true :=
  Snake9.LocalRup.prove_clause [c12139, c781] c13092 (by decide) p (sat_cons (step12139 p h) (sat_cons (step781 p h) (sat_nil p)))
def c13093 : List Lit := [(31, false), (26, false), (27, false)]
theorem step13093 (p : Nat → Bool) (h : Constraints p) : clause p c13093 = true :=
  Snake9.LocalRup.prove_clause [c12139, c102] c13093 (by decide) p (sat_cons (step12139 p h) (sat_cons (step102 p h) (sat_nil p)))
def c13094 : List Lit := [(105, false), (104, false), (107, false)]
theorem step13094 (p : Nat → Bool) (h : Constraints p) : clause p c13094 = true :=
  Snake9.LocalRup.prove_clause [c12139, c779] c13094 (by decide) p (sat_cons (step12139 p h) (sat_cons (step779 p h) (sat_nil p)))
def c13095 : List Lit := [(1796, true), (1812, true), (99, true), (102, true), (112, true)]
theorem step13095 (p : Nat → Bool) (h : Constraints p) : clause p c13095 = true :=
  Snake9.LocalRup.prove_clause [c12139, c3027] c13095 (by decide) p (sat_cons (step12139 p h) (sat_cons (step3027 p h) (sat_nil p)))
def c13096 : List Lit := [(1796, true), (1767, true), (100, false)]
theorem step13096 (p : Nat → Bool) (h : Constraints p) : clause p c13096 = true :=
  Snake9.LocalRup.prove_clause [c12139, c2965] c13096 (by decide) p (sat_cons (step12139 p h) (sat_cons (step2965 p h) (sat_nil p)))
def c13097 : List Lit := [(27, false), (1764, true), (96, true)]
theorem step13097 (p : Nat → Bool) (h : Constraints p) : clause p c13097 = true :=
  Snake9.LocalRup.prove_clause [c12139, c2789] c13097 (by decide) p (sat_cons (step12139 p h) (sat_cons (step2789 p h) (sat_nil p)))
def c13098 : List Lit := [(20, false), (124, true), (30, false), (1767, true)]
theorem step13098 (p : Nat → Bool) (h : Constraints p) : clause p c13098 = true :=
  Snake9.LocalRup.prove_clause [c12139, c2759] c13098 (by decide) p (sat_cons (step12139 p h) (sat_cons (step2759 p h) (sat_nil p)))
def c13099 : List Lit := [(1796, true), (1811, true), (1802, true), (114, true), (99, true), (112, false), (100, false)]
theorem step13099 (p : Nat → Bool) (h : Constraints p) : clause p c13099 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4250] c13099 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4250 p h) (sat_nil p)))
def c13100 : List Lit := [(1811, true), (1812, true), (99, true), (102, true), (122, false)]
theorem step13100 (p : Nat → Bool) (h : Constraints p) : clause p c13100 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4438] c13100 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4438 p h) (sat_nil p)))
def c13101 : List Lit := [(1777, true), (62, false), (1759, false), (122, false)]
theorem step13101 (p : Nat → Bool) (h : Constraints p) : clause p c13101 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4426] c13101 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4426 p h) (sat_nil p)))
def c13102 : List Lit := [(1778, true), (102, true), (1759, false), (62, false), (122, false)]
theorem step13102 (p : Nat → Bool) (h : Constraints p) : clause p c13102 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4409] c13102 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4409 p h) (sat_nil p)))
def c13103 : List Lit := [(80, false), (1642, true), (27, false), (1792, true), (100, false), (8, false)]
theorem step13103 (p : Nat → Bool) (h : Constraints p) : clause p c13103 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4209] c13103 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4209 p h) (sat_nil p)))
def c13104 : List Lit := [(1763, true), (90, false)]
theorem step13104 (p : Nat → Bool) (h : Constraints p) : clause p c13104 = true :=
  Snake9.LocalRup.prove_clause [c12139, c5250] c13104 (by decide) p (sat_cons (step12139 p h) (sat_cons (step5250 p h) (sat_nil p)))
def c13105 : List Lit := [(27, false), (1764, true), (90, false)]
theorem step13105 (p : Nat → Bool) (h : Constraints p) : clause p c13105 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4784] c13105 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4784 p h) (sat_nil p)))
def c13106 : List Lit := [(1776, true), (1761, false), (1763, false), (90, false)]
theorem step13106 (p : Nat → Bool) (h : Constraints p) : clause p c13106 = true :=
  Snake9.LocalRup.prove_clause [c12139, c5273] c13106 (by decide) p (sat_cons (step12139 p h) (sat_cons (step5273 p h) (sat_nil p)))
def c13107 : List Lit := [(27, false), (1780, true), (90, false), (1769, false), (103, true), (96, true), (1761, false)]
theorem step13107 (p : Nat → Bool) (h : Constraints p) : clause p c13107 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4970] c13107 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4970 p h) (sat_nil p)))
def c13108 : List Lit := [(1764, true), (96, true), (90, false)]
theorem step13108 (p : Nat → Bool) (h : Constraints p) : clause p c13108 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4825] c13108 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4825 p h) (sat_nil p)))
def c13109 : List Lit := [(102, true), (1765, true), (90, false), (96, true)]
theorem step13109 (p : Nat → Bool) (h : Constraints p) : clause p c13109 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4753] c13109 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4753 p h) (sat_nil p)))
def c13110 : List Lit := [(99, false), (1585, true), (90, false)]
theorem step13110 (p : Nat → Bool) (h : Constraints p) : clause p c13110 = true :=
  Snake9.LocalRup.prove_clause [c12139, c5160] c13110 (by decide) p (sat_cons (step12139 p h) (sat_cons (step5160 p h) (sat_nil p)))
def c13111 : List Lit := [(62, false), (1769, false), (96, true), (1761, false), (1780, true), (90, false), (103, true)]
theorem step13111 (p : Nat → Bool) (h : Constraints p) : clause p c13111 = true :=
  Snake9.LocalRup.prove_clause [c12139, c4969] c13111 (by decide) p (sat_cons (step12139 p h) (sat_cons (step4969 p h) (sat_nil p)))
def c13112 : List Lit := [(1776, true), (122, false)]
theorem step13112 (p : Nat → Bool) (h : Constraints p) : clause p c13112 = true :=
  Snake9.LocalRup.prove_clause [c12139, c5469] c13112 (by decide) p (sat_cons (step12139 p h) (sat_cons (step5469 p h) (sat_nil p)))
def c13113 : List Lit := [(53, false), (62, false), (18, true), (90, false), (1586, true)]
theorem step13113 (p : Nat → Bool) (h : Constraints p) : clause p c13113 = true :=
  Snake9.LocalRup.prove_clause [c12139, c5862] c13113 (by decide) p (sat_cons (step12139 p h) (sat_cons (step5862 p h) (sat_nil p)))
def c13114 : List Lit := [(53, false), (62, false), (18, true), (99, false), (1586, true)]
theorem step13114 (p : Nat → Bool) (h : Constraints p) : clause p c13114 = true :=
  Snake9.LocalRup.prove_clause [c12139, c5861] c13114 (by decide) p (sat_cons (step12139 p h) (sat_cons (step5861 p h) (sat_nil p)))
def c13115 : List Lit := [(27, false), (62, false), (1625, true), (35, true), (7, false), (1814, true), (1802, true), (46, false), (122, true), (1783, false), (3, false)]
theorem step13115 (p : Nat → Bool) (h : Constraints p) : clause p c13115 = true :=
  Snake9.LocalRup.prove_clause [c12139, c6013] c13115 (by decide) p (sat_cons (step12139 p h) (sat_cons (step6013 p h) (sat_nil p)))
def c13116 : List Lit := [(18, true), (46, false), (3, false), (90, false), (7, false), (1625, true), (27, true), (1586, true)]
theorem step13116 (p : Nat → Bool) (h : Constraints p) : clause p c13116 = true :=
  Snake9.LocalRup.prove_clause [c12139, c5882] c13116 (by decide) p (sat_cons (step12139 p h) (sat_cons (step5882 p h) (sat_nil p)))
def c13117 : List Lit := [(90, false), (1812, true)]
theorem step13117 (p : Nat → Bool) (h : Constraints p) : clause p c13117 = true :=
  Snake9.LocalRup.prove_clause [c12139, c9271] c13117 (by decide) p (sat_cons (step12139 p h) (sat_cons (step9271 p h) (sat_nil p)))
def c13118 : List Lit := [(114, true), (1812, true), (122, false), (112, false), (62, false), (99, true)]
theorem step13118 (p : Nat → Bool) (h : Constraints p) : clause p c13118 = true :=
  Snake9.LocalRup.prove_clause [c12139, c6815] c13118 (by decide) p (sat_cons (step12139 p h) (sat_cons (step6815 p h) (sat_nil p)))
def c13119 : List Lit := [(1763, true), (62, false)]
theorem step13119 (p : Nat → Bool) (h : Constraints p) : clause p c13119 = true :=
  Snake9.LocalRup.prove_clause [c12139, c6720] c13119 (by decide) p (sat_cons (step12139 p h) (sat_cons (step6720 p h) (sat_nil p)))
def c13120 : List Lit := [(1812, true), (1796, false), (102, true), (1767, false), (112, false), (122, true), (106, true)]
theorem step13120 (p : Nat → Bool) (h : Constraints p) : clause p c13120 = true :=
  Snake9.LocalRup.prove_clause [c12139, c9032] c13120 (by decide) p (sat_cons (step12139 p h) (sat_cons (step9032 p h) (sat_nil p)))
def c13121 : List Lit := [(1812, true), (1722, false), (99, false), (112, false), (122, false), (1767, false), (90, true), (100, true)]
theorem step13121 (p : Nat → Bool) (h : Constraints p) : clause p c13121 = true :=
  Snake9.LocalRup.prove_clause [c12139, c9118] c13121 (by decide) p (sat_cons (step12139 p h) (sat_cons (step9118 p h) (sat_nil p)))
def c13122 : List Lit := [(1722, true), (1812, true), (90, true)]
theorem step13122 (p : Nat → Bool) (h : Constraints p) : clause p c13122 = true :=
  Snake9.LocalRup.prove_clause [c12139, c9241] c13122 (by decide) p (sat_cons (step12139 p h) (sat_cons (step9241 p h) (sat_nil p)))
def c13123 : List Lit := [(1636, false), (107, false), (1598, true), (1681, true), (1571, false), (100, false)]
theorem step13123 (p : Nat → Bool) (h : Constraints p) : clause p c13123 = true :=
  Snake9.LocalRup.prove_clause [c12139, c9060] c13123 (by decide) p (sat_cons (step12139 p h) (sat_cons (step9060 p h) (sat_nil p)))
def c13124 : List Lit := [(1812, true), (112, true), (122, false), (1767, false)]
theorem step13124 (p : Nat → Bool) (h : Constraints p) : clause p c13124 = true :=
  Snake9.LocalRup.prove_clause [c12139, c9127] c13124 (by decide) p (sat_cons (step12139 p h) (sat_cons (step9127 p h) (sat_nil p)))
def c13125 : List Lit := [(1796, true), (1812, true), (122, true), (112, true)]
theorem step13125 (p : Nat → Bool) (h : Constraints p) : clause p c13125 = true :=
  Snake9.LocalRup.prove_clause [c12139, c9079] c13125 (by decide) p (sat_cons (step12139 p h) (sat_cons (step9079 p h) (sat_nil p)))
end B112E052
