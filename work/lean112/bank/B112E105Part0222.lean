import B112E105Part0221
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c16137 : List Lit := [(122, true), (123, true), (101, true), (66, true), (110, true), (83, true)]
theorem step16137 (p : Nat → Bool) (h : Constraints p) : clause p c16137 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2196] c16137 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2196 p h) (sat_nil p)))
def c16138 : List Lit := [(1741, false), (1754, true)]
theorem step16138 (p : Nat → Bool) (h : Constraints p) : clause p c16138 = true :=
  Snake9.LocalRup.prove_clause [c13901, c1734] c16138 (by decide) p (sat_cons (step13901 p h) (sat_cons (step1734 p h) (sat_nil p)))
def c16139 : List Lit := [(1740, false), (1753, true)]
theorem step16139 (p : Nat → Bool) (h : Constraints p) : clause p c16139 = true :=
  Snake9.LocalRup.prove_clause [c13901, c1729] c16139 (by decide) p (sat_cons (step13901 p h) (sat_cons (step1729 p h) (sat_nil p)))
def c16140 : List Lit := [(97, false), (94, false), (101, false)]
theorem step16140 (p : Nat → Bool) (h : Constraints p) : clause p c16140 = true :=
  Snake9.LocalRup.prove_clause [c13899, c567] c16140 (by decide) p (sat_cons (step13899 p h) (sat_cons (step567 p h) (sat_nil p)))
def c16141 : List Lit := [(123, false), (110, false), (112, false)]
theorem step16141 (p : Nat → Bool) (h : Constraints p) : clause p c16141 = true :=
  Snake9.LocalRup.prove_clause [c13899, c1922] c16141 (by decide) p (sat_cons (step13899 p h) (sat_cons (step1922 p h) (sat_nil p)))
def c16142 : List Lit := [(1748, true), (110, false)]
theorem step16142 (p : Nat → Bool) (h : Constraints p) : clause p c16142 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2058] c16142 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2058 p h) (sat_nil p)))
def c16143 : List Lit := [(110, false), (55, false), (66, false)]
theorem step16143 (p : Nat → Bool) (h : Constraints p) : clause p c16143 = true :=
  Snake9.LocalRup.prove_clause [c13899, c1888] c16143 (by decide) p (sat_cons (step13899 p h) (sat_cons (step1888 p h) (sat_nil p)))
def c16144 : List Lit := [(117, false), (110, false), (66, false)]
theorem step16144 (p : Nat → Bool) (h : Constraints p) : clause p c16144 = true :=
  Snake9.LocalRup.prove_clause [c13899, c884] c16144 (by decide) p (sat_cons (step13899 p h) (sat_cons (step884 p h) (sat_nil p)))
def c16145 : List Lit := [(123, false), (110, false), (101, false)]
theorem step16145 (p : Nat → Bool) (h : Constraints p) : clause p c16145 = true :=
  Snake9.LocalRup.prove_clause [c13899, c902] c16145 (by decide) p (sat_cons (step13899 p h) (sat_cons (step902 p h) (sat_nil p)))
def c16146 : List Lit := [(110, false), (83, false), (66, false)]
theorem step16146 (p : Nat → Bool) (h : Constraints p) : clause p c16146 = true :=
  Snake9.LocalRup.prove_clause [c13899, c876] c16146 (by decide) p (sat_cons (step13899 p h) (sat_cons (step876 p h) (sat_nil p)))
def c16147 : List Lit := [(117, false), (110, false), (101, false)]
theorem step16147 (p : Nat → Bool) (h : Constraints p) : clause p c16147 = true :=
  Snake9.LocalRup.prove_clause [c13899, c900] c16147 (by decide) p (sat_cons (step13899 p h) (sat_cons (step900 p h) (sat_nil p)))
def c16148 : List Lit := [(122, false), (110, false), (101, false)]
theorem step16148 (p : Nat → Bool) (h : Constraints p) : clause p c16148 = true :=
  Snake9.LocalRup.prove_clause [c13899, c901] c16148 (by decide) p (sat_cons (step13899 p h) (sat_cons (step901 p h) (sat_nil p)))
def c16149 : List Lit := [(122, false), (118, false), (117, false)]
theorem step16149 (p : Nat → Bool) (h : Constraints p) : clause p c16149 = true :=
  Snake9.LocalRup.prove_clause [c13899, c1927] c16149 (by decide) p (sat_cons (step13899 p h) (sat_cons (step1927 p h) (sat_nil p)))
def c16150 : List Lit := [(124, false), (122, false), (123, false)]
theorem step16150 (p : Nat → Bool) (h : Constraints p) : clause p c16150 = true :=
  Snake9.LocalRup.prove_clause [c13899, c1928] c16150 (by decide) p (sat_cons (step13899 p h) (sat_cons (step1928 p h) (sat_nil p)))
def c16151 : List Lit := [(111, false), (122, false), (118, false)]
theorem step16151 (p : Nat → Bool) (h : Constraints p) : clause p c16151 = true :=
  Snake9.LocalRup.prove_clause [c13899, c919] c16151 (by decide) p (sat_cons (step13899 p h) (sat_cons (step919 p h) (sat_nil p)))
def c16152 : List Lit := [(117, false), (101, false), (83, false)]
theorem step16152 (p : Nat → Bool) (h : Constraints p) : clause p c16152 = true :=
  Snake9.LocalRup.prove_clause [c13899, c891] c16152 (by decide) p (sat_cons (step13899 p h) (sat_cons (step891 p h) (sat_nil p)))
def c16153 : List Lit := [(94, false), (117, false), (101, false)]
theorem step16153 (p : Nat → Bool) (h : Constraints p) : clause p c16153 = true :=
  Snake9.LocalRup.prove_clause [c13899, c1910] c16153 (by decide) p (sat_cons (step13899 p h) (sat_cons (step1910 p h) (sat_nil p)))
def c16154 : List Lit := [(117, false), (110, false), (1746, true)]
theorem step16154 (p : Nat → Bool) (h : Constraints p) : clause p c16154 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2056] c16154 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2056 p h) (sat_nil p)))
def c16155 : List Lit := [(117, false), (110, false), (83, false)]
theorem step16155 (p : Nat → Bool) (h : Constraints p) : clause p c16155 = true :=
  Snake9.LocalRup.prove_clause [c13899, c894] c16155 (by decide) p (sat_cons (step13899 p h) (sat_cons (step894 p h) (sat_nil p)))
def c16156 : List Lit := [(119, false), (118, false), (117, false)]
theorem step16156 (p : Nat → Bool) (h : Constraints p) : clause p c16156 = true :=
  Snake9.LocalRup.prove_clause [c13899, c817] c16156 (by decide) p (sat_cons (step13899 p h) (sat_cons (step817 p h) (sat_nil p)))
def c16157 : List Lit := [(118, false), (114, false), (117, false)]
theorem step16157 (p : Nat → Bool) (h : Constraints p) : clause p c16157 = true :=
  Snake9.LocalRup.prove_clause [c13899, c815] c16157 (by decide) p (sat_cons (step13899 p h) (sat_cons (step815 p h) (sat_nil p)))
def c16158 : List Lit := [(117, false), (83, false), (66, false)]
theorem step16158 (p : Nat → Bool) (h : Constraints p) : clause p c16158 = true :=
  Snake9.LocalRup.prove_clause [c13899, c877] c16158 (by decide) p (sat_cons (step13899 p h) (sat_cons (step877 p h) (sat_nil p)))
def c16159 : List Lit := [(77, false), (117, false), (83, false)]
theorem step16159 (p : Nat → Bool) (h : Constraints p) : clause p c16159 = true :=
  Snake9.LocalRup.prove_clause [c13899, c1901] c16159 (by decide) p (sat_cons (step13899 p h) (sat_cons (step1901 p h) (sat_nil p)))
def c16160 : List Lit := [(119, false), (117, false), (114, false)]
theorem step16160 (p : Nat → Bool) (h : Constraints p) : clause p c16160 = true :=
  Snake9.LocalRup.prove_clause [c13899, c816] c16160 (by decide) p (sat_cons (step13899 p h) (sat_cons (step816 p h) (sat_nil p)))
def c16161 : List Lit := [(94, false), (77, false), (117, false)]
theorem step16161 (p : Nat → Bool) (h : Constraints p) : clause p c16161 = true :=
  Snake9.LocalRup.prove_clause [c13899, c805] c16161 (by decide) p (sat_cons (step13899 p h) (sat_cons (step805 p h) (sat_nil p)))
def c16162 : List Lit := [(94, false), (119, false), (117, false)]
theorem step16162 (p : Nat → Bool) (h : Constraints p) : clause p c16162 = true :=
  Snake9.LocalRup.prove_clause [c13899, c813] c16162 (by decide) p (sat_cons (step13899 p h) (sat_cons (step813 p h) (sat_nil p)))
def c16163 : List Lit := [(190, false), (63, false)]
theorem step16163 (p : Nat → Bool) (h : Constraints p) : clause p c16163 = true :=
  Snake9.LocalRup.prove_clause [c13899, c384] c16163 (by decide) p (sat_cons (step13899 p h) (sat_cons (step384 p h) (sat_nil p)))
def c16164 : List Lit := [(66, false), (1748, true)]
theorem step16164 (p : Nat → Bool) (h : Constraints p) : clause p c16164 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2451] c16164 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2451 p h) (sat_nil p)))
def c16165 : List Lit := [(1732, false), (1766, true)]
theorem step16165 (p : Nat → Bool) (h : Constraints p) : clause p c16165 = true :=
  Snake9.LocalRup.prove_clause [c13900, c1784] c16165 (by decide) p (sat_cons (step13900 p h) (sat_cons (step1784 p h) (sat_nil p)))
def c16166 : List Lit := [(123, false), (110, false), (83, false)]
theorem step16166 (p : Nat → Bool) (h : Constraints p) : clause p c16166 = true :=
  Snake9.LocalRup.prove_clause [c13899, c896] c16166 (by decide) p (sat_cons (step13899 p h) (sat_cons (step896 p h) (sat_nil p)))
def c16167 : List Lit := [(119, false), (123, false), (112, false)]
theorem step16167 (p : Nat → Bool) (h : Constraints p) : clause p c16167 = true :=
  Snake9.LocalRup.prove_clause [c13899, c929] c16167 (by decide) p (sat_cons (step13899 p h) (sat_cons (step929 p h) (sat_nil p)))
def c16168 : List Lit := [(123, false), (101, false), (83, false)]
theorem step16168 (p : Nat → Bool) (h : Constraints p) : clause p c16168 = true :=
  Snake9.LocalRup.prove_clause [c13899, c893] c16168 (by decide) p (sat_cons (step13899 p h) (sat_cons (step893 p h) (sat_nil p)))
def c16169 : List Lit := [(80, false), (77, false), (83, false)]
theorem step16169 (p : Nat → Bool) (h : Constraints p) : clause p c16169 = true :=
  Snake9.LocalRup.prove_clause [c13899, c472] c16169 (by decide) p (sat_cons (step13899 p h) (sat_cons (step472 p h) (sat_nil p)))
def c16170 : List Lit := [(1765, true), (1731, false)]
theorem step16170 (p : Nat → Bool) (h : Constraints p) : clause p c16170 = true :=
  Snake9.LocalRup.prove_clause [c13900, c1775] c16170 (by decide) p (sat_cons (step13900 p h) (sat_cons (step1775 p h) (sat_nil p)))
def c16171 : List Lit := [(1764, true), (1730, false)]
theorem step16171 (p : Nat → Bool) (h : Constraints p) : clause p c16171 = true :=
  Snake9.LocalRup.prove_clause [c13900, c1767] c16171 (by decide) p (sat_cons (step13900 p h) (sat_cons (step1767 p h) (sat_nil p)))
def c16172 : List Lit := [(1754, true), (66, false), (83, false)]
theorem step16172 (p : Nat → Bool) (h : Constraints p) : clause p c16172 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2491] c16172 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2491 p h) (sat_nil p)))
def c16173 : List Lit := [(1746, true), (101, false), (83, false)]
theorem step16173 (p : Nat → Bool) (h : Constraints p) : clause p c16173 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2529] c16173 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2529 p h) (sat_nil p)))
def c16174 : List Lit := [(80, false), (77, false), (81, true)]
theorem step16174 (p : Nat → Bool) (h : Constraints p) : clause p c16174 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2534] c16174 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2534 p h) (sat_nil p)))
def c16175 : List Lit := [(1762, true), (225, true), (1723, false)]
theorem step16175 (p : Nat → Bool) (h : Constraints p) : clause p c16175 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2542] c16175 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2542 p h) (sat_nil p)))
def c16176 : List Lit := [(101, false), (66, false), (1754, true)]
theorem step16176 (p : Nat → Bool) (h : Constraints p) : clause p c16176 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2530] c16176 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2530 p h) (sat_nil p)))
def c16177 : List Lit := [(1763, true), (66, false), (1753, false), (1723, false)]
theorem step16177 (p : Nat → Bool) (h : Constraints p) : clause p c16177 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2540] c16177 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2540 p h) (sat_nil p)))
def c16178 : List Lit := [(1762, true), (453, true)]
theorem step16178 (p : Nat → Bool) (h : Constraints p) : clause p c16178 = true :=
  Snake9.LocalRup.prove_clause [c13900, c2572] c16178 (by decide) p (sat_cons (step13900 p h) (sat_cons (step2572 p h) (sat_nil p)))
def c16179 : List Lit := [(1748, true), (83, false)]
theorem step16179 (p : Nat → Bool) (h : Constraints p) : clause p c16179 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3189] c16179 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3189 p h) (sat_nil p)))
def c16180 : List Lit := [(1748, true), (116, true)]
theorem step16180 (p : Nat → Bool) (h : Constraints p) : clause p c16180 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2623] c16180 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2623 p h) (sat_nil p)))
def c16181 : List Lit := [(1785, true), (66, false), (1754, false), (1729, false), (1654, false), (1666, false), (104, false)]
theorem step16181 (p : Nat → Bool) (h : Constraints p) : clause p c16181 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3325] c16181 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3325 p h) (sat_nil p)))
def c16182 : List Lit := [(1745, true), (110, false)]
theorem step16182 (p : Nat → Bool) (h : Constraints p) : clause p c16182 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3153] c16182 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3153 p h) (sat_nil p)))
def c16183 : List Lit := [(1737, false), (1754, true), (108, true)]
theorem step16183 (p : Nat → Bool) (h : Constraints p) : clause p c16183 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3187] c16183 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3187 p h) (sat_nil p)))
def c16184 : List Lit := [(1737, false), (83, false), (1755, true), (108, true)]
theorem step16184 (p : Nat → Bool) (h : Constraints p) : clause p c16184 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3491] c16184 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3491 p h) (sat_nil p)))
def c16185 : List Lit := [(1746, true), (83, false), (66, false)]
theorem step16185 (p : Nat → Bool) (h : Constraints p) : clause p c16185 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3216] c16185 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3216 p h) (sat_nil p)))
def c16186 : List Lit := [(1754, true), (66, false), (1743, false), (108, true)]
theorem step16186 (p : Nat → Bool) (h : Constraints p) : clause p c16186 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3274] c16186 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3274 p h) (sat_nil p)))
def c16187 : List Lit := [(1749, true), (116, true), (66, false)]
theorem step16187 (p : Nat → Bool) (h : Constraints p) : clause p c16187 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2669] c16187 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2669 p h) (sat_nil p)))
def c16188 : List Lit := [(116, true), (1741, false), (88, false), (83, false), (66, false), (93, false), (1769, true), (1724, false)]
theorem step16188 (p : Nat → Bool) (h : Constraints p) : clause p c16188 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3389] c16188 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3389 p h) (sat_nil p)))
def c16189 : List Lit := [(1717, false), (1740, false), (104, false), (66, false), (1724, false), (85, false), (1768, true)]
theorem step16189 (p : Nat → Bool) (h : Constraints p) : clause p c16189 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3428] c16189 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3428 p h) (sat_nil p)))
def c16190 : List Lit := [(1741, false), (116, true), (1724, false), (66, false), (1768, true), (83, false)]
theorem step16190 (p : Nat → Bool) (h : Constraints p) : clause p c16190 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3384] c16190 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3384 p h) (sat_nil p)))
def c16191 : List Lit := [(101, false), (116, true), (1750, true), (66, false)]
theorem step16191 (p : Nat → Bool) (h : Constraints p) : clause p c16191 = true :=
  Snake9.LocalRup.prove_clause [c13899, c2609] c16191 (by decide) p (sat_cons (step13899 p h) (sat_cons (step2609 p h) (sat_nil p)))
def c16192 : List Lit := [(1746, true), (110, false), (66, false)]
theorem step16192 (p : Nat → Bool) (h : Constraints p) : clause p c16192 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3276] c16192 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3276 p h) (sat_nil p)))
def c16193 : List Lit := [(122, false), (1716, true), (95, true), (225, true)]
theorem step16193 (p : Nat → Bool) (h : Constraints p) : clause p c16193 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3104] c16193 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3104 p h) (sat_nil p)))
def c16194 : List Lit := [(101, false), (83, false), (1749, true)]
theorem step16194 (p : Nat → Bool) (h : Constraints p) : clause p c16194 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3182] c16194 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3182 p h) (sat_nil p)))
def c16195 : List Lit := [(101, false), (1754, true), (83, false)]
theorem step16195 (p : Nat → Bool) (h : Constraints p) : clause p c16195 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3204] c16195 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3204 p h) (sat_nil p)))
def c16196 : List Lit := [(1737, false), (83, false), (1754, true)]
theorem step16196 (p : Nat → Bool) (h : Constraints p) : clause p c16196 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3871] c16196 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3871 p h) (sat_nil p)))
def c16197 : List Lit := [(101, false), (1737, false), (1754, true)]
theorem step16197 (p : Nat → Bool) (h : Constraints p) : clause p c16197 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3876] c16197 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3876 p h) (sat_nil p)))
def c16198 : List Lit := [(1715, true), (1682, false), (1690, true), (421, true), (112, true), (66, false)]
theorem step16198 (p : Nat → Bool) (h : Constraints p) : clause p c16198 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3569] c16198 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3569 p h) (sat_nil p)))
def c16199 : List Lit := [(116, true), (95, true), (1740, false), (1725, false), (1768, true), (66, false)]
theorem step16199 (p : Nat → Bool) (h : Constraints p) : clause p c16199 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3538] c16199 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3538 p h) (sat_nil p)))
def c16200 : List Lit := [(101, false), (1684, true), (489, true)]
theorem step16200 (p : Nat → Bool) (h : Constraints p) : clause p c16200 = true :=
  Snake9.LocalRup.prove_clause [c13899, c3877] c16200 (by decide) p (sat_cons (step13899 p h) (sat_cons (step3877 p h) (sat_nil p)))
end B112E105
