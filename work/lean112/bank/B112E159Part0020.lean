import B112E159Part0019
namespace B112E159
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2285 : List Lit := [(41, false), (926, true), (14, true)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c2211, c2284, c1040, c1223, c686, c1042, c1892, c695, c694, c2247, c1986, c2252, c1246, c1243, c569, c1244, c1032, c672, c586, c642, c779, c744, c739, c673, c1043, c664, c689, c1197] c2285 (by decide) p (sat_cons (step2211 p h) (sat_cons (step2284 p h) (sat_cons (step1040 p h) (sat_cons (step1223 p h) (sat_cons (step686 p h) (sat_cons (step1042 p h) (sat_cons (step1892 p h) (sat_cons (step695 p h) (sat_cons (step694 p h) (sat_cons (step2247 p h) (sat_cons (step1986 p h) (sat_cons (step2252 p h) (sat_cons (step1246 p h) (sat_cons (step1243 p h) (sat_cons (step569 p h) (sat_cons (step1244 p h) (sat_cons (step1032 p h) (sat_cons (step672 p h) (sat_cons (step586 p h) (sat_cons (step642 p h) (sat_cons (step779 p h) (sat_cons (step744 p h) (sat_cons (step739 p h) (sat_cons (step673 p h) (sat_cons (step1043 p h) (sat_cons (step664 p h) (sat_cons (step689 p h) (sat_cons (step1197 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2286 : List Lit := [(904, true), (862, false), (893, false), (14, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c2284, c1040, c1892, c1388, c1223, c2247, c734, c739, c1044, c672, c692, c1834] c2286 (by decide) p (sat_cons (step2284 p h) (sat_cons (step1040 p h) (sat_cons (step1892 p h) (sat_cons (step1388 p h) (sat_cons (step1223 p h) (sat_cons (step2247 p h) (sat_cons (step734 p h) (sat_cons (step739 p h) (sat_cons (step1044 p h) (sat_cons (step672 p h) (sat_cons (step692 p h) (sat_cons (step1834 p h) (sat_nil p)))))))))))))
def c2287 : List Lit := [(862, false), (926, true), (14, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c2213, c2211, c2284, c1040, c1223, c2285, c681, c689, c1043, c694, c2137, c774, c1892, c1986, c2072, c569, c1032, c1382, c2286, c779, c642, c638, c586, c1988, c1839, c596] c2287 (by decide) p (sat_cons (step2213 p h) (sat_cons (step2211 p h) (sat_cons (step2284 p h) (sat_cons (step1040 p h) (sat_cons (step1223 p h) (sat_cons (step2285 p h) (sat_cons (step681 p h) (sat_cons (step689 p h) (sat_cons (step1043 p h) (sat_cons (step694 p h) (sat_cons (step2137 p h) (sat_cons (step774 p h) (sat_cons (step1892 p h) (sat_cons (step1986 p h) (sat_cons (step2072 p h) (sat_cons (step569 p h) (sat_cons (step1032 p h) (sat_cons (step1382 p h) (sat_cons (step2286 p h) (sat_cons (step779 p h) (sat_cons (step642 p h) (sat_cons (step638 p h) (sat_cons (step586 p h) (sat_cons (step1988 p h) (sat_cons (step1839 p h) (sat_cons (step596 p h) (sat_nil p)))))))))))))))))))))))))))
def c2288 : List Lit := [(926, true), (14, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c2214, c2213, c2284, c1040, c1892, c1388, c694, c2137, c695, c703, c774, c2285, c681, c2287, c656, c1179, c2242, c226, c595, c1334, c1988, c255, c685, c690, c1044, c734, c779, c634, c638, c1708, c584, c597, c1839] c2288 (by decide) p (sat_cons (step2214 p h) (sat_cons (step2213 p h) (sat_cons (step2284 p h) (sat_cons (step1040 p h) (sat_cons (step1892 p h) (sat_cons (step1388 p h) (sat_cons (step694 p h) (sat_cons (step2137 p h) (sat_cons (step695 p h) (sat_cons (step703 p h) (sat_cons (step774 p h) (sat_cons (step2285 p h) (sat_cons (step681 p h) (sat_cons (step2287 p h) (sat_cons (step656 p h) (sat_cons (step1179 p h) (sat_cons (step2242 p h) (sat_cons (step226 p h) (sat_cons (step595 p h) (sat_cons (step1334 p h) (sat_cons (step1988 p h) (sat_cons (step255 p h) (sat_cons (step685 p h) (sat_cons (step690 p h) (sat_cons (step1044 p h) (sat_cons (step734 p h) (sat_cons (step779 p h) (sat_cons (step634 p h) (sat_cons (step638 p h) (sat_cons (step1708 p h) (sat_cons (step584 p h) (sat_cons (step597 p h) (sat_cons (step1839 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2289 : List Lit := [(14, true)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1945, c2284, c700, c1040, c1038, c2075, c2288, c1400, c1925, c957, c1733, c1907, c1791, c1712, c866, c862, c859, c860, c344, c864, c1110, c1053, c1502, c826] c2289 (by decide) p (sat_cons (step1945 p h) (sat_cons (step2284 p h) (sat_cons (step700 p h) (sat_cons (step1040 p h) (sat_cons (step1038 p h) (sat_cons (step2075 p h) (sat_cons (step2288 p h) (sat_cons (step1400 p h) (sat_cons (step1925 p h) (sat_cons (step957 p h) (sat_cons (step1733 p h) (sat_cons (step1907 p h) (sat_cons (step1791 p h) (sat_cons (step1712 p h) (sat_cons (step866 p h) (sat_cons (step862 p h) (sat_cons (step859 p h) (sat_cons (step860 p h) (sat_cons (step344 p h) (sat_cons (step864 p h) (sat_cons (step1110 p h) (sat_cons (step1053 p h) (sat_cons (step1502 p h) (sat_cons (step826 p h) (sat_nil p)))))))))))))))))))))))))
def c2290 : List Lit := [(41, false), (857, false), (926, true), (888, false)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c2211, c1943, c2289, c2006, c1968, c2140, c688, c57, c1296, c1297, c2142, c131, c150, c1654, c569, c774, c1032, c641, c1382, c586, c636, c637, c1380, c1246, c767, c766, c610, c1894, c573, c1399, c602, c596, c184, c1926, c1974, c1055, c2002, c2013, c746, c2074, c2024, c714, c1673, c711, c958, c862, c689, c1038, c1041, c1712, c684, c696, c860, c1335, c92, c207, c600] c2290 (by decide) p (sat_cons (step2211 p h) (sat_cons (step1943 p h) (sat_cons (step2289 p h) (sat_cons (step2006 p h) (sat_cons (step1968 p h) (sat_cons (step2140 p h) (sat_cons (step688 p h) (sat_cons (step57 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step2142 p h) (sat_cons (step131 p h) (sat_cons (step150 p h) (sat_cons (step1654 p h) (sat_cons (step569 p h) (sat_cons (step774 p h) (sat_cons (step1032 p h) (sat_cons (step641 p h) (sat_cons (step1382 p h) (sat_cons (step586 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step1380 p h) (sat_cons (step1246 p h) (sat_cons (step767 p h) (sat_cons (step766 p h) (sat_cons (step610 p h) (sat_cons (step1894 p h) (sat_cons (step573 p h) (sat_cons (step1399 p h) (sat_cons (step602 p h) (sat_cons (step596 p h) (sat_cons (step184 p h) (sat_cons (step1926 p h) (sat_cons (step1974 p h) (sat_cons (step1055 p h) (sat_cons (step2002 p h) (sat_cons (step2013 p h) (sat_cons (step746 p h) (sat_cons (step2074 p h) (sat_cons (step2024 p h) (sat_cons (step714 p h) (sat_cons (step1673 p h) (sat_cons (step711 p h) (sat_cons (step958 p h) (sat_cons (step862 p h) (sat_cons (step689 p h) (sat_cons (step1038 p h) (sat_cons (step1041 p h) (sat_cons (step1712 p h) (sat_cons (step684 p h) (sat_cons (step696 p h) (sat_cons (step860 p h) (sat_cons (step1335 p h) (sat_cons (step92 p h) (sat_cons (step207 p h) (sat_cons (step600 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2291 : List Lit := [(857, false), (926, true), (888, false)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c2214, c2211, c2289, c1968, c2140, c1643, c2006, c2290, c682, c1938, c1287, c1695, c1296, c1295, c2148, c569, c53, c95, c921, c1032, c596, c858, c1382, c1894, c861, c637, c1761, c773, c1399, c1926, c958, c1780, c1691, c1791, c864, c866, c2107] c2291 (by decide) p (sat_cons (step2214 p h) (sat_cons (step2211 p h) (sat_cons (step2289 p h) (sat_cons (step1968 p h) (sat_cons (step2140 p h) (sat_cons (step1643 p h) (sat_cons (step2006 p h) (sat_cons (step2290 p h) (sat_cons (step682 p h) (sat_cons (step1938 p h) (sat_cons (step1287 p h) (sat_cons (step1695 p h) (sat_cons (step1296 p h) (sat_cons (step1295 p h) (sat_cons (step2148 p h) (sat_cons (step569 p h) (sat_cons (step53 p h) (sat_cons (step95 p h) (sat_cons (step921 p h) (sat_cons (step1032 p h) (sat_cons (step596 p h) (sat_cons (step858 p h) (sat_cons (step1382 p h) (sat_cons (step1894 p h) (sat_cons (step861 p h) (sat_cons (step637 p h) (sat_cons (step1761 p h) (sat_cons (step773 p h) (sat_cons (step1399 p h) (sat_cons (step1926 p h) (sat_cons (step958 p h) (sat_cons (step1780 p h) (sat_cons (step1691 p h) (sat_cons (step1791 p h) (sat_cons (step864 p h) (sat_cons (step866 p h) (sat_cons (step2107 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c2292 : List Lit := [(41, false), (926, true), (888, false)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c2289, c2211, c1968, c2291, c1951, c596, c1894, c647, c645, c1770, c1937, c779, c642, c649, c644, c121, c1310, c41, c1425, c604, c2140, c688, c710, c131, c1722, c569, c1032, c1382, c586, c638, c637, c615, c774, c590, c745, c587, c669, c2011, c665, c1549, c657] c2292 (by decide) p (sat_cons (step2289 p h) (sat_cons (step2211 p h) (sat_cons (step1968 p h) (sat_cons (step2291 p h) (sat_cons (step1951 p h) (sat_cons (step596 p h) (sat_cons (step1894 p h) (sat_cons (step647 p h) (sat_cons (step645 p h) (sat_cons (step1770 p h) (sat_cons (step1937 p h) (sat_cons (step779 p h) (sat_cons (step642 p h) (sat_cons (step649 p h) (sat_cons (step644 p h) (sat_cons (step121 p h) (sat_cons (step1310 p h) (sat_cons (step41 p h) (sat_cons (step1425 p h) (sat_cons (step604 p h) (sat_cons (step2140 p h) (sat_cons (step688 p h) (sat_cons (step710 p h) (sat_cons (step131 p h) (sat_cons (step1722 p h) (sat_cons (step569 p h) (sat_cons (step1032 p h) (sat_cons (step1382 p h) (sat_cons (step586 p h) (sat_cons (step638 p h) (sat_cons (step637 p h) (sat_cons (step615 p h) (sat_cons (step774 p h) (sat_cons (step590 p h) (sat_cons (step745 p h) (sat_cons (step587 p h) (sat_cons (step669 p h) (sat_cons (step2011 p h) (sat_cons (step665 p h) (sat_cons (step1549 p h) (sat_cons (step657 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c2293 : List Lit := [(926, true), (888, false)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c2214, c2213, c2289, c1968, c2291, c647, c649, c1892, c1951, c644, c645, c596, c121, c1770, c56, c1894, c1310, c1938, c1297, c632, c41, c94, c767, c655, c2292, c682, c691, c1995, c1964, c133, c130, c129, c1399, c654, c1926, c664, c668, c741, c1540, c715, c2074, c2024, c702, c958, c862, c1038, c860, c1712] c2293 (by decide) p (sat_cons (step2214 p h) (sat_cons (step2213 p h) (sat_cons (step2289 p h) (sat_cons (step1968 p h) (sat_cons (step2291 p h) (sat_cons (step647 p h) (sat_cons (step649 p h) (sat_cons (step1892 p h) (sat_cons (step1951 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step596 p h) (sat_cons (step121 p h) (sat_cons (step1770 p h) (sat_cons (step56 p h) (sat_cons (step1894 p h) (sat_cons (step1310 p h) (sat_cons (step1938 p h) (sat_cons (step1297 p h) (sat_cons (step632 p h) (sat_cons (step41 p h) (sat_cons (step94 p h) (sat_cons (step767 p h) (sat_cons (step655 p h) (sat_cons (step2292 p h) (sat_cons (step682 p h) (sat_cons (step691 p h) (sat_cons (step1995 p h) (sat_cons (step1964 p h) (sat_cons (step133 p h) (sat_cons (step130 p h) (sat_cons (step129 p h) (sat_cons (step1399 p h) (sat_cons (step654 p h) (sat_cons (step1926 p h) (sat_cons (step664 p h) (sat_cons (step668 p h) (sat_cons (step741 p h) (sat_cons (step1540 p h) (sat_cons (step715 p h) (sat_cons (step2074 p h) (sat_cons (step2024 p h) (sat_cons (step702 p h) (sat_cons (step958 p h) (sat_cons (step862 p h) (sat_cons (step1038 p h) (sat_cons (step860 p h) (sat_cons (step1712 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c2294 : List Lit := [(1024, true), (1056, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1945, c957, c1791, c1513, c2069, c1502, c825, c826, c302] c2294 (by decide) p (sat_cons (step1945 p h) (sat_cons (step957 p h) (sat_cons (step1791 p h) (sat_cons (step1513 p h) (sat_cons (step2069 p h) (sat_cons (step1502 p h) (sat_cons (step825 p h) (sat_cons (step826 p h) (sat_cons (step302 p h) (sat_nil p))))))))))
def c2295 : List Lit := [(857, false), (888, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1945, c2211, c1943, c1947, c2289, c2293, c1400, c2220, c2294, c2014, c133, c569, c1032, c1382, c636, c768, c148, c145, c654, c151, c150, c682, c957, c1925, c1968, c1962, c1399, c2281, c859, c1712, c1038, c2159, c1223, c692, c718, c747, c2002, c644, c645, c2243] c2295 (by decide) p (sat_cons (step1945 p h) (sat_cons (step2211 p h) (sat_cons (step1943 p h) (sat_cons (step1947 p h) (sat_cons (step2289 p h) (sat_cons (step2293 p h) (sat_cons (step1400 p h) (sat_cons (step2220 p h) (sat_cons (step2294 p h) (sat_cons (step2014 p h) (sat_cons (step133 p h) (sat_cons (step569 p h) (sat_cons (step1032 p h) (sat_cons (step1382 p h) (sat_cons (step636 p h) (sat_cons (step768 p h) (sat_cons (step148 p h) (sat_cons (step145 p h) (sat_cons (step654 p h) (sat_cons (step151 p h) (sat_cons (step150 p h) (sat_cons (step682 p h) (sat_cons (step957 p h) (sat_cons (step1925 p h) (sat_cons (step1968 p h) (sat_cons (step1962 p h) (sat_cons (step1399 p h) (sat_cons (step2281 p h) (sat_cons (step859 p h) (sat_cons (step1712 p h) (sat_cons (step1038 p h) (sat_cons (step2159 p h) (sat_cons (step1223 p h) (sat_cons (step692 p h) (sat_cons (step718 p h) (sat_cons (step747 p h) (sat_cons (step2002 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step2243 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c2296 : List Lit := [(888, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c2213, c2289, c1968, c2293, c1400, c2220, c2294, c2014, c150, c151, c682, c2295, c1964, c647, c1399, c645, c2281, c56, c858, c1297, c94] c2296 (by decide) p (sat_cons (step2213 p h) (sat_cons (step2289 p h) (sat_cons (step1968 p h) (sat_cons (step2293 p h) (sat_cons (step1400 p h) (sat_cons (step2220 p h) (sat_cons (step2294 p h) (sat_cons (step2014 p h) (sat_cons (step150 p h) (sat_cons (step151 p h) (sat_cons (step682 p h) (sat_cons (step2295 p h) (sat_cons (step1964 p h) (sat_cons (step647 p h) (sat_cons (step1399 p h) (sat_cons (step645 p h) (sat_cons (step2281 p h) (sat_cons (step56 p h) (sat_cons (step858 p h) (sat_cons (step1297 p h) (sat_cons (step94 p h) (sat_nil p))))))))))))))))))))))
def c2297 : List Lit := [(886, false)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c2296, c700] c2297 (by decide) p (sat_cons (step2296 p h) (sat_cons (step700 p h) (sat_nil p)))
def c2298 : List Lit := [(883, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2296, c1040] c2298 (by decide) p (sat_cons (step2296 p h) (sat_cons (step1040 p h) (sat_nil p)))
def c2299 : List Lit := [(884, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c2296, c703] c2299 (by decide) p (sat_cons (step2296 p h) (sat_cons (step703 p h) (sat_nil p)))
def c2300 : List Lit := [(55, true)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c2297, c1038] c2300 (by decide) p (sat_cons (step2297 p h) (sat_cons (step1038 p h) (sat_nil p)))
def c2301 : List Lit := [(51, true)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c2298, c694] c2301 (by decide) p (sat_cons (step2298 p h) (sat_cons (step694 p h) (sat_nil p)))
def c2302 : List Lit := [(50, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c2298, c695] c2302 (by decide) p (sat_cons (step2298 p h) (sat_cons (step695 p h) (sat_nil p)))
def c2303 : List Lit := [(877, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c2298, c1223] c2303 (by decide) p (sat_cons (step2298 p h) (sat_cons (step1223 p h) (sat_nil p)))
def c2304 : List Lit := [(857, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c2298, c1892] c2304 (by decide) p (sat_cons (step2298 p h) (sat_cons (step1892 p h) (sat_nil p)))
def c2305 : List Lit := [(1024, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c2298, c2075] c2305 (by decide) p (sat_cons (step2298 p h) (sat_cons (step2075 p h) (sat_nil p)))
def c2306 : List Lit := [(903, true)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c2298, c2190] c2306 (by decide) p (sat_cons (step2298 p h) (sat_cons (step2190 p h) (sat_nil p)))
def c2307 : List Lit := [(869, true)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c2304, c1388] c2307 (by decide) p (sat_cons (step2304 p h) (sat_cons (step1388 p h) (sat_nil p)))
def c2308 : List Lit := [(21, false), (41, false), (926, true)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c2302, c2301, c2303, c2289, c2211, c2304, c1943, c1243, c1246, c2140, c57, c689, c1296, c1043, c131, c1722, c569, c664, c1032, c673, c586, c745, c641, c774] c2308 (by decide) p (sat_cons (step2302 p h) (sat_cons (step2301 p h) (sat_cons (step2303 p h) (sat_cons (step2289 p h) (sat_cons (step2211 p h) (sat_cons (step2304 p h) (sat_cons (step1943 p h) (sat_cons (step1243 p h) (sat_cons (step1246 p h) (sat_cons (step2140 p h) (sat_cons (step57 p h) (sat_cons (step689 p h) (sat_cons (step1296 p h) (sat_cons (step1043 p h) (sat_cons (step131 p h) (sat_cons (step1722 p h) (sat_cons (step569 p h) (sat_cons (step664 p h) (sat_cons (step1032 p h) (sat_cons (step673 p h) (sat_cons (step586 p h) (sat_cons (step745 p h) (sat_cons (step641 p h) (sat_cons (step774 p h) (sat_nil p)))))))))))))))))))))))))
def c2309 : List Lit := [(41, false), (926, true)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c2306, c2301, c2302, c2213, c2304, c2211, c2289, c2303, c783, c1246, c1243, c584, c1244, c672, c2308, c595, c1894, c637, c774, c2072, c569, c1032, c586, c642, c643, c779, c1439, c739, c2200, c1043, c689] c2309 (by decide) p (sat_cons (step2306 p h) (sat_cons (step2301 p h) (sat_cons (step2302 p h) (sat_cons (step2213 p h) (sat_cons (step2304 p h) (sat_cons (step2211 p h) (sat_cons (step2289 p h) (sat_cons (step2303 p h) (sat_cons (step783 p h) (sat_cons (step1246 p h) (sat_cons (step1243 p h) (sat_cons (step584 p h) (sat_cons (step1244 p h) (sat_cons (step672 p h) (sat_cons (step2308 p h) (sat_cons (step595 p h) (sat_cons (step1894 p h) (sat_cons (step637 p h) (sat_cons (step774 p h) (sat_cons (step2072 p h) (sat_cons (step569 p h) (sat_cons (step1032 p h) (sat_cons (step586 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step779 p h) (sat_cons (step1439 p h) (sat_cons (step739 p h) (sat_cons (step2200 p h) (sat_cons (step1043 p h) (sat_cons (step689 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2310 : List Lit := [(34, true), (21, false), (926, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c2211, c2289, c2298, c2299, c2302, c2303, c2301, c2309, c681, c689, c1043, c1287, c1770, c1296, c569, c53, c2198, c1032, c596, c1389, c1382, c1894, c637, c774, c740, c2242, c745, c1044, c677, c692, c690, c682, c2246] c2310 (by decide) p (sat_cons (step2211 p h) (sat_cons (step2289 p h) (sat_cons (step2298 p h) (sat_cons (step2299 p h) (sat_cons (step2302 p h) (sat_cons (step2303 p h) (sat_cons (step2301 p h) (sat_cons (step2309 p h) (sat_cons (step681 p h) (sat_cons (step689 p h) (sat_cons (step1043 p h) (sat_cons (step1287 p h) (sat_cons (step1770 p h) (sat_cons (step1296 p h) (sat_cons (step569 p h) (sat_cons (step53 p h) (sat_cons (step2198 p h) (sat_cons (step1032 p h) (sat_cons (step596 p h) (sat_cons (step1389 p h) (sat_cons (step1382 p h) (sat_cons (step1894 p h) (sat_cons (step637 p h) (sat_cons (step774 p h) (sat_cons (step740 p h) (sat_cons (step2242 p h) (sat_cons (step745 p h) (sat_cons (step1044 p h) (sat_cons (step677 p h) (sat_cons (step692 p h) (sat_cons (step690 p h) (sat_cons (step682 p h) (sat_cons (step2246 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2311 : List Lit := [(846, true), (805, false)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1943, c2301, c1382, c641, c637, c586, c1894, c1839, c596] c2311 (by decide) p (sat_cons (step1943 p h) (sat_cons (step2301 p h) (sat_cons (step1382 p h) (sat_cons (step641 p h) (sat_cons (step637 p h) (sat_cons (step586 p h) (sat_cons (step1894 p h) (sat_cons (step1839 p h) (sat_cons (step596 p h) (sat_nil p))))))))))
def c2312 : List Lit := [(905, true), (34, false), (21, false), (41, true)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c2299, c2301, c2302, c2304, c2289, c2303, c1103, c681, c689, c1043, c2242, c745, c661, c673, c672, c664, c740, c1689, c1044, c682, c692] c2312 (by decide) p (sat_cons (step2299 p h) (sat_cons (step2301 p h) (sat_cons (step2302 p h) (sat_cons (step2304 p h) (sat_cons (step2289 p h) (sat_cons (step2303 p h) (sat_cons (step1103 p h) (sat_cons (step681 p h) (sat_cons (step689 p h) (sat_cons (step1043 p h) (sat_cons (step2242 p h) (sat_cons (step745 p h) (sat_cons (step661 p h) (sat_cons (step673 p h) (sat_cons (step672 p h) (sat_cons (step664 p h) (sat_cons (step740 p h) (sat_cons (step1689 p h) (sat_cons (step1044 p h) (sat_cons (step682 p h) (sat_cons (step692 p h) (sat_nil p))))))))))))))))))))))
def c2313 : List Lit := [(862, true), (861, false), (876, false), (21, false), (907, true)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c2299, c2301, c2302, c2304, c656, c1179, c226, c1334, c252, c255, c644, c685, c2002, c693, c747, c1045] c2313 (by decide) p (sat_cons (step2299 p h) (sat_cons (step2301 p h) (sat_cons (step2302 p h) (sat_cons (step2304 p h) (sat_cons (step656 p h) (sat_cons (step1179 p h) (sat_cons (step226 p h) (sat_cons (step1334 p h) (sat_cons (step252 p h) (sat_cons (step255 p h) (sat_cons (step644 p h) (sat_cons (step685 p h) (sat_cons (step2002 p h) (sat_cons (step693 p h) (sat_cons (step747 p h) (sat_cons (step1045 p h) (sat_nil p)))))))))))))))))
def c2314 : List Lit := [(845, true)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c1943, c2214, c2213, c2301, c636, c632, c584, c1894, c1839, c596] c2314 (by decide) p (sat_cons (step1943 p h) (sat_cons (step2214 p h) (sat_cons (step2213 p h) (sat_cons (step2301 p h) (sat_cons (step636 p h) (sat_cons (step632 p h) (sat_cons (step584 p h) (sat_cons (step1894 p h) (sat_cons (step1839 p h) (sat_cons (step596 p h) (sat_nil p)))))))))))
def c2315 : List Lit := [(21, false), (926, true)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c2215, c2314, c2211, c2289, c2303, c2304, c767, c2309, c761, c2310, c2312, c774, c2311, c1032, c569, c132, c130, c129, c682, c654, c692, c2313, c1044, c664, c746, c673] c2315 (by decide) p (sat_cons (step2215 p h) (sat_cons (step2314 p h) (sat_cons (step2211 p h) (sat_cons (step2289 p h) (sat_cons (step2303 p h) (sat_cons (step2304 p h) (sat_cons (step767 p h) (sat_cons (step2309 p h) (sat_cons (step761 p h) (sat_cons (step2310 p h) (sat_cons (step2312 p h) (sat_cons (step774 p h) (sat_cons (step2311 p h) (sat_cons (step1032 p h) (sat_cons (step569 p h) (sat_cons (step132 p h) (sat_cons (step130 p h) (sat_cons (step129 p h) (sat_cons (step682 p h) (sat_cons (step654 p h) (sat_cons (step692 p h) (sat_cons (step2313 p h) (sat_cons (step1044 p h) (sat_cons (step664 p h) (sat_cons (step746 p h) (sat_cons (step673 p h) (sat_nil p)))))))))))))))))))))))))))
def c2316 : List Lit := [(862, true), (905, true), (29, true), (875, false)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c2299, c2301, c2302, c656, c1179, c226, c1334, c252, c255, c646, c685, c648, c690, c1389, c1044, c740] c2316 (by decide) p (sat_cons (step2299 p h) (sat_cons (step2301 p h) (sat_cons (step2302 p h) (sat_cons (step656 p h) (sat_cons (step1179 p h) (sat_cons (step226 p h) (sat_cons (step1334 p h) (sat_cons (step252 p h) (sat_cons (step255 p h) (sat_cons (step646 p h) (sat_cons (step685 p h) (sat_cons (step648 p h) (sat_cons (step690 p h) (sat_cons (step1389 p h) (sat_cons (step1044 p h) (sat_cons (step740 p h) (sat_nil p)))))))))))))))))
def c2317 : List Lit := [(904, true), (862, false), (34, true), (41, true)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c2307, c2304, c2303, c2301, c681, c689, c1043, c734, c739, c1044, c672, c692, c690, c682, c2246] c2317 (by decide) p (sat_cons (step2307 p h) (sat_cons (step2304 p h) (sat_cons (step2303 p h) (sat_cons (step2301 p h) (sat_cons (step681 p h) (sat_cons (step689 p h) (sat_cons (step1043 p h) (sat_cons (step734 p h) (sat_cons (step739 p h) (sat_cons (step1044 p h) (sat_cons (step672 p h) (sat_cons (step692 p h) (sat_cons (step690 p h) (sat_cons (step682 p h) (sat_cons (step2246 p h) (sat_nil p))))))))))))))))
def c2318 : List Lit := [(34, true), (926, true)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c2289, c2211, c2301, c2315, c595, c1894, c2309, c681, c1287, c1770, c569, c1032, c1382, c2311, c774, c2316, c2317, c779, c642, c638, c586, c1439, c1839, c597] c2318 (by decide) p (sat_cons (step2289 p h) (sat_cons (step2211 p h) (sat_cons (step2301 p h) (sat_cons (step2315 p h) (sat_cons (step595 p h) (sat_cons (step1894 p h) (sat_cons (step2309 p h) (sat_cons (step681 p h) (sat_cons (step1287 p h) (sat_cons (step1770 p h) (sat_cons (step569 p h) (sat_cons (step1032 p h) (sat_cons (step1382 p h) (sat_cons (step2311 p h) (sat_cons (step774 p h) (sat_cons (step2316 p h) (sat_cons (step2317 p h) (sat_cons (step779 p h) (sat_cons (step642 p h) (sat_cons (step638 p h) (sat_cons (step586 p h) (sat_cons (step1439 p h) (sat_cons (step1839 p h) (sat_cons (step597 p h) (sat_nil p)))))))))))))))))))))))))
def c2319 : List Lit := [(905, true), (878, false), (926, true)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c2307, c2304, c2289, c2309, c681, c690, c1044, c2318, c735, c740, c1045, c672, c693, c663, c682, c1689] c2319 (by decide) p (sat_cons (step2307 p h) (sat_cons (step2304 p h) (sat_cons (step2289 p h) (sat_cons (step2309 p h) (sat_cons (step681 p h) (sat_cons (step690 p h) (sat_cons (step1044 p h) (sat_cons (step2318 p h) (sat_cons (step735 p h) (sat_cons (step740 p h) (sat_cons (step1045 p h) (sat_cons (step672 p h) (sat_cons (step693 p h) (sat_cons (step663 p h) (sat_cons (step682 p h) (sat_cons (step1689 p h) (sat_nil p)))))))))))))))))
def c2320 : List Lit := [(905, false), (926, true)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c2213, c2301, c2318, c2315, c595, c1894, c774, c1935, c637, c597, c584, c1839] c2320 (by decide) p (sat_cons (step2213 p h) (sat_cons (step2301 p h) (sat_cons (step2318 p h) (sat_cons (step2315 p h) (sat_cons (step595 p h) (sat_cons (step1894 p h) (sat_cons (step774 p h) (sat_cons (step1935 p h) (sat_cons (step637 p h) (sat_cons (step597 p h) (sat_cons (step584 p h) (sat_cons (step1839 p h) (sat_nil p)))))))))))))
def c2321 : List Lit := [(862, true), (878, true)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c2299, c2301, c2302, c656, c1179, c226, c685, c1334, c255] c2321 (by decide) p (sat_cons (step2299 p h) (sat_cons (step2301 p h) (sat_cons (step2302 p h) (sat_cons (step656 p h) (sat_cons (step1179 p h) (sat_cons (step226 p h) (sat_cons (step685 p h) (sat_cons (step1334 p h) (sat_cons (step255 p h) (sat_nil p))))))))))
def c2322 : List Lit := [(926, true)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c2289, c2304, c2303, c2309, c681, c689, c1043, c2318, c1103, c2320, c745, c2319, c673, c2321, c664, c661, c1689, c672, c682, c740, c692, c1044] c2322 (by decide) p (sat_cons (step2289 p h) (sat_cons (step2304 p h) (sat_cons (step2303 p h) (sat_cons (step2309 p h) (sat_cons (step681 p h) (sat_cons (step689 p h) (sat_cons (step1043 p h) (sat_cons (step2318 p h) (sat_cons (step1103 p h) (sat_cons (step2320 p h) (sat_cons (step745 p h) (sat_cons (step2319 p h) (sat_cons (step673 p h) (sat_cons (step2321 p h) (sat_cons (step664 p h) (sat_cons (step661 p h) (sat_cons (step1689 p h) (sat_cons (step672 p h) (sat_cons (step682 p h) (sat_cons (step740 p h) (sat_cons (step692 p h) (sat_cons (step1044 p h) (sat_nil p)))))))))))))))))))))))
def c2323 : List Lit := [(1056, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c2322, c1400] c2323 (by decide) p (sat_cons (step2322 p h) (sat_cons (step1400 p h) (sat_nil p)))
def c2324 : List Lit := [(1039, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c2323, c1925] c2324 (by decide) p (sat_cons (step2323 p h) (sat_cons (step1925 p h) (sat_nil p)))
def c2325 : List Lit := [(979, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c2323, c1945, c957] c2325 (by decide) p (sat_cons (step2323 p h) (sat_cons (step1945 p h) (sat_cons (step957 p h) (sat_nil p))))
def c2326 : List Lit := [(34, true)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c2323, c2220] c2326 (by decide) p (sat_cons (step2323 p h) (sat_cons (step2220 p h) (sat_nil p)))
def c2327 : List Lit := [(997, false)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c2323, c2305, c2300, c1945, c1733] c2327 (by decide) p (sat_cons (step2323 p h) (sat_cons (step2305 p h) (sat_cons (step2300 p h) (sat_cons (step1945 p h) (sat_cons (step1733 p h) (sat_nil p))))))
def c2328 : List Lit := [(104, true)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c2323, c2305, c2014] c2328 (by decide) p (sat_cons (step2323 p h) (sat_cons (step2305 p h) (sat_cons (step2014 p h) (sat_nil p))))
def c2329 : List Lit := [(995, false)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c2324, c2305, c1907] c2329 (by decide) p (sat_cons (step2324 p h) (sat_cons (step2305 p h) (sat_cons (step1907 p h) (sat_nil p))))
def c2330 : List Lit := [(66, true)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c2325, c1791] c2330 (by decide) p (sat_cons (step2325 p h) (sat_cons (step1791 p h) (sat_nil p)))
def c2331 : List Lit := [(90, false)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c2325, c2300, c1712] c2331 (by decide) p (sat_cons (step2325 p h) (sat_cons (step2300 p h) (sat_cons (step1712 p h) (sat_nil p))))
def c2332 : List Lit := [(98, true)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c2327, c866] c2332 (by decide) p (sat_cons (step2327 p h) (sat_cons (step866 p h) (sat_nil p)))
def c2333 : List Lit := [(95, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c2327, c867] c2333 (by decide) p (sat_cons (step2327 p h) (sat_cons (step867 p h) (sat_nil p)))
def c2334 : List Lit := [(4, false)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c2328, c2326, c2289, c133] c2334 (by decide) p (sat_cons (step2328 p h) (sat_cons (step2326 p h) (sat_cons (step2289 p h) (sat_cons (step133 p h) (sat_nil p)))))
def c2335 : List Lit := [(36, false)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c2328, c2289, c2326, c148] c2335 (by decide) p (sat_cons (step2328 p h) (sat_cons (step2289 p h) (sat_cons (step2326 p h) (sat_cons (step148 p h) (sat_nil p)))))
def c2336 : List Lit := [(32, false)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c2328, c2326, c2289, c145] c2336 (by decide) p (sat_cons (step2328 p h) (sat_cons (step2326 p h) (sat_cons (step2289 p h) (sat_cons (step145 p h) (sat_nil p)))))
def c2337 : List Lit := [(993, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c2329, c862] c2337 (by decide) p (sat_cons (step2329 p h) (sat_cons (step862 p h) (sat_nil p)))
def c2338 : List Lit := [(992, true)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c2331, c859] c2338 (by decide) p (sat_cons (step2331 p h) (sat_cons (step859 p h) (sat_nil p)))
def c2339 : List Lit := [(94, true)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c2331, c2337, c860] c2339 (by decide) p (sat_cons (step2331 p h) (sat_cons (step2337 p h) (sat_cons (step860 p h) (sat_nil p))))
def c2340 : List Lit := [(100, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c2332, c2339, c2330, c344] c2340 (by decide) p (sat_cons (step2332 p h) (sat_cons (step2339 p h) (sat_cons (step2330 p h) (sat_cons (step344 p h) (sat_nil p)))))
def c2341 : List Lit := [(26, true)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c2333, c2339, c2340, c1165] c2341 (by decide) p (sat_cons (step2333 p h) (sat_cons (step2339 p h) (sat_cons (step2340 p h) (sat_cons (step1165 p h) (sat_nil p)))))
def c2342 : List Lit := [(802, true)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c2334, c2211, c569] c2342 (by decide) p (sat_cons (step2334 p h) (sat_cons (step2211 p h) (sat_cons (step569 p h) (sat_nil p))))
def c2343 : List Lit := [(861, true)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c2336, c2335, c654] c2343 (by decide) p (sat_cons (step2336 p h) (sat_cons (step2335 p h) (sat_cons (step654 p h) (sat_nil p))))
def c2344 : List Lit := [(1057, true)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c2338, c2323, c2305, c2281] c2344 (by decide) p (sat_cons (step2338 p h) (sat_cons (step2323 p h) (sat_cons (step2305 p h) (sat_cons (step2281 p h) (sat_nil p)))))
def c2345 : List Lit := [(88, true)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c2338, c2329, c864] c2345 (by decide) p (sat_cons (step2338 p h) (sat_cons (step2329 p h) (sat_cons (step864 p h) (sat_nil p))))
def c2346 : List Lit := [(805, true)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c2342, c1032] c2346 (by decide) p (sat_cons (step2342 p h) (sat_cons (step1032 p h) (sat_nil p)))
def c2347 : List Lit := [(865, true)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c2343, c663] c2347 (by decide) p (sat_cons (step2343 p h) (sat_cons (step663 p h) (sat_nil p)))
def c2348 : List Lit := [(925, false)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c2344, c1399] c2348 (by decide) p (sat_cons (step2344 p h) (sat_cons (step1399 p h) (sat_nil p)))
end B112E159
