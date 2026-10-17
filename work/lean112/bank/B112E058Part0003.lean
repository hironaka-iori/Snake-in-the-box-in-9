import B112E058Part0002
namespace B112E058
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c875 : List Lit := [(1528, true), (1627, true), (105, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c696, c708, c712, c281, c290, c292, c634, c718, c588, c631, c624, c748, c865, c501, c503, c498, c499, c226, c108, c228, c231, c109, c113, c151, c433, c422, c436, c428, c449] c875 (by decide) p (sat_cons (step696 p h) (sat_cons (step708 p h) (sat_cons (step712 p h) (sat_cons (step281 p h) (sat_cons (step290 p h) (sat_cons (step292 p h) (sat_cons (step634 p h) (sat_cons (step718 p h) (sat_cons (step588 p h) (sat_cons (step631 p h) (sat_cons (step624 p h) (sat_cons (step748 p h) (sat_cons (step865 p h) (sat_cons (step501 p h) (sat_cons (step503 p h) (sat_cons (step498 p h) (sat_cons (step499 p h) (sat_cons (step226 p h) (sat_cons (step108 p h) (sat_cons (step228 p h) (sat_cons (step231 p h) (sat_cons (step109 p h) (sat_cons (step113 p h) (sat_cons (step151 p h) (sat_cons (step433 p h) (sat_cons (step422 p h) (sat_cons (step436 p h) (sat_cons (step428 p h) (sat_cons (step449 p h) (sat_nil p))))))))))))))))))))))))))))))
def c876 : List Lit := [(62, false), (1537, true), (1627, true), (105, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c696, c708, c712, c290, c292, c634, c718, c588, c631, c624, c748, c226, c228, c231, c117, c157, c156, c507, c511, c516] c876 (by decide) p (sat_cons (step696 p h) (sat_cons (step708 p h) (sat_cons (step712 p h) (sat_cons (step290 p h) (sat_cons (step292 p h) (sat_cons (step634 p h) (sat_cons (step718 p h) (sat_cons (step588 p h) (sat_cons (step631 p h) (sat_cons (step624 p h) (sat_cons (step748 p h) (sat_cons (step226 p h) (sat_cons (step228 p h) (sat_cons (step231 p h) (sat_cons (step117 p h) (sat_cons (step157 p h) (sat_cons (step156 p h) (sat_cons (step507 p h) (sat_cons (step511 p h) (sat_cons (step516 p h) (sat_nil p)))))))))))))))))))))
def c877 : List Lit := [(1414, true), (63, false), (76, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c260, c259, c332, c335, c329, c319, c321, c323, c316, c10, c6, c1] c877 (by decide) p (sat_cons (step260 p h) (sat_cons (step259 p h) (sat_cons (step332 p h) (sat_cons (step335 p h) (sat_cons (step329 p h) (sat_cons (step319 p h) (sat_cons (step321 p h) (sat_cons (step323 p h) (sat_cons (step316 p h) (sat_cons (step10 p h) (sat_cons (step6 p h) (sat_cons (step1 p h) (sat_nil p)))))))))))))
def c878 : List Lit := [(1533, false), (1550, false), (1537, true), (1572, true), (1528, false), (69, true), (1403, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c258, c284, c742, c507, c516, c319, c317, c3, c518, c515, c508, c526, c572, c560, c548, c543, c165, c511, c172, c174, c679] c878 (by decide) p (sat_cons (step258 p h) (sat_cons (step284 p h) (sat_cons (step742 p h) (sat_cons (step507 p h) (sat_cons (step516 p h) (sat_cons (step319 p h) (sat_cons (step317 p h) (sat_cons (step3 p h) (sat_cons (step518 p h) (sat_cons (step515 p h) (sat_cons (step508 p h) (sat_cons (step526 p h) (sat_cons (step572 p h) (sat_cons (step560 p h) (sat_cons (step548 p h) (sat_cons (step543 p h) (sat_cons (step165 p h) (sat_cons (step511 p h) (sat_cons (step172 p h) (sat_cons (step174 p h) (sat_cons (step679 p h) (sat_nil p))))))))))))))))))))))
def c879 : List Lit := [(1550, false), (1537, true), (1572, true), (1627, true), (1528, false), (69, true), (1403, true), (105, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c258, c284, c319, c317, c3, c742, c878, c509, c510, c172, c165, c175, c543, c508, c548, c872, c560, c572] c879 (by decide) p (sat_cons (step258 p h) (sat_cons (step284 p h) (sat_cons (step319 p h) (sat_cons (step317 p h) (sat_cons (step3 p h) (sat_cons (step742 p h) (sat_cons (step878 p h) (sat_cons (step509 p h) (sat_cons (step510 p h) (sat_cons (step172 p h) (sat_cons (step165 p h) (sat_cons (step175 p h) (sat_cons (step543 p h) (sat_cons (step508 p h) (sat_cons (step548 p h) (sat_cons (step872 p h) (sat_cons (step560 p h) (sat_cons (step572 p h) (sat_nil p)))))))))))))))))))
def c880 : List Lit := [(72, false), (70, false), (67, false), (69, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c284, c172, c175] c880 (by decide) p (sat_cons (step284 p h) (sat_cons (step172 p h) (sat_cons (step175 p h) (sat_nil p))))
def c881 : List Lit := [(1490, true), (1482, false), (51, true), (69, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c275, c431, c438, c444, c447, c441, c425, c427, c432, c422, c85, c89] c881 (by decide) p (sat_cons (step275 p h) (sat_cons (step431 p h) (sat_cons (step438 p h) (sat_cons (step444 p h) (sat_cons (step447 p h) (sat_cons (step441 p h) (sat_cons (step425 p h) (sat_cons (step427 p h) (sat_cons (step432 p h) (sat_cons (step422 p h) (sat_cons (step85 p h) (sat_cons (step89 p h) (sat_nil p)))))))))))))
def c882 : List Lit := [(37, true), (1469, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c683, c272, c414, c397, c413, c411, c401, c402, c409, c403, c404, c77, c70, c74] c882 (by decide) p (sat_cons (step683 p h) (sat_cons (step272 p h) (sat_cons (step414 p h) (sat_cons (step397 p h) (sat_cons (step413 p h) (sat_cons (step411 p h) (sat_cons (step401 p h) (sat_cons (step402 p h) (sat_cons (step409 p h) (sat_cons (step403 p h) (sat_cons (step404 p h) (sat_cons (step77 p h) (sat_cons (step70 p h) (sat_cons (step74 p h) (sat_nil p)))))))))))))))
def c883 : List Lit := [(1469, true), (1437, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true :=
  Snake9.LocalRup.prove_clause [c683, c269, c262, c414, c395, c397, c392, c393, c51, c852, c62, c882, c31, c353, c783, c845, c16, c17] c883 (by decide) p (sat_cons (step683 p h) (sat_cons (step269 p h) (sat_cons (step262 p h) (sat_cons (step414 p h) (sat_cons (step395 p h) (sat_cons (step397 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step51 p h) (sat_cons (step852 p h) (sat_cons (step62 p h) (sat_cons (step882 p h) (sat_cons (step31 p h) (sat_cons (step353 p h) (sat_cons (step783 p h) (sat_cons (step845 p h) (sat_cons (step16 p h) (sat_cons (step17 p h) (sat_nil p)))))))))))))))))))
def c884 : List Lit := [(1470, true), (1455, false), (37, true)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true :=
  Snake9.LocalRup.prove_clause [c683, c272, c395, c401, c417, c415, c398, c411, c409, c402, c403, c404, c77, c70, c74] c884 (by decide) p (sat_cons (step683 p h) (sat_cons (step272 p h) (sat_cons (step395 p h) (sat_cons (step401 p h) (sat_cons (step417 p h) (sat_cons (step415 p h) (sat_cons (step398 p h) (sat_cons (step411 p h) (sat_cons (step409 p h) (sat_cons (step402 p h) (sat_cons (step403 p h) (sat_cons (step404 p h) (sat_cons (step77 p h) (sat_cons (step70 p h) (sat_cons (step74 p h) (sat_nil p))))))))))))))))
def c885 : List Lit := [(1531, false), (1542, true), (58, true), (65, false), (67, false), (70, true)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true :=
  Snake9.LocalRup.prove_clause [c503, c527, c510, c515, c516, c530, c511, c504, c123, c498] c885 (by decide) p (sat_cons (step503 p h) (sat_cons (step527 p h) (sat_cons (step510 p h) (sat_cons (step515 p h) (sat_cons (step516 p h) (sat_cons (step530 p h) (sat_cons (step511 p h) (sat_cons (step504 p h) (sat_cons (step123 p h) (sat_cons (step498 p h) (sat_nil p)))))))))))
def c886 : List Lit := [(1542, true), (58, true), (70, true), (65, false), (67, false)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true :=
  Snake9.LocalRup.prove_clause [c885, c507, c121, c126, c498, c511, c504, c513, c530] c886 (by decide) p (sat_cons (step885 p h) (sat_cons (step507 p h) (sat_cons (step121 p h) (sat_cons (step126 p h) (sat_cons (step498 p h) (sat_cons (step511 p h) (sat_cons (step504 p h) (sat_cons (step513 p h) (sat_cons (step530 p h) (sat_nil p))))))))))
def c887 : List Lit := [(1443, true), (1428, false), (1627, true)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true :=
  Snake9.LocalRup.prove_clause [c720, c696, c708, c712, c634, c718, c588, c631, c624, c744, c748, c747, c595, c585, c377, c381, c824, c332, c787, c327, c324] c887 (by decide) p (sat_cons (step720 p h) (sat_cons (step696 p h) (sat_cons (step708 p h) (sat_cons (step712 p h) (sat_cons (step634 p h) (sat_cons (step718 p h) (sat_cons (step588 p h) (sat_cons (step631 p h) (sat_cons (step624 p h) (sat_cons (step744 p h) (sat_cons (step748 p h) (sat_cons (step747 p h) (sat_cons (step595 p h) (sat_cons (step585 p h) (sat_cons (step377 p h) (sat_cons (step381 p h) (sat_cons (step824 p h) (sat_cons (step332 p h) (sat_cons (step787 p h) (sat_cons (step327 p h) (sat_cons (step324 p h) (sat_nil p))))))))))))))))))))))
def c888 : List Lit := [(1414, false), (1436, false), (1489, false), (1516, true)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true :=
  Snake9.LocalRup.prove_clause [c684, c454, c490, c383, c382, c883, c486, c458] c888 (by decide) p (sat_cons (step684 p h) (sat_cons (step454 p h) (sat_cons (step490 p h) (sat_cons (step383 p h) (sat_cons (step382 p h) (sat_cons (step883 p h) (sat_cons (step486 p h) (sat_cons (step458 p h) (sat_nil p)))))))))
def c889 : List Lit := [(1561, true), (65, false), (67, false), (1618, true), (39, false), (1498, true), (1438, true), (1482, false), (1414, true), (18, true)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true :=
  Snake9.TreeRup.prove_clause [c261, c258, c684, c683, c270, c708, c711, c274, c288, c291, c263, c272, c623, c741, c624, c735, c458, c413, c407, c882, c64, c66, c405, c414, c395, c392, c65, c31, c32, c353, c393, c455, c335, c319, c317, c3, c332, c327, c324, c13, c795, c329, c323, c325, c721, c166, c163, c194, c601, c431, c734, c606, c438, c536, c598, c447, c541, c425, c557, c423, c547, c139, c546, c83, c219, c131, c11, c229, c19, c67, c340, c73, c346, c71, c371, c349, c358] c889 (by decide) p (sat_cons (step261 p h) (sat_cons (step258 p h) (sat_cons (step684 p h) (sat_cons (step683 p h) (sat_cons (step270 p h) (sat_cons (step708 p h) (sat_cons (step711 p h) (sat_cons (step274 p h) (sat_cons (step288 p h) (sat_cons (step291 p h) (sat_cons (step263 p h) (sat_cons (step272 p h) (sat_cons (step623 p h) (sat_cons (step741 p h) (sat_cons (step624 p h) (sat_cons (step735 p h) (sat_cons (step458 p h) (sat_cons (step413 p h) (sat_cons (step407 p h) (sat_cons (step882 p h) (sat_cons (step64 p h) (sat_cons (step66 p h) (sat_cons (step405 p h) (sat_cons (step414 p h) (sat_cons (step395 p h) (sat_cons (step392 p h) (sat_cons (step65 p h) (sat_cons (step31 p h) (sat_cons (step32 p h) (sat_cons (step353 p h) (sat_cons (step393 p h) (sat_cons (step455 p h) (sat_cons (step335 p h) (sat_cons (step319 p h) (sat_cons (step317 p h) (sat_cons (step3 p h) (sat_cons (step332 p h) (sat_cons (step327 p h) (sat_cons (step324 p h) (sat_cons (step13 p h) (sat_cons (step795 p h) (sat_cons (step329 p h) (sat_cons (step323 p h) (sat_cons (step325 p h) (sat_cons (step721 p h) (sat_cons (step166 p h) (sat_cons (step163 p h) (sat_cons (step194 p h) (sat_cons (step601 p h) (sat_cons (step431 p h) (sat_cons (step734 p h) (sat_cons (step606 p h) (sat_cons (step438 p h) (sat_cons (step536 p h) (sat_cons (step598 p h) (sat_cons (step447 p h) (sat_cons (step541 p h) (sat_cons (step425 p h) (sat_cons (step557 p h) (sat_cons (step423 p h) (sat_cons (step547 p h) (sat_cons (step139 p h) (sat_cons (step546 p h) (sat_cons (step83 p h) (sat_cons (step219 p h) (sat_cons (step131 p h) (sat_cons (step11 p h) (sat_cons (step229 p h) (sat_cons (step19 p h) (sat_cons (step67 p h) (sat_cons (step340 p h) (sat_cons (step73 p h) (sat_cons (step346 p h) (sat_cons (step71 p h) (sat_cons (step371 p h) (sat_cons (step349 p h) (sat_cons (step358 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c890 : List Lit := [(1537, true), (70, true), (111, false), (104, false), (69, false), (101, false), (1498, true), (1482, false), (1403, true)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true :=
  Snake9.LocalRup.prove_clause [c258, c292, c683, c684, c668, c713, c735, c454, c458, c883, c378, c485, c663, c655, c742, c507, c834, c515, c414, c395, c392, c393, c397, c51, c234, c232, c226, c498, c501, c526, c572, c455, c319, c317, c3, c795, c722, c516, c535, c511, c541, c154, c558, c422, c550, c425, c767, c447, c740, c438, c163, c431] c890 (by decide) p (sat_cons (step258 p h) (sat_cons (step292 p h) (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step668 p h) (sat_cons (step713 p h) (sat_cons (step735 p h) (sat_cons (step454 p h) (sat_cons (step458 p h) (sat_cons (step883 p h) (sat_cons (step378 p h) (sat_cons (step485 p h) (sat_cons (step663 p h) (sat_cons (step655 p h) (sat_cons (step742 p h) (sat_cons (step507 p h) (sat_cons (step834 p h) (sat_cons (step515 p h) (sat_cons (step414 p h) (sat_cons (step395 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step397 p h) (sat_cons (step51 p h) (sat_cons (step234 p h) (sat_cons (step232 p h) (sat_cons (step226 p h) (sat_cons (step498 p h) (sat_cons (step501 p h) (sat_cons (step526 p h) (sat_cons (step572 p h) (sat_cons (step455 p h) (sat_cons (step319 p h) (sat_cons (step317 p h) (sat_cons (step3 p h) (sat_cons (step795 p h) (sat_cons (step722 p h) (sat_cons (step516 p h) (sat_cons (step535 p h) (sat_cons (step511 p h) (sat_cons (step541 p h) (sat_cons (step154 p h) (sat_cons (step558 p h) (sat_cons (step422 p h) (sat_cons (step550 p h) (sat_cons (step425 p h) (sat_cons (step767 p h) (sat_cons (step447 p h) (sat_cons (step740 p h) (sat_cons (step438 p h) (sat_cons (step163 p h) (sat_cons (step431 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c891 : List Lit := [(70, true), (1618, true), (104, false), (69, false), (101, false), (1498, true), (1402, true), (1438, true), (1482, false), (1414, true), (18, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.TreeRup.prove_clause [c258, c684, c668, c713, c292, c683, c711, c285, c623, c741, c735, c458, c414, c395, c392, c393, c397, c51, c234, c232, c226, c498, c501, c716, c400, c454, c883, c378, c485, c663, c655, c455, c335, c319, c317, c3, c795, c332, c329, c323, c742, c890, c527, c577, c721, c827, c163, c194, c431, c734, c537, c438, c536, c203, c447, c541, c889, c425, c556, c508, c422, c580, c154, c528, c511, c519] c891 (by decide) p (sat_cons (step258 p h) (sat_cons (step684 p h) (sat_cons (step668 p h) (sat_cons (step713 p h) (sat_cons (step292 p h) (sat_cons (step683 p h) (sat_cons (step711 p h) (sat_cons (step285 p h) (sat_cons (step623 p h) (sat_cons (step741 p h) (sat_cons (step735 p h) (sat_cons (step458 p h) (sat_cons (step414 p h) (sat_cons (step395 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step397 p h) (sat_cons (step51 p h) (sat_cons (step234 p h) (sat_cons (step232 p h) (sat_cons (step226 p h) (sat_cons (step498 p h) (sat_cons (step501 p h) (sat_cons (step716 p h) (sat_cons (step400 p h) (sat_cons (step454 p h) (sat_cons (step883 p h) (sat_cons (step378 p h) (sat_cons (step485 p h) (sat_cons (step663 p h) (sat_cons (step655 p h) (sat_cons (step455 p h) (sat_cons (step335 p h) (sat_cons (step319 p h) (sat_cons (step317 p h) (sat_cons (step3 p h) (sat_cons (step795 p h) (sat_cons (step332 p h) (sat_cons (step329 p h) (sat_cons (step323 p h) (sat_cons (step742 p h) (sat_cons (step890 p h) (sat_cons (step527 p h) (sat_cons (step577 p h) (sat_cons (step721 p h) (sat_cons (step827 p h) (sat_cons (step163 p h) (sat_cons (step194 p h) (sat_cons (step431 p h) (sat_cons (step734 p h) (sat_cons (step537 p h) (sat_cons (step438 p h) (sat_cons (step536 p h) (sat_cons (step203 p h) (sat_cons (step447 p h) (sat_cons (step541 p h) (sat_cons (step889 p h) (sat_cons (step425 p h) (sat_cons (step556 p h) (sat_cons (step508 p h) (sat_cons (step422 p h) (sat_cons (step580 p h) (sat_cons (step154 p h) (sat_cons (step528 p h) (sat_cons (step511 p h) (sat_cons (step519 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c892 : List Lit := [(70, false), (104, false), (69, false), (1490, true), (1482, false), (5, false)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true :=
  Snake9.LocalRup.prove_clause [c258, c3, c153, c162, c422, c431, c425, c438, c447] c892 (by decide) p (sat_cons (step258 p h) (sat_cons (step3 p h) (sat_cons (step153 p h) (sat_cons (step162 p h) (sat_cons (step422 p h) (sat_cons (step431 p h) (sat_cons (step425 p h) (sat_cons (step438 p h) (sat_cons (step447 p h) (sat_nil p))))))))))
def c893 : List Lit := [(104, false), (69, false), (101, false), (1498, true), (1402, true), (1438, true), (1482, false), (1414, true), (18, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true :=
  Snake9.LocalRup.prove_clause [c683, c684, c668, c292, c696, c735, c454, c458, c883, c378, c485, c663, c414, c395, c392, c393, c397, c51, c455, c335, c742, c507, c319, c795, c317, c234, c232, c834, c226, c515, c498, c501, c526, c892, c891, c631, c653, c571, c791, c559, c542] c893 (by decide) p (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step668 p h) (sat_cons (step292 p h) (sat_cons (step696 p h) (sat_cons (step735 p h) (sat_cons (step454 p h) (sat_cons (step458 p h) (sat_cons (step883 p h) (sat_cons (step378 p h) (sat_cons (step485 p h) (sat_cons (step663 p h) (sat_cons (step414 p h) (sat_cons (step395 p h) (sat_cons (step392 p h) (sat_cons (step393 p h) (sat_cons (step397 p h) (sat_cons (step51 p h) (sat_cons (step455 p h) (sat_cons (step335 p h) (sat_cons (step742 p h) (sat_cons (step507 p h) (sat_cons (step319 p h) (sat_cons (step795 p h) (sat_cons (step317 p h) (sat_cons (step234 p h) (sat_cons (step232 p h) (sat_cons (step834 p h) (sat_cons (step226 p h) (sat_cons (step515 p h) (sat_cons (step498 p h) (sat_cons (step501 p h) (sat_cons (step526 p h) (sat_cons (step892 p h) (sat_cons (step891 p h) (sat_cons (step631 p h) (sat_cons (step653 p h) (sat_cons (step571 p h) (sat_cons (step791 p h) (sat_cons (step559 p h) (sat_cons (step542 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c894 : List Lit := [(5, false), (71, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true :=
  Snake9.LocalRup.prove_clause [c258, c3] c894 (by decide) p (sat_cons (step258 p h) (sat_cons (step3 p h) (sat_nil p)))
def c895 : List Lit := [(6, false), (7, true)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true :=
  Snake9.LocalRup.prove_clause [c259, c5] c895 (by decide) p (sat_cons (step259 p h) (sat_cons (step5 p h) (sat_nil p)))
def c896 : List Lit := [(6, false), (3, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true :=
  Snake9.LocalRup.prove_clause [c259, c6] c896 (by decide) p (sat_cons (step259 p h) (sat_cons (step6 p h) (sat_nil p)))
def c897 : List Lit := [(8, true), (76, true), (10, false)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true :=
  Snake9.LocalRup.prove_clause [c260, c10] c897 (by decide) p (sat_cons (step260 p h) (sat_cons (step10 p h) (sat_nil p)))
def c898 : List Lit := [(15, false), (16, true)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true :=
  Snake9.LocalRup.prove_clause [c261, c13] c898 (by decide) p (sat_cons (step261 p h) (sat_cons (step13 p h) (sat_nil p)))
def c899 : List Lit := [(19, true), (18, false), (32, true)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true :=
  Snake9.LocalRup.prove_clause [c262, c16] c899 (by decide) p (sat_cons (step262 p h) (sat_cons (step16 p h) (sat_nil p)))
def c900 : List Lit := [(22, false), (17, true)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true :=
  Snake9.LocalRup.prove_clause [c263, c19] c900 (by decide) p (sat_cons (step263 p h) (sat_cons (step19 p h) (sat_nil p)))
def c901 : List Lit := [(23, false), (41, true)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true :=
  Snake9.LocalRup.prove_clause [c264, c20] c901 (by decide) p (sat_cons (step264 p h) (sat_cons (step20 p h) (sat_nil p)))
def c902 : List Lit := [(24, false), (25, true)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true :=
  Snake9.LocalRup.prove_clause [c265, c22] c902 (by decide) p (sat_cons (step265 p h) (sat_cons (step22 p h) (sat_nil p)))
def c903 : List Lit := [(29, true), (100, true), (27, false), (32, true), (28, true)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true :=
  Snake9.LocalRup.prove_clause [c266, c26] c903 (by decide) p (sat_cons (step266 p h) (sat_cons (step26 p h) (sat_nil p)))
def c904 : List Lit := [(29, true), (28, true), (27, false), (1, true), (32, true)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true :=
  Snake9.LocalRup.prove_clause [c266, c27] c904 (by decide) p (sat_cons (step266 p h) (sat_cons (step27 p h) (sat_nil p)))
def c905 : List Lit := [(40, true), (105, true), (32, true), (33, false)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true :=
  Snake9.LocalRup.prove_clause [c267, c55] c905 (by decide) p (sat_cons (step267 p h) (sat_cons (step55 p h) (sat_nil p)))
def c906 : List Lit := [(28, true), (41, true), (34, false), (32, true)]
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true :=
  Snake9.LocalRup.prove_clause [c268, c57] c906 (by decide) p (sat_cons (step268 p h) (sat_cons (step57 p h) (sat_nil p)))
def c907 : List Lit := [(36, true), (28, true), (32, true), (34, false)]
theorem step907 (p : Nat → Bool) (h : Constraints p) : clause p c907 = true :=
  Snake9.LocalRup.prove_clause [c268, c58] c907 (by decide) p (sat_cons (step268 p h) (sat_cons (step58 p h) (sat_nil p)))
def c908 : List Lit := [(36, true), (35, false), (32, true)]
theorem step908 (p : Nat → Bool) (h : Constraints p) : clause p c908 = true :=
  Snake9.LocalRup.prove_clause [c269, c60] c908 (by decide) p (sat_cons (step269 p h) (sat_cons (step60 p h) (sat_nil p)))
def c909 : List Lit := [(36, true), (29, true), (35, false)]
theorem step909 (p : Nat → Bool) (h : Constraints p) : clause p c909 = true :=
  Snake9.LocalRup.prove_clause [c269, c61] c909 (by decide) p (sat_cons (step269 p h) (sat_cons (step61 p h) (sat_nil p)))
def c910 : List Lit := [(29, true), (35, false), (32, true)]
theorem step910 (p : Nat → Bool) (h : Constraints p) : clause p c910 = true :=
  Snake9.LocalRup.prove_clause [c269, c62] c910 (by decide) p (sat_cons (step269 p h) (sat_cons (step62 p h) (sat_nil p)))
def c911 : List Lit := [(37, false), (38, true)]
theorem step911 (p : Nat → Bool) (h : Constraints p) : clause p c911 = true :=
  Snake9.LocalRup.prove_clause [c270, c64] c911 (by decide) p (sat_cons (step270 p h) (sat_cons (step64 p h) (sat_nil p)))
def c912 : List Lit := [(37, false), (29, true)]
theorem step912 (p : Nat → Bool) (h : Constraints p) : clause p c912 = true :=
  Snake9.LocalRup.prove_clause [c270, c65] c912 (by decide) p (sat_cons (step270 p h) (sat_cons (step65 p h) (sat_nil p)))
def c913 : List Lit := [(44, true), (38, true), (39, false)]
theorem step913 (p : Nat → Bool) (h : Constraints p) : clause p c913 = true :=
  Snake9.LocalRup.prove_clause [c271, c68] c913 (by decide) p (sat_cons (step271 p h) (sat_cons (step68 p h) (sat_nil p)))
def c914 : List Lit := [(44, true), (31, true), (39, false)]
theorem step914 (p : Nat → Bool) (h : Constraints p) : clause p c914 = true :=
  Snake9.LocalRup.prove_clause [c271, c69] c914 (by decide) p (sat_cons (step271 p h) (sat_cons (step69 p h) (sat_nil p)))
def c915 : List Lit := [(44, true), (41, true), (42, false)]
theorem step915 (p : Nat → Bool) (h : Constraints p) : clause p c915 = true :=
  Snake9.LocalRup.prove_clause [c272, c73] c915 (by decide) p (sat_cons (step272 p h) (sat_cons (step73 p h) (sat_nil p)))
def c916 : List Lit := [(44, true), (40, true), (42, false)]
theorem step916 (p : Nat → Bool) (h : Constraints p) : clause p c916 = true :=
  Snake9.LocalRup.prove_clause [c272, c74] c916 (by decide) p (sat_cons (step272 p h) (sat_cons (step74 p h) (sat_nil p)))
def c917 : List Lit := [(54, true), (50, true), (63, true), (46, false)]
theorem step917 (p : Nat → Bool) (h : Constraints p) : clause p c917 = true :=
  Snake9.LocalRup.prove_clause [c273, c79] c917 (by decide) p (sat_cons (step273 p h) (sat_cons (step79 p h) (sat_nil p)))
def c918 : List Lit := [(45, true), (54, true), (63, true), (46, false)]
theorem step918 (p : Nat → Bool) (h : Constraints p) : clause p c918 = true :=
  Snake9.LocalRup.prove_clause [c273, c80] c918 (by decide) p (sat_cons (step273 p h) (sat_cons (step80 p h) (sat_nil p)))
def c919 : List Lit := [(53, true), (68, true), (48, false)]
theorem step919 (p : Nat → Bool) (h : Constraints p) : clause p c919 = true :=
  Snake9.LocalRup.prove_clause [c274, c82] c919 (by decide) p (sat_cons (step274 p h) (sat_cons (step82 p h) (sat_nil p)))
def c920 : List Lit := [(47, true), (68, true), (48, false)]
theorem step920 (p : Nat → Bool) (h : Constraints p) : clause p c920 = true :=
  Snake9.LocalRup.prove_clause [c274, c83] c920 (by decide) p (sat_cons (step274 p h) (sat_cons (step83 p h) (sat_nil p)))
def c921 : List Lit := [(53, true), (47, true), (48, false)]
theorem step921 (p : Nat → Bool) (h : Constraints p) : clause p c921 = true :=
  Snake9.LocalRup.prove_clause [c274, c84] c921 (by decide) p (sat_cons (step274 p h) (sat_cons (step84 p h) (sat_nil p)))
def c922 : List Lit := [(50, true), (49, false), (69, true)]
theorem step922 (p : Nat → Bool) (h : Constraints p) : clause p c922 = true :=
  Snake9.LocalRup.prove_clause [c275, c85] c922 (by decide) p (sat_cons (step275 p h) (sat_cons (step85 p h) (sat_nil p)))
def c923 : List Lit := [(45, true), (49, false), (69, true)]
theorem step923 (p : Nat → Bool) (h : Constraints p) : clause p c923 = true :=
  Snake9.LocalRup.prove_clause [c275, c86] c923 (by decide) p (sat_cons (step275 p h) (sat_cons (step86 p h) (sat_nil p)))
def c924 : List Lit := [(45, true), (49, false), (50, true)]
theorem step924 (p : Nat → Bool) (h : Constraints p) : clause p c924 = true :=
  Snake9.LocalRup.prove_clause [c275, c87] c924 (by decide) p (sat_cons (step275 p h) (sat_cons (step87 p h) (sat_nil p)))
def c925 : List Lit := [(53, true), (71, true), (51, false)]
theorem step925 (p : Nat → Bool) (h : Constraints p) : clause p c925 = true :=
  Snake9.LocalRup.prove_clause [c276, c93] c925 (by decide) p (sat_cons (step276 p h) (sat_cons (step93 p h) (sat_nil p)))
def c926 : List Lit := [(50, true), (71, true), (51, false)]
theorem step926 (p : Nat → Bool) (h : Constraints p) : clause p c926 = true :=
  Snake9.LocalRup.prove_clause [c276, c94] c926 (by decide) p (sat_cons (step276 p h) (sat_cons (step94 p h) (sat_nil p)))
def c927 : List Lit := [(50, true), (53, true), (51, false)]
theorem step927 (p : Nat → Bool) (h : Constraints p) : clause p c927 = true :=
  Snake9.LocalRup.prove_clause [c276, c95] c927 (by decide) p (sat_cons (step276 p h) (sat_cons (step95 p h) (sat_nil p)))
def c928 : List Lit := [(50, true), (53, true), (52, false)]
theorem step928 (p : Nat → Bool) (h : Constraints p) : clause p c928 = true :=
  Snake9.LocalRup.prove_clause [c277, c96] c928 (by decide) p (sat_cons (step277 p h) (sat_cons (step96 p h) (sat_nil p)))
def c929 : List Lit := [(55, true), (56, false), (76, true)]
theorem step929 (p : Nat → Bool) (h : Constraints p) : clause p c929 = true :=
  Snake9.LocalRup.prove_clause [c278, c103] c929 (by decide) p (sat_cons (step278 p h) (sat_cons (step103 p h) (sat_nil p)))
def c930 : List Lit := [(54, true), (56, false), (76, true)]
theorem step930 (p : Nat → Bool) (h : Constraints p) : clause p c930 = true :=
  Snake9.LocalRup.prove_clause [c278, c104] c930 (by decide) p (sat_cons (step278 p h) (sat_cons (step104 p h) (sat_nil p)))
def c931 : List Lit := [(55, true), (47, true), (57, false)]
theorem step931 (p : Nat → Bool) (h : Constraints p) : clause p c931 = true :=
  Snake9.LocalRup.prove_clause [c279, c106] c931 (by decide) p (sat_cons (step279 p h) (sat_cons (step106 p h) (sat_nil p)))
def c932 : List Lit := [(59, false), (61, true)]
theorem step932 (p : Nat → Bool) (h : Constraints p) : clause p c932 = true :=
  Snake9.LocalRup.prove_clause [c281, c108] c932 (by decide) p (sat_cons (step281 p h) (sat_cons (step108 p h) (sat_nil p)))
def c933 : List Lit := [(68, true), (78, true), (66, false), (63, true), (65, true)]
theorem step933 (p : Nat → Bool) (h : Constraints p) : clause p c933 = true :=
  Snake9.LocalRup.prove_clause [c282, c130] c933 (by decide) p (sat_cons (step282 p h) (sat_cons (step130 p h) (sat_nil p)))
def c934 : List Lit := [(64, true), (73, true), (70, false), (81, true), (71, true)]
theorem step934 (p : Nat → Bool) (h : Constraints p) : clause p c934 = true :=
  Snake9.LocalRup.prove_clause [c283, c160] c934 (by decide) p (sat_cons (step283 p h) (sat_cons (step160 p h) (sat_nil p)))
def c935 : List Lit := [(71, true), (70, false), (69, true), (73, true), (64, true)]
theorem step935 (p : Nat → Bool) (h : Constraints p) : clause p c935 = true :=
  Snake9.LocalRup.prove_clause [c283, c161] c935 (by decide) p (sat_cons (step283 p h) (sat_cons (step161 p h) (sat_nil p)))
def c936 : List Lit := [(73, true), (69, true), (72, false)]
theorem step936 (p : Nat → Bool) (h : Constraints p) : clause p c936 = true :=
  Snake9.LocalRup.prove_clause [c284, c172] c936 (by decide) p (sat_cons (step284 p h) (sat_cons (step172 p h) (sat_nil p)))
def c937 : List Lit := [(72, false), (73, true), (65, true)]
theorem step937 (p : Nat → Bool) (h : Constraints p) : clause p c937 = true :=
  Snake9.LocalRup.prove_clause [c284, c173] c937 (by decide) p (sat_cons (step284 p h) (sat_cons (step173 p h) (sat_nil p)))
def c938 : List Lit := [(72, false), (65, true), (69, true)]
theorem step938 (p : Nat → Bool) (h : Constraints p) : clause p c938 = true :=
  Snake9.LocalRup.prove_clause [c284, c174] c938 (by decide) p (sat_cons (step284 p h) (sat_cons (step174 p h) (sat_nil p)))
end B112E058
