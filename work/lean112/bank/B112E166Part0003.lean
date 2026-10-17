import B112E166Part0002
namespace B112E166
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c834 : List Lit := [(73, true), (1367, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c732, c825, c396, c772, c831, c465, c472, c481, c528, c500, c505, c833, c482, c475, c473, c832, c466, c501, c507, c510, c514, c527, c494, c496, c619, c813, c603, c821, c492, c819] c834 (by decide) p (sat_cons (step732 p h) (sat_cons (step825 p h) (sat_cons (step396 p h) (sat_cons (step772 p h) (sat_cons (step831 p h) (sat_cons (step465 p h) (sat_cons (step472 p h) (sat_cons (step481 p h) (sat_cons (step528 p h) (sat_cons (step500 p h) (sat_cons (step505 p h) (sat_cons (step833 p h) (sat_cons (step482 p h) (sat_cons (step475 p h) (sat_cons (step473 p h) (sat_cons (step832 p h) (sat_cons (step466 p h) (sat_cons (step501 p h) (sat_cons (step507 p h) (sat_cons (step510 p h) (sat_cons (step514 p h) (sat_cons (step527 p h) (sat_cons (step494 p h) (sat_cons (step496 p h) (sat_cons (step619 p h) (sat_cons (step813 p h) (sat_cons (step603 p h) (sat_cons (step821 p h) (sat_cons (step492 p h) (sat_cons (step819 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c835 : List Lit := [(1419, true), (1367, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c230, c224, c201, c732, c754, c633, c396, c834, c830, c492, c494, c144, c825, c772, c831, c465, c472, c481, c528, c807, c785, c475, c473, c832, c466, c467, c499, c121, c130, c505, c4, c517, c513, c318, c497, c527, c813, c619, c600, c603, c618, c821, c630, c346, c446, c361, c662, c327, c319, c659, c313, c723] c835 (by decide) p (sat_cons (step230 p h) (sat_cons (step224 p h) (sat_cons (step201 p h) (sat_cons (step732 p h) (sat_cons (step754 p h) (sat_cons (step633 p h) (sat_cons (step396 p h) (sat_cons (step834 p h) (sat_cons (step830 p h) (sat_cons (step492 p h) (sat_cons (step494 p h) (sat_cons (step144 p h) (sat_cons (step825 p h) (sat_cons (step772 p h) (sat_cons (step831 p h) (sat_cons (step465 p h) (sat_cons (step472 p h) (sat_cons (step481 p h) (sat_cons (step528 p h) (sat_cons (step807 p h) (sat_cons (step785 p h) (sat_cons (step475 p h) (sat_cons (step473 p h) (sat_cons (step832 p h) (sat_cons (step466 p h) (sat_cons (step467 p h) (sat_cons (step499 p h) (sat_cons (step121 p h) (sat_cons (step130 p h) (sat_cons (step505 p h) (sat_cons (step4 p h) (sat_cons (step517 p h) (sat_cons (step513 p h) (sat_cons (step318 p h) (sat_cons (step497 p h) (sat_cons (step527 p h) (sat_cons (step813 p h) (sat_cons (step619 p h) (sat_cons (step600 p h) (sat_cons (step603 p h) (sat_cons (step618 p h) (sat_cons (step821 p h) (sat_cons (step630 p h) (sat_cons (step346 p h) (sat_cons (step446 p h) (sat_cons (step361 p h) (sat_cons (step662 p h) (sat_cons (step327 p h) (sat_cons (step319 p h) (sat_cons (step659 p h) (sat_cons (step313 p h) (sat_cons (step723 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c836 : List Lit := [(1367, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c732, c754, c753, c633, c210, c396, c771, c772, c786, c807, c785, c825, c834, c830, c492, c835, c482, c531, c816, c532, c619, c497, c768, c813, c600, c603, c618, c563, c569, c630, c759, c544, c446, c566, c358, c697, c347, c338, c345, c344, c339, c340, c32, c29, c540, c542, c546, c824] c836 (by decide) p (sat_cons (step732 p h) (sat_cons (step754 p h) (sat_cons (step753 p h) (sat_cons (step633 p h) (sat_cons (step210 p h) (sat_cons (step396 p h) (sat_cons (step771 p h) (sat_cons (step772 p h) (sat_cons (step786 p h) (sat_cons (step807 p h) (sat_cons (step785 p h) (sat_cons (step825 p h) (sat_cons (step834 p h) (sat_cons (step830 p h) (sat_cons (step492 p h) (sat_cons (step835 p h) (sat_cons (step482 p h) (sat_cons (step531 p h) (sat_cons (step816 p h) (sat_cons (step532 p h) (sat_cons (step619 p h) (sat_cons (step497 p h) (sat_cons (step768 p h) (sat_cons (step813 p h) (sat_cons (step600 p h) (sat_cons (step603 p h) (sat_cons (step618 p h) (sat_cons (step563 p h) (sat_cons (step569 p h) (sat_cons (step630 p h) (sat_cons (step759 p h) (sat_cons (step544 p h) (sat_cons (step446 p h) (sat_cons (step566 p h) (sat_cons (step358 p h) (sat_cons (step697 p h) (sat_cons (step347 p h) (sat_cons (step338 p h) (sat_cons (step345 p h) (sat_cons (step344 p h) (sat_cons (step339 p h) (sat_cons (step340 p h) (sat_cons (step32 p h) (sat_cons (step29 p h) (sat_cons (step540 p h) (sat_cons (step542 p h) (sat_cons (step546 p h) (sat_cons (step824 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c837 : List Lit := [(1369, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c836, c399] c837 (by decide) p (sat_cons (step836 p h) (sat_cons (step399 p h) (sat_nil p)))
def c838 : List Lit := [(1381, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c837, c671] c838 (by decide) p (sat_cons (step837 p h) (sat_cons (step671 p h) (sat_nil p)))
def c839 : List Lit := [(1383, true), (52, true), (1316, false), (1353, false), (1400, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c836, c346, c808, c709, c402, c704] c839 (by decide) p (sat_cons (step836 p h) (sat_cons (step346 p h) (sat_cons (step808 p h) (sat_cons (step709 p h) (sat_cons (step402 p h) (sat_cons (step704 p h) (sat_nil p)))))))
def c840 : List Lit := [(86, true), (1473, true), (1466, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c544, c540, c542, c546, c824] c840 (by decide) p (sat_cons (step544 p h) (sat_cons (step540 p h) (sat_cons (step542 p h) (sat_cons (step546 p h) (sat_cons (step824 p h) (sat_nil p))))))
def c841 : List Lit := [(1478, true), (1436, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c753, c235, c563, c569, c759, c566, c559, c840, c755, c683, c557, c550, c551, c552, c179, c183] c841 (by decide) p (sat_cons (step753 p h) (sat_cons (step235 p h) (sat_cons (step563 p h) (sat_cons (step569 p h) (sat_cons (step759 p h) (sat_cons (step566 p h) (sat_cons (step559 p h) (sat_cons (step840 p h) (sat_cons (step755 p h) (sat_cons (step683 p h) (sat_cons (step557 p h) (sat_cons (step550 p h) (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step179 p h) (sat_cons (step183 p h) (sat_nil p)))))))))))))))))
def c842 : List Lit := [(1470, true), (86, true), (1467, true), (79, false)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c552, c674, c166, c168, c547, c542] c842 (by decide) p (sat_cons (step552 p h) (sat_cons (step674 p h) (sat_cons (step166 p h) (sat_cons (step168 p h) (sat_cons (step547 p h) (sat_cons (step542 p h) (sat_nil p)))))))
def c843 : List Lit := [(1320, false), (47, true), (1400, true), (1353, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c836, c393, c402, c808, c443, c665, c357, c439, c701, c428] c843 (by decide) p (sat_cons (step836 p h) (sat_cons (step393 p h) (sat_cons (step402 p h) (sat_cons (step808 p h) (sat_cons (step443 p h) (sat_cons (step665 p h) (sat_cons (step357 p h) (sat_cons (step439 p h) (sat_cons (step701 p h) (sat_cons (step428 p h) (sat_nil p)))))))))))
def c844 : List Lit := [(68, false), (1436, true), (1442, false), (1419, false)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c753, c732, c633, c222, c836, c206, c210, c209, c478, c526, c616, c841, c604, c502, c813, c606, c573, c603, c619, c615, c746, c531, c630, c482, c459, c456, c457, c105, c107, c393, c402, c808, c443, c700, c334, c336, c331, c332, c19, c843, c346, c342, c343, c340, c341, c337, c338, c31, c32, c30, c22, c25, c29, c842, c687] c844 (by decide) p (sat_cons (step753 p h) (sat_cons (step732 p h) (sat_cons (step633 p h) (sat_cons (step222 p h) (sat_cons (step836 p h) (sat_cons (step206 p h) (sat_cons (step210 p h) (sat_cons (step209 p h) (sat_cons (step478 p h) (sat_cons (step526 p h) (sat_cons (step616 p h) (sat_cons (step841 p h) (sat_cons (step604 p h) (sat_cons (step502 p h) (sat_cons (step813 p h) (sat_cons (step606 p h) (sat_cons (step573 p h) (sat_cons (step603 p h) (sat_cons (step619 p h) (sat_cons (step615 p h) (sat_cons (step746 p h) (sat_cons (step531 p h) (sat_cons (step630 p h) (sat_cons (step482 p h) (sat_cons (step459 p h) (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step105 p h) (sat_cons (step107 p h) (sat_cons (step393 p h) (sat_cons (step402 p h) (sat_cons (step808 p h) (sat_cons (step443 p h) (sat_cons (step700 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step331 p h) (sat_cons (step332 p h) (sat_cons (step19 p h) (sat_cons (step843 p h) (sat_cons (step346 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step340 p h) (sat_cons (step341 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step31 p h) (sat_cons (step32 p h) (sat_cons (step30 p h) (sat_cons (step22 p h) (sat_cons (step25 p h) (sat_cons (step29 p h) (sat_cons (step842 p h) (sat_cons (step687 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c845 : List Lit := [(1320, true), (1436, true), (1508, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c733, c206, c210, c209, c207, c238, c232, c503, c502, c607, c346, c348, c342, c343, c334, c336, c340, c341, c337, c338, c331, c332, c19, c31, c32, c30, c22, c25, c29, c20, c197, c155, c643, c575, c686, c674, c578, c557, c687, c574, c606, c592, c587, c582, c583, c698] c845 (by decide) p (sat_cons (step733 p h) (sat_cons (step206 p h) (sat_cons (step210 p h) (sat_cons (step209 p h) (sat_cons (step207 p h) (sat_cons (step238 p h) (sat_cons (step232 p h) (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_cons (step607 p h) (sat_cons (step346 p h) (sat_cons (step348 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step340 p h) (sat_cons (step341 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step331 p h) (sat_cons (step332 p h) (sat_cons (step19 p h) (sat_cons (step31 p h) (sat_cons (step32 p h) (sat_cons (step30 p h) (sat_cons (step22 p h) (sat_cons (step25 p h) (sat_cons (step29 p h) (sat_cons (step20 p h) (sat_cons (step197 p h) (sat_cons (step155 p h) (sat_cons (step643 p h) (sat_cons (step575 p h) (sat_cons (step686 p h) (sat_cons (step674 p h) (sat_cons (step578 p h) (sat_cons (step557 p h) (sat_cons (step687 p h) (sat_cons (step574 p h) (sat_cons (step606 p h) (sat_cons (step592 p h) (sat_cons (step587 p h) (sat_cons (step582 p h) (sat_cons (step583 p h) (sat_cons (step698 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c846 : List Lit := [(1479, false), (1383, true), (1400, true), (1320, false), (1442, false), (1419, false)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c733, c732, c836, c478, c526, c616, c606, c605, c749, c619, c843, c808, c531, c402, c482, c394, c459, c456, c736, c75] c846 (by decide) p (sat_cons (step733 p h) (sat_cons (step732 p h) (sat_cons (step836 p h) (sat_cons (step478 p h) (sat_cons (step526 p h) (sat_cons (step616 p h) (sat_cons (step606 p h) (sat_cons (step605 p h) (sat_cons (step749 p h) (sat_cons (step619 p h) (sat_cons (step843 p h) (sat_cons (step808 p h) (sat_cons (step531 p h) (sat_cons (step402 p h) (sat_cons (step482 p h) (sat_cons (step394 p h) (sat_cons (step459 p h) (sat_cons (step456 p h) (sat_cons (step736 p h) (sat_cons (step75 p h) (sat_nil p)))))))))))))))))))))
def c847 : List Lit := [(1497, true), (80, false), (1470, false), (1479, true), (86, true), (15, true), (19, false), (1400, true), (1320, false), (1436, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c18, c642, c837, c216, c16, c314, c316, c661, c357, c443, c503, c594, c749, c579, c710, c427, c808, c446, c417, c400, c358, c361, c390, c351, c662, c722, c335, c319, c398, c688, c690, c570, c386, c388, c555, c557, c389, c392, c548, c412, c42, c44, c757, c432, c373, c675, c380, c378, c160, c374, c577, c692] c847 (by decide) p (sat_cons (step18 p h) (sat_cons (step642 p h) (sat_cons (step837 p h) (sat_cons (step216 p h) (sat_cons (step16 p h) (sat_cons (step314 p h) (sat_cons (step316 p h) (sat_cons (step661 p h) (sat_cons (step357 p h) (sat_cons (step443 p h) (sat_cons (step503 p h) (sat_cons (step594 p h) (sat_cons (step749 p h) (sat_cons (step579 p h) (sat_cons (step710 p h) (sat_cons (step427 p h) (sat_cons (step808 p h) (sat_cons (step446 p h) (sat_cons (step417 p h) (sat_cons (step400 p h) (sat_cons (step358 p h) (sat_cons (step361 p h) (sat_cons (step390 p h) (sat_cons (step351 p h) (sat_cons (step662 p h) (sat_cons (step722 p h) (sat_cons (step335 p h) (sat_cons (step319 p h) (sat_cons (step398 p h) (sat_cons (step688 p h) (sat_cons (step690 p h) (sat_cons (step570 p h) (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step555 p h) (sat_cons (step557 p h) (sat_cons (step389 p h) (sat_cons (step392 p h) (sat_cons (step548 p h) (sat_cons (step412 p h) (sat_cons (step42 p h) (sat_cons (step44 p h) (sat_cons (step757 p h) (sat_cons (step432 p h) (sat_cons (step373 p h) (sat_cons (step675 p h) (sat_cons (step380 p h) (sat_cons (step378 p h) (sat_cons (step160 p h) (sat_cons (step374 p h) (sat_cons (step577 p h) (sat_cons (step692 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))
def c848 : List Lit := [(1411, true), (1291, false), (1400, true), (1320, false)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c222, c836, c213, c316, c661, c357, c443, c423, c459, c772, c456, c457, c105, c107, c393, c843, c402, c699, c379, c381, c689, c418, c414, c377, c369, c422, c390, c403, c373, c368, c446, c398, c39, c361, c37, c662, c388, c319, c690] c848 (by decide) p (sat_cons (step222 p h) (sat_cons (step836 p h) (sat_cons (step213 p h) (sat_cons (step316 p h) (sat_cons (step661 p h) (sat_cons (step357 p h) (sat_cons (step443 p h) (sat_cons (step423 p h) (sat_cons (step459 p h) (sat_cons (step772 p h) (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step105 p h) (sat_cons (step107 p h) (sat_cons (step393 p h) (sat_cons (step843 p h) (sat_cons (step402 p h) (sat_cons (step699 p h) (sat_cons (step379 p h) (sat_cons (step381 p h) (sat_cons (step689 p h) (sat_cons (step418 p h) (sat_cons (step414 p h) (sat_cons (step377 p h) (sat_cons (step369 p h) (sat_cons (step422 p h) (sat_cons (step390 p h) (sat_cons (step403 p h) (sat_cons (step373 p h) (sat_cons (step368 p h) (sat_cons (step446 p h) (sat_cons (step398 p h) (sat_cons (step39 p h) (sat_cons (step361 p h) (sat_cons (step37 p h) (sat_cons (step662 p h) (sat_cons (step388 p h) (sat_cons (step319 p h) (sat_cons (step690 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c849 : List Lit := [(1316, true), (1400, true), (1436, true), (1442, false), (1419, false)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c210, c209, c642, c18, c753, c732, c478, c526, c616, c845, c841, c502, c342, c343, c340, c341, c337, c338, c32, c30, c16, c23, c29, c314, c316, c661, c357, c443, c846, c848, c573, c482, c842, c531, c687, c619, c847, c603] c849 (by decide) p (sat_cons (step210 p h) (sat_cons (step209 p h) (sat_cons (step642 p h) (sat_cons (step18 p h) (sat_cons (step753 p h) (sat_cons (step732 p h) (sat_cons (step478 p h) (sat_cons (step526 p h) (sat_cons (step616 p h) (sat_cons (step845 p h) (sat_cons (step841 p h) (sat_cons (step502 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step340 p h) (sat_cons (step341 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step32 p h) (sat_cons (step30 p h) (sat_cons (step16 p h) (sat_cons (step23 p h) (sat_cons (step29 p h) (sat_cons (step314 p h) (sat_cons (step316 p h) (sat_cons (step661 p h) (sat_cons (step357 p h) (sat_cons (step443 p h) (sat_cons (step846 p h) (sat_cons (step848 p h) (sat_cons (step573 p h) (sat_cons (step482 p h) (sat_cons (step842 p h) (sat_cons (step531 p h) (sat_cons (step687 p h) (sat_cons (step619 p h) (sat_cons (step847 p h) (sat_cons (step603 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c850 : List Lit := [(1383, true), (1316, false), (1400, true), (1320, false), (68, true), (73, false), (1419, false)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c836, c703, c705, c689, c402, c704, c848, c709, c482, c830, c816, c492, c497] c850 (by decide) p (sat_cons (step836 p h) (sat_cons (step703 p h) (sat_cons (step705 p h) (sat_cons (step689 p h) (sat_cons (step402 p h) (sat_cons (step704 p h) (sat_cons (step848 p h) (sat_cons (step709 p h) (sat_cons (step482 p h) (sat_cons (step830 p h) (sat_cons (step816 p h) (sat_cons (step492 p h) (sat_cons (step497 p h) (sat_nil p))))))))))))))
def c851 : List Lit := [(1400, true), (1438, true), (1442, false), (1419, false)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c732, c206, c836, c212, c478, c526, c616, c504, c845, c665, c844, c505, c500, c439, c849, c850, c443, c700, c357, c334, c336, c661, c786, c331, c19, c316, c318, c24, c704, c370, c402, c699, c381, c413, c428, c433, c418, c414, c384, c382, c390, c403, c371, c377, c398, c368, c373, c690, c35, c388, c37] c851 (by decide) p (sat_cons (step732 p h) (sat_cons (step206 p h) (sat_cons (step836 p h) (sat_cons (step212 p h) (sat_cons (step478 p h) (sat_cons (step526 p h) (sat_cons (step616 p h) (sat_cons (step504 p h) (sat_cons (step845 p h) (sat_cons (step665 p h) (sat_cons (step844 p h) (sat_cons (step505 p h) (sat_cons (step500 p h) (sat_cons (step439 p h) (sat_cons (step849 p h) (sat_cons (step850 p h) (sat_cons (step443 p h) (sat_cons (step700 p h) (sat_cons (step357 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step661 p h) (sat_cons (step786 p h) (sat_cons (step331 p h) (sat_cons (step19 p h) (sat_cons (step316 p h) (sat_cons (step318 p h) (sat_cons (step24 p h) (sat_cons (step704 p h) (sat_cons (step370 p h) (sat_cons (step402 p h) (sat_cons (step699 p h) (sat_cons (step381 p h) (sat_cons (step413 p h) (sat_cons (step428 p h) (sat_cons (step433 p h) (sat_cons (step418 p h) (sat_cons (step414 p h) (sat_cons (step384 p h) (sat_cons (step382 p h) (sat_cons (step390 p h) (sat_cons (step403 p h) (sat_cons (step371 p h) (sat_cons (step377 p h) (sat_cons (step398 p h) (sat_cons (step368 p h) (sat_cons (step373 p h) (sat_cons (step690 p h) (sat_cons (step35 p h) (sat_cons (step388 p h) (sat_cons (step37 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c852 : List Lit := [(45, true), (152, true), (54, true), (47, true), (52, true), (1353, false), (1385, true), (1401, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c836, c217, c216, c206, c211, c429, c395, c49, c405, c52, c419, c386, c390, c389, c392, c388, c414, c42, c44, c428, c434, c373, c444, c377, c700, c382, c334, c336, c370, c331, c19, c33, c634] c852 (by decide) p (sat_cons (step836 p h) (sat_cons (step217 p h) (sat_cons (step216 p h) (sat_cons (step206 p h) (sat_cons (step211 p h) (sat_cons (step429 p h) (sat_cons (step395 p h) (sat_cons (step49 p h) (sat_cons (step405 p h) (sat_cons (step52 p h) (sat_cons (step419 p h) (sat_cons (step386 p h) (sat_cons (step390 p h) (sat_cons (step389 p h) (sat_cons (step392 p h) (sat_cons (step388 p h) (sat_cons (step414 p h) (sat_cons (step42 p h) (sat_cons (step44 p h) (sat_cons (step428 p h) (sat_cons (step434 p h) (sat_cons (step373 p h) (sat_cons (step444 p h) (sat_cons (step377 p h) (sat_cons (step700 p h) (sat_cons (step382 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step370 p h) (sat_cons (step331 p h) (sat_cons (step19 p h) (sat_cons (step33 p h) (sat_cons (step634 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c853 : List Lit := [(44, true), (46, false), (45, false), (152, true), (155, true), (64, true), (58, false), (52, true), (66, true)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c218, c63, c50, c77, c56] c853 (by decide) p (sat_cons (step218 p h) (sat_cons (step63 p h) (sat_cons (step50 p h) (sat_cons (step77 p h) (sat_cons (step56 p h) (sat_nil p))))))
def c854 : List Lit := [(1, false), (45, false), (152, true), (155, true), (169, true), (1294, true), (64, true), (54, true), (59, true), (58, false), (52, true), (66, true)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c201, c217, c223, c685, c319, c4, c853, c690, c52, c119, c54, c112] c854 (by decide) p (sat_cons (step201 p h) (sat_cons (step217 p h) (sat_cons (step223 p h) (sat_cons (step685 p h) (sat_cons (step319 p h) (sat_cons (step4 p h) (sat_cons (step853 p h) (sat_cons (step690 p h) (sat_cons (step52 p h) (sat_cons (step119 p h) (sat_cons (step54 p h) (sat_cons (step112 p h) (sat_nil p)))))))))))))
def c855 : List Lit := [(1438, true), (1442, false), (1419, false)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.TreeRup.prove_clause [c732, c230, c733, c633, c222, c224, c836, c229, c225, c652, c312, c218, c203, c478, c526, c616, c504, c505, c499, c500, c828, c144, c145, c467, c841, c844, c602, c614, c631, c845, c665, c851, c440, c630, c615, c618, c603, c531, c527, c749, c479, c482, c516, c476, c459, c461, c772, c497, c456, c457, c491, c492, c105, c106, c110, c107, c465, c466, c393, c474, c121, c402, c469, c146, c808, c142, c141, c447, c100, c139, c361, c124, c662, c134, c317, c281, c282, c283, c284, c285, c293, c280, c307, c279, c310, c278, c272, c274, c270, c254, c268, c252, c261, c262, c245, c260, c257, c243, c259, c256, c242, c11, c852, c854, c57, c9, c68, c315] c855 (by decide) p (sat_cons (step732 p h) (sat_cons (step230 p h) (sat_cons (step733 p h) (sat_cons (step633 p h) (sat_cons (step222 p h) (sat_cons (step224 p h) (sat_cons (step836 p h) (sat_cons (step229 p h) (sat_cons (step225 p h) (sat_cons (step652 p h) (sat_cons (step312 p h) (sat_cons (step218 p h) (sat_cons (step203 p h) (sat_cons (step478 p h) (sat_cons (step526 p h) (sat_cons (step616 p h) (sat_cons (step504 p h) (sat_cons (step505 p h) (sat_cons (step499 p h) (sat_cons (step500 p h) (sat_cons (step828 p h) (sat_cons (step144 p h) (sat_cons (step145 p h) (sat_cons (step467 p h) (sat_cons (step841 p h) (sat_cons (step844 p h) (sat_cons (step602 p h) (sat_cons (step614 p h) (sat_cons (step631 p h) (sat_cons (step845 p h) (sat_cons (step665 p h) (sat_cons (step851 p h) (sat_cons (step440 p h) (sat_cons (step630 p h) (sat_cons (step615 p h) (sat_cons (step618 p h) (sat_cons (step603 p h) (sat_cons (step531 p h) (sat_cons (step527 p h) (sat_cons (step749 p h) (sat_cons (step479 p h) (sat_cons (step482 p h) (sat_cons (step516 p h) (sat_cons (step476 p h) (sat_cons (step459 p h) (sat_cons (step461 p h) (sat_cons (step772 p h) (sat_cons (step497 p h) (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step491 p h) (sat_cons (step492 p h) (sat_cons (step105 p h) (sat_cons (step106 p h) (sat_cons (step110 p h) (sat_cons (step107 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step393 p h) (sat_cons (step474 p h) (sat_cons (step121 p h) (sat_cons (step402 p h) (sat_cons (step469 p h) (sat_cons (step146 p h) (sat_cons (step808 p h) (sat_cons (step142 p h) (sat_cons (step141 p h) (sat_cons (step447 p h) (sat_cons (step100 p h) (sat_cons (step139 p h) (sat_cons (step361 p h) (sat_cons (step124 p h) (sat_cons (step662 p h) (sat_cons (step134 p h) (sat_cons (step317 p h) (sat_cons (step281 p h) (sat_cons (step282 p h) (sat_cons (step283 p h) (sat_cons (step284 p h) (sat_cons (step285 p h) (sat_cons (step293 p h) (sat_cons (step280 p h) (sat_cons (step307 p h) (sat_cons (step279 p h) (sat_cons (step310 p h) (sat_cons (step278 p h) (sat_cons (step272 p h) (sat_cons (step274 p h) (sat_cons (step270 p h) (sat_cons (step254 p h) (sat_cons (step268 p h) (sat_cons (step252 p h) (sat_cons (step261 p h) (sat_cons (step262 p h) (sat_cons (step245 p h) (sat_cons (step260 p h) (sat_cons (step257 p h) (sat_cons (step243 p h) (sat_cons (step259 p h) (sat_cons (step256 p h) (sat_cons (step242 p h) (sat_cons (step11 p h) (sat_cons (step852 p h) (sat_cons (step854 p h) (sat_cons (step57 p h) (sat_cons (step9 p h) (sat_cons (step68 p h) (sat_cons (step315 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c856 : List Lit := [(2, false), (46, true)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c201, c4] c856 (by decide) p (sat_cons (step201 p h) (sat_cons (step4 p h) (sat_nil p)))
def c857 : List Lit := [(48, true), (3, false), (1, true)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c202, c5] c857 (by decide) p (sat_cons (step202 p h) (sat_cons (step5 p h) (sat_nil p)))
def c858 : List Lit := [(4, true), (5, false), (6, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c203, c8] c858 (by decide) p (sat_cons (step203 p h) (sat_cons (step8 p h) (sat_nil p)))
def c859 : List Lit := [(1, true), (5, false), (6, true)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c203, c9] c859 (by decide) p (sat_cons (step203 p h) (sat_cons (step9 p h) (sat_nil p)))
def c860 : List Lit := [(7, false), (9, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c204, c12] c860 (by decide) p (sat_cons (step204 p h) (sat_cons (step12 p h) (sat_nil p)))
def c861 : List Lit := [(7, false), (4, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c204, c13] c861 (by decide) p (sat_cons (step204 p h) (sat_cons (step13 p h) (sat_nil p)))
def c862 : List Lit := [(9, false), (2, true), (118, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c644, c15] c862 (by decide) p (sat_cons (step644 p h) (sat_cons (step15 p h) (sat_nil p)))
def c863 : List Lit := [(3, false), (19, false)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c18, c642, c16] c863 (by decide) p (sat_cons (step18 p h) (sat_cons (step642 p h) (sat_cons (step16 p h) (sat_nil p))))
def c864 : List Lit := [(13, false), (16, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c206, c19] c864 (by decide) p (sat_cons (step206 p h) (sat_cons (step19 p h) (sat_nil p)))
def c865 : List Lit := [(18, true), (15, true), (14, false)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c207, c20] c865 (by decide) p (sat_cons (step207 p h) (sat_cons (step20 p h) (sat_nil p)))
def c866 : List Lit := [(22, false), (89, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c209, c30] c866 (by decide) p (sat_cons (step209 p h) (sat_cons (step30 p h) (sat_nil p)))
def c867 : List Lit := [(24, false), (26, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c210, c31] c867 (by decide) p (sat_cons (step210 p h) (sat_cons (step31 p h) (sat_nil p)))
def c868 : List Lit := [(24, false), (20, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c210, c32] c868 (by decide) p (sat_cons (step210 p h) (sat_cons (step32 p h) (sat_nil p)))
def c869 : List Lit := [(25, false), (26, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c211, c33] c869 (by decide) p (sat_cons (step211 p h) (sat_cons (step33 p h) (sat_nil p)))
def c870 : List Lit := [(25, false), (16, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c211, c34] c870 (by decide) p (sat_cons (step211 p h) (sat_cons (step34 p h) (sat_nil p)))
def c871 : List Lit := [(28, false), (31, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c212, c35] c871 (by decide) p (sat_cons (step212 p h) (sat_cons (step35 p h) (sat_nil p)))
def c872 : List Lit := [(32, false), (41, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c213, c38] c872 (by decide) p (sat_cons (step213 p h) (sat_cons (step38 p h) (sat_nil p)))
def c873 : List Lit := [(32, false), (31, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c213, c39] c873 (by decide) p (sat_cons (step213 p h) (sat_cons (step39 p h) (sat_nil p)))
def c874 : List Lit := [(30, true), (95, true), (34, false)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c214, c40] c874 (by decide) p (sat_cons (step214 p h) (sat_cons (step40 p h) (sat_nil p)))
def c875 : List Lit := [(37, false), (42, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c215, c41] c875 (by decide) p (sat_cons (step215 p h) (sat_cons (step41 p h) (sat_nil p)))
def c876 : List Lit := [(39, false), (41, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c216, c42] c876 (by decide) p (sat_cons (step216 p h) (sat_cons (step42 p h) (sat_nil p)))
def c877 : List Lit := [(1, true), (48, true), (45, false), (64, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c218, c57] c877 (by decide) p (sat_cons (step218 p h) (sat_cons (step57 p h) (sat_nil p)))
def c878 : List Lit := [(60, true), (46, true), (50, false), (48, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c220, c88] c878 (by decide) p (sat_cons (step220 p h) (sat_cons (step88 p h) (sat_nil p)))
def c879 : List Lit := [(46, true), (50, false), (48, true), (49, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c220, c89] c879 (by decide) p (sat_cons (step220 p h) (sat_cons (step89 p h) (sat_nil p)))
def c880 : List Lit := [(51, true), (55, true), (53, false)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c221, c101] c880 (by decide) p (sat_cons (step221 p h) (sat_cons (step101 p h) (sat_nil p)))
def c881 : List Lit := [(56, false), (57, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c222, c105] c881 (by decide) p (sat_cons (step222 p h) (sat_cons (step105 p h) (sat_nil p)))
def c882 : List Lit := [(62, false), (65, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c224, c121] c882 (by decide) p (sat_cons (step224 p h) (sat_cons (step121 p h) (sat_nil p)))
def c883 : List Lit := [(67, true), (64, true), (63, false)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true :=
  Snake9.LocalRup.prove_clause [c225, c124] c883 (by decide) p (sat_cons (step225 p h) (sat_cons (step124 p h) (sat_nil p)))
def c884 : List Lit := [(46, true), (75, true), (66, false)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true :=
  Snake9.LocalRup.prove_clause [c226, c131] c884 (by decide) p (sat_cons (step226 p h) (sat_cons (step131 p h) (sat_nil p)))
def c885 : List Lit := [(67, true), (64, true), (48, true), (68, false)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true :=
  Snake9.LocalRup.prove_clause [c227, c136] c885 (by decide) p (sat_cons (step227 p h) (sat_cons (step136 p h) (sat_nil p)))
def c886 : List Lit := [(72, true), (76, true), (71, false)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true :=
  Snake9.LocalRup.prove_clause [c229, c141] c886 (by decide) p (sat_cons (step229 p h) (sat_cons (step141 p h) (sat_nil p)))
def c887 : List Lit := [(55, true), (76, true), (71, false)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true :=
  Snake9.LocalRup.prove_clause [c229, c142] c887 (by decide) p (sat_cons (step229 p h) (sat_cons (step142 p h) (sat_nil p)))
def c888 : List Lit := [(72, true), (55, true), (71, false)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true :=
  Snake9.LocalRup.prove_clause [c229, c143] c888 (by decide) p (sat_cons (step229 p h) (sat_cons (step143 p h) (sat_nil p)))
def c889 : List Lit := [(73, false), (75, true)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true :=
  Snake9.LocalRup.prove_clause [c230, c144] c889 (by decide) p (sat_cons (step230 p h) (sat_cons (step144 p h) (sat_nil p)))
def c890 : List Lit := [(73, false), (69, true)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true :=
  Snake9.LocalRup.prove_clause [c230, c145] c890 (by decide) p (sat_cons (step230 p h) (sat_cons (step145 p h) (sat_nil p)))
def c891 : List Lit := [(88, true), (80, true), (78, false)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.LocalRup.prove_clause [c232, c155] c891 (by decide) p (sat_cons (step232 p h) (sat_cons (step155 p h) (sat_nil p)))
def c892 : List Lit := [(94, true), (84, false), (82, true), (80, true)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true :=
  Snake9.LocalRup.prove_clause [c234, c173] c892 (by decide) p (sat_cons (step234 p h) (sat_cons (step173 p h) (sat_nil p)))
def c893 : List Lit := [(83, true), (84, false), (80, true), (82, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true :=
  Snake9.LocalRup.prove_clause [c234, c174] c893 (by decide) p (sat_cons (step234 p h) (sat_cons (step174 p h) (sat_nil p)))
def c894 : List Lit := [(90, false), (85, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true :=
  Snake9.LocalRup.prove_clause [c235, c180] c894 (by decide) p (sat_cons (step235 p h) (sat_cons (step180 p h) (sat_nil p)))
def c895 : List Lit := [(91, true), (92, false), (82, true)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true :=
  Snake9.LocalRup.prove_clause [c236, c186] c895 (by decide) p (sat_cons (step236 p h) (sat_cons (step186 p h) (sat_nil p)))
def c896 : List Lit := [(97, false), (95, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true :=
  Snake9.LocalRup.prove_clause [c237, c193] c896 (by decide) p (sat_cons (step237 p h) (sat_cons (step193 p h) (sat_nil p)))
def c897 : List Lit := [(101, false), (80, true)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true :=
  Snake9.LocalRup.prove_clause [c238, c197] c897 (by decide) p (sat_cons (step238 p h) (sat_cons (step197 p h) (sat_nil p)))
end B112E166
