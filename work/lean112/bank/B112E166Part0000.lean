import B112E166Inputs
namespace B112E166
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c642 : List Lit := [(10, true)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true :=
  Snake9.LocalRup.prove_clause [c18, c17] c642 (by decide) p (sat_cons (step18 p h) (sat_cons (step17 p h) (sat_nil p)))
def c643 : List Lit := [(19, false), (18, false), (82, false)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true :=
  Snake9.LocalRup.prove_clause [c642, c27] c643 (by decide) p (sat_cons (step642 p h) (sat_cons (step27 p h) (sat_nil p)))
def c644 : List Lit := [(8, false)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true :=
  Snake9.LocalRup.prove_clause [c205, c14] c644 (by decide) p (sat_cons (step205 p h) (sat_cons (step14 p h) (sat_nil p)))
def c645 : List Lit := [(430, false)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true :=
  Snake9.LocalRup.prove_clause [c312, c309] c645 (by decide) p (sat_cons (step312 p h) (sat_cons (step309 p h) (sat_nil p)))
def c646 : List Lit := [(324, false)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true :=
  Snake9.LocalRup.prove_clause [c312, c311] c646 (by decide) p (sat_cons (step312 p h) (sat_cons (step311 p h) (sat_nil p)))
def c647 : List Lit := [(428, false)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true :=
  Snake9.LocalRup.prove_clause [c645, c306] c647 (by decide) p (sat_cons (step645 p h) (sat_cons (step306 p h) (sat_nil p)))
def c648 : List Lit := [(376, false)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true :=
  Snake9.LocalRup.prove_clause [c645, c308] c648 (by decide) p (sat_cons (step645 p h) (sat_cons (step308 p h) (sat_nil p)))
def c649 : List Lit := [(322, false)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true :=
  Snake9.LocalRup.prove_clause [c646, c273] c649 (by decide) p (sat_cons (step646 p h) (sat_cons (step273 p h) (sat_nil p)))
def c650 : List Lit := [(270, false)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true :=
  Snake9.LocalRup.prove_clause [c646, c276] c650 (by decide) p (sat_cons (step646 p h) (sat_cons (step276 p h) (sat_nil p)))
def c651 : List Lit := [(400, false)]
theorem step651 (p : Nat → Bool) (h : Constraints p) : clause p c651 = true :=
  Snake9.LocalRup.prove_clause [c647, c305] c651 (by decide) p (sat_cons (step647 p h) (sat_cons (step305 p h) (sat_nil p)))
def c652 : List Lit := [(348, false)]
theorem step652 (p : Nat → Bool) (h : Constraints p) : clause p c652 = true :=
  Snake9.LocalRup.prove_clause [c648, c294] c652 (by decide) p (sat_cons (step648 p h) (sat_cons (step294 p h) (sat_nil p)))
def c653 : List Lit := [(320, false)]
theorem step653 (p : Nat → Bool) (h : Constraints p) : clause p c653 = true :=
  Snake9.LocalRup.prove_clause [c649, c271] c653 (by decide) p (sat_cons (step649 p h) (sat_cons (step271 p h) (sat_nil p)))
def c654 : List Lit := [(242, false)]
theorem step654 (p : Nat → Bool) (h : Constraints p) : clause p c654 = true :=
  Snake9.LocalRup.prove_clause [c650, c255] c654 (by decide) p (sat_cons (step650 p h) (sat_cons (step255 p h) (sat_nil p)))
def c655 : List Lit := [(386, false)]
theorem step655 (p : Nat → Bool) (h : Constraints p) : clause p c655 = true :=
  Snake9.LocalRup.prove_clause [c651, c304] c655 (by decide) p (sat_cons (step651 p h) (sat_cons (step304 p h) (sat_nil p)))
def c656 : List Lit := [(228, false)]
theorem step656 (p : Nat → Bool) (h : Constraints p) : clause p c656 = true :=
  Snake9.LocalRup.prove_clause [c654, c253] c656 (by decide) p (sat_cons (step654 p h) (sat_cons (step253 p h) (sat_nil p)))
def c657 : List Lit := [(1296, true)]
theorem step657 (p : Nat → Bool) (h : Constraints p) : clause p c657 = true :=
  Snake9.LocalRup.prove_clause [c644, c321] c657 (by decide) p (sat_cons (step644 p h) (sat_cons (step321 p h) (sat_nil p)))
def c658 : List Lit := [(1298, true)]
theorem step658 (p : Nat → Bool) (h : Constraints p) : clause p c658 = true :=
  Snake9.LocalRup.prove_clause [c657, c322] c658 (by decide) p (sat_cons (step657 p h) (sat_cons (step322 p h) (sat_nil p)))
def c659 : List Lit := [(7, true), (1299, true)]
theorem step659 (p : Nat → Bool) (h : Constraints p) : clause p c659 = true :=
  Snake9.LocalRup.prove_clause [c657, c323] c659 (by decide) p (sat_cons (step657 p h) (sat_cons (step323 p h) (sat_nil p)))
def c660 : List Lit := [(1301, true)]
theorem step660 (p : Nat → Bool) (h : Constraints p) : clause p c660 = true :=
  Snake9.LocalRup.prove_clause [c658, c324] c660 (by decide) p (sat_cons (step658 p h) (sat_cons (step324 p h) (sat_nil p)))
def c661 : List Lit := [(1293, false), (1302, true)]
theorem step661 (p : Nat → Bool) (h : Constraints p) : clause p c661 = true :=
  Snake9.LocalRup.prove_clause [c658, c326] c661 (by decide) p (sat_cons (step658 p h) (sat_cons (step326 p h) (sat_nil p)))
def c662 : List Lit := [(1294, false), (1303, true)]
theorem step662 (p : Nat → Bool) (h : Constraints p) : clause p c662 = true :=
  Snake9.LocalRup.prove_clause [c658, c328] c662 (by decide) p (sat_cons (step658 p h) (sat_cons (step328 p h) (sat_nil p)))
def c663 : List Lit := [(1295, false), (1304, true)]
theorem step663 (p : Nat → Bool) (h : Constraints p) : clause p c663 = true :=
  Snake9.LocalRup.prove_clause [c658, c330] c663 (by decide) p (sat_cons (step658 p h) (sat_cons (step330 p h) (sat_nil p)))
def c664 : List Lit := [(1327, true)]
theorem step664 (p : Nat → Bool) (h : Constraints p) : clause p c664 = true :=
  Snake9.LocalRup.prove_clause [c660, c352] c664 (by decide) p (sat_cons (step660 p h) (sat_cons (step352 p h) (sat_nil p)))
def c665 : List Lit := [(1320, false), (1328, true)]
theorem step665 (p : Nat → Bool) (h : Constraints p) : clause p c665 = true :=
  Snake9.LocalRup.prove_clause [c660, c353] c665 (by decide) p (sat_cons (step660 p h) (sat_cons (step353 p h) (sat_nil p)))
def c666 : List Lit := [(1321, false), (1329, true)]
theorem step666 (p : Nat → Bool) (h : Constraints p) : clause p c666 = true :=
  Snake9.LocalRup.prove_clause [c660, c354] c666 (by decide) p (sat_cons (step660 p h) (sat_cons (step354 p h) (sat_nil p)))
def c667 : List Lit := [(1322, false), (1330, true)]
theorem step667 (p : Nat → Bool) (h : Constraints p) : clause p c667 = true :=
  Snake9.LocalRup.prove_clause [c660, c355] c667 (by decide) p (sat_cons (step660 p h) (sat_cons (step355 p h) (sat_nil p)))
def c668 : List Lit := [(1383, false), (1398, true)]
theorem step668 (p : Nat → Bool) (h : Constraints p) : clause p c668 = true :=
  Snake9.LocalRup.prove_clause [c664, c437] c668 (by decide) p (sat_cons (step664 p h) (sat_cons (step437 p h) (sat_nil p)))
def c669 : List Lit := [(1436, true), (1465, true), (1321, true)]
theorem step669 (p : Nat → Bool) (h : Constraints p) : clause p c669 = true :=
  Snake9.LocalRup.prove_clause [c232, c233, c543, c541, c540, c545, c351, c335, c347, c345, c502, c503, c165, c154, c157, c158, c159, c333, c21, c22, c339] c669 (by decide) p (sat_cons (step232 p h) (sat_cons (step233 p h) (sat_cons (step543 p h) (sat_cons (step541 p h) (sat_cons (step540 p h) (sat_cons (step545 p h) (sat_cons (step351 p h) (sat_cons (step335 p h) (sat_cons (step347 p h) (sat_cons (step345 p h) (sat_cons (step502 p h) (sat_cons (step503 p h) (sat_cons (step165 p h) (sat_cons (step154 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step159 p h) (sat_cons (step333 p h) (sat_cons (step21 p h) (sat_cons (step22 p h) (sat_cons (step339 p h) (sat_nil p))))))))))))))))))))))
def c670 : List Lit := [(1422, true)]
theorem step670 (p : Nat → Bool) (h : Constraints p) : clause p c670 = true :=
  Snake9.LocalRup.prove_clause [c222, c477, c480, c472, c459, c465, c456, c457, c105, c110] c670 (by decide) p (sat_cons (step222 p h) (sat_cons (step477 p h) (sat_cons (step480 p h) (sat_cons (step472 p h) (sat_cons (step459 p h) (sat_cons (step465 p h) (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step105 p h) (sat_cons (step110 p h) (sat_nil p)))))))))))
def c671 : List Lit := [(1369, false), (1381, true)]
theorem step671 (p : Nat → Bool) (h : Constraints p) : clause p c671 = true :=
  Snake9.LocalRup.prove_clause [c216, c421, c407, c412, c425, c389, c391, c379, c387, c42, c377, c44, c373] c671 (by decide) p (sat_cons (step216 p h) (sat_cons (step421 p h) (sat_cons (step407 p h) (sat_cons (step412 p h) (sat_cons (step425 p h) (sat_cons (step389 p h) (sat_cons (step391 p h) (sat_cons (step379 p h) (sat_cons (step387 p h) (sat_cons (step42 p h) (sat_cons (step377 p h) (sat_cons (step44 p h) (sat_cons (step373 p h) (sat_nil p))))))))))))))
def c672 : List Lit := [(1362, true), (1354, true)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true :=
  Snake9.LocalRup.prove_clause [c216, c215, c212, c380, c389, c391, c387, c42, c44, c373, c377, c378, c382, c374, c369, c41, c368, c43, c35] c672 (by decide) p (sat_cons (step216 p h) (sat_cons (step215 p h) (sat_cons (step212 p h) (sat_cons (step380 p h) (sat_cons (step389 p h) (sat_cons (step391 p h) (sat_cons (step387 p h) (sat_cons (step42 p h) (sat_cons (step44 p h) (sat_cons (step373 p h) (sat_cons (step377 p h) (sat_cons (step378 p h) (sat_cons (step382 p h) (sat_cons (step374 p h) (sat_cons (step369 p h) (sat_cons (step41 p h) (sat_cons (step368 p h) (sat_cons (step43 p h) (sat_cons (step35 p h) (sat_nil p))))))))))))))))))))
def c673 : List Lit := [(1419, true), (1381, true)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true :=
  Snake9.LocalRup.prove_clause [c218, c217, c215, c213, c224, c219, c421, c416, c390, c430, c672, c411, c425, c379, c377, c373, c38, c376, c374, c41, c39, c43, c388, c671, c399, c397, c396, c401, c394, c48, c53, c61, c467, c393, c74, c56, c471, c473, c469, c464, c465, c122, c83, c123, c64] c673 (by decide) p (sat_cons (step218 p h) (sat_cons (step217 p h) (sat_cons (step215 p h) (sat_cons (step213 p h) (sat_cons (step224 p h) (sat_cons (step219 p h) (sat_cons (step421 p h) (sat_cons (step416 p h) (sat_cons (step390 p h) (sat_cons (step430 p h) (sat_cons (step672 p h) (sat_cons (step411 p h) (sat_cons (step425 p h) (sat_cons (step379 p h) (sat_cons (step377 p h) (sat_cons (step373 p h) (sat_cons (step38 p h) (sat_cons (step376 p h) (sat_cons (step374 p h) (sat_cons (step41 p h) (sat_cons (step39 p h) (sat_cons (step43 p h) (sat_cons (step388 p h) (sat_cons (step671 p h) (sat_cons (step399 p h) (sat_cons (step397 p h) (sat_cons (step396 p h) (sat_cons (step401 p h) (sat_cons (step394 p h) (sat_cons (step48 p h) (sat_cons (step53 p h) (sat_cons (step61 p h) (sat_cons (step467 p h) (sat_cons (step393 p h) (sat_cons (step74 p h) (sat_cons (step56 p h) (sat_cons (step471 p h) (sat_cons (step473 p h) (sat_cons (step469 p h) (sat_cons (step464 p h) (sat_cons (step465 p h) (sat_cons (step122 p h) (sat_cons (step83 p h) (sat_cons (step123 p h) (sat_cons (step64 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c674 : List Lit := [(82, true), (1470, true)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true :=
  Snake9.LocalRup.prove_clause [c236, c552, c551, c185, c186, c641] c674 (by decide) p (sat_cons (step236 p h) (sat_cons (step552 p h) (sat_cons (step551 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step641 p h) (sat_nil p)))))))
def c675 : List Lit := [(1479, true), (84, true), (81, true), (1470, false)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true :=
  Snake9.LocalRup.prove_clause [c235, c541, c546, c554, c570, c573, c557, c547, c548, c549, c542, c180, c175] c675 (by decide) p (sat_cons (step235 p h) (sat_cons (step541 p h) (sat_cons (step546 p h) (sat_cons (step554 p h) (sat_cons (step570 p h) (sat_cons (step573 p h) (sat_cons (step557 p h) (sat_cons (step547 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step542 p h) (sat_cons (step180 p h) (sat_cons (step175 p h) (sat_nil p))))))))))))))
def c676 : List Lit := [(53, false), (56, false), (52, false)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true :=
  Snake9.LocalRup.prove_clause [c222, c90, c106] c676 (by decide) p (sat_cons (step222 p h) (sat_cons (step90 p h) (sat_cons (step106 p h) (sat_nil p))))
def c677 : List Lit := [(44, false), (45, false), (53, false), (52, false)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true :=
  Snake9.LocalRup.prove_clause [c217, c48, c103, c52] c677 (by decide) p (sat_cons (step217 p h) (sat_cons (step48 p h) (sat_cons (step103 p h) (sat_cons (step52 p h) (sat_nil p)))))
def c678 : List Lit := [(5, true), (1329, true)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true :=
  Snake9.LocalRup.prove_clause [c642, c18, c360, c662, c317, c313, c315, c316, c16, c661, c338, c357, c343, c346] c678 (by decide) p (sat_cons (step642 p h) (sat_cons (step18 p h) (sat_cons (step360 p h) (sat_cons (step662 p h) (sat_cons (step317 p h) (sat_cons (step313 p h) (sat_cons (step315 p h) (sat_cons (step316 p h) (sat_cons (step16 p h) (sat_cons (step661 p h) (sat_cons (step338 p h) (sat_cons (step357 p h) (sat_cons (step343 p h) (sat_cons (step346 p h) (sat_nil p)))))))))))))))
def c679 : List Lit := [(63, false), (1432, true), (64, false), (45, false)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true :=
  Snake9.LocalRup.prove_clause [c125, c126, c497, c492] c679 (by decide) p (sat_cons (step125 p h) (sat_cons (step126 p h) (sat_cons (step497 p h) (sat_cons (step492 p h) (sat_nil p)))))
def c680 : List Lit := [(1476, true), (79, false)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true :=
  Snake9.LocalRup.prove_clause [c561, c564, c554, c545, c552, c674, c166] c680 (by decide) p (sat_cons (step561 p h) (sat_cons (step564 p h) (sat_cons (step554 p h) (sat_cons (step545 p h) (sat_cons (step552 p h) (sat_cons (step674 p h) (sat_cons (step166 p h) (sat_nil p))))))))
def c681 : List Lit := [(86, false), (90, false), (87, false)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true :=
  Snake9.LocalRup.prove_clause [c235, c175, c180] c681 (by decide) p (sat_cons (step235 p h) (sat_cons (step175 p h) (sat_cons (step180 p h) (sat_nil p))))
def c682 : List Lit := [(1470, true), (1506, true), (79, false)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true :=
  Snake9.LocalRup.prove_clause [c552, c674, c166, c170, c168, c583, c541, c587, c546, c589, c602, c572, c569, c547, c556, c542, c548, c549, c681] c682 (by decide) p (sat_cons (step552 p h) (sat_cons (step674 p h) (sat_cons (step166 p h) (sat_cons (step170 p h) (sat_cons (step168 p h) (sat_cons (step583 p h) (sat_cons (step541 p h) (sat_cons (step587 p h) (sat_cons (step546 p h) (sat_cons (step589 p h) (sat_cons (step602 p h) (sat_cons (step572 p h) (sat_cons (step569 p h) (sat_cons (step547 p h) (sat_cons (step556 p h) (sat_cons (step542 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step681 p h) (sat_nil p))))))))))))))))))))
def c683 : List Lit := [(86, false), (87, false), (1436, true)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true :=
  Snake9.LocalRup.prove_clause [c232, c503, c502, c154, c177, c156] c683 (by decide) p (sat_cons (step232 p h) (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_cons (step154 p h) (sat_cons (step177 p h) (sat_cons (step156 p h) (sat_nil p)))))))
def c684 : List Lit := [(1483, false), (1497, true), (68, false)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true :=
  Snake9.LocalRup.prove_clause [c237, c594, c578, c581, c592, c193, c191, c587, c583] c684 (by decide) p (sat_cons (step237 p h) (sat_cons (step594 p h) (sat_cons (step578 p h) (sat_cons (step581 p h) (sat_cons (step592 p h) (sat_cons (step193 p h) (sat_cons (step191 p h) (sat_cons (step587 p h) (sat_cons (step583 p h) (sat_nil p))))))))))
def c685 : List Lit := [(1291, true), (1, false), (45, false)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true :=
  Snake9.LocalRup.prove_clause [c313, c314, c1] c685 (by decide) p (sat_cons (step313 p h) (sat_cons (step314 p h) (sat_cons (step1 p h) (sat_nil p))))
def c686 : List Lit := [(1468, true), (88, false), (89, false)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true :=
  Snake9.LocalRup.prove_clause [c235, c548, c549, c180, c176] c686 (by decide) p (sat_cons (step235 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step180 p h) (sat_cons (step176 p h) (sat_nil p))))))
def c687 : List Lit := [(80, true), (1479, true), (1470, false), (15, true), (89, false), (19, false), (86, true), (1436, true)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true :=
  Snake9.LocalRup.prove_clause [c232, c234, c208, c236, c540, c543, c567, c503, c502, c155, c686, c557, c558, c570, c544, c546, c542, c162, c173, c174, c28, c187, c161, c553, c186] c687 (by decide) p (sat_cons (step232 p h) (sat_cons (step234 p h) (sat_cons (step208 p h) (sat_cons (step236 p h) (sat_cons (step540 p h) (sat_cons (step543 p h) (sat_cons (step567 p h) (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_cons (step155 p h) (sat_cons (step686 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step570 p h) (sat_cons (step544 p h) (sat_cons (step546 p h) (sat_cons (step542 p h) (sat_cons (step162 p h) (sat_cons (step173 p h) (sat_cons (step174 p h) (sat_cons (step28 p h) (sat_cons (step187 p h) (sat_cons (step161 p h) (sat_cons (step553 p h) (sat_cons (step186 p h) (sat_nil p))))))))))))))))))))))))))
def c688 : List Lit := [(1466, true), (80, false), (15, true), (19, false), (1308, true), (86, true), (1436, true)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true :=
  Snake9.LocalRup.prove_clause [c208, c540, c503, c502, c544, c546, c542, c162, c159, c28, c333, c26] c688 (by decide) p (sat_cons (step208 p h) (sat_cons (step540 p h) (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_cons (step544 p h) (sat_cons (step546 p h) (sat_cons (step542 p h) (sat_cons (step162 p h) (sat_cons (step159 p h) (sat_cons (step28 p h) (sat_cons (step333 p h) (sat_cons (step26 p h) (sat_nil p)))))))))))))
def c689 : List Lit := [(1370, false), (1375, true), (1383, true)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true :=
  Snake9.LocalRup.prove_clause [c408, c413, c432, c672] c689 (by decide) p (sat_cons (step408 p h) (sat_cons (step413 p h) (sat_cons (step432 p h) (sat_cons (step672 p h) (sat_nil p)))))
def c690 : List Lit := [(2, false), (50, false), (44, false)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true :=
  Snake9.LocalRup.prove_clause [c201, c4, c58] c690 (by decide) p (sat_cons (step201 p h) (sat_cons (step4 p h) (sat_cons (step58 p h) (sat_nil p))))
def c691 : List Lit := [(1490, true), (101, false)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true :=
  Snake9.LocalRup.prove_clause [c238, c196, c584, c585, c200] c691 (by decide) p (sat_cons (step238 p h) (sat_cons (step196 p h) (sat_cons (step584 p h) (sat_cons (step585 p h) (sat_cons (step200 p h) (sat_nil p))))))
def c692 : List Lit := [(37, false), (40, false), (98, false)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true :=
  Snake9.LocalRup.prove_clause [c215, c41, c45] c692 (by decide) p (sat_cons (step215 p h) (sat_cons (step41 p h) (sat_cons (step45 p h) (sat_nil p))))
def c693 : List Lit := [(1423, true), (55, false), (71, false), (1416, false)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true :=
  Snake9.LocalRup.prove_clause [c470, c478, c481, c473, c461, c465, c104] c693 (by decide) p (sat_cons (step470 p h) (sat_cons (step478 p h) (sat_cons (step481 p h) (sat_cons (step473 p h) (sat_cons (step461 p h) (sat_cons (step465 p h) (sat_cons (step104 p h) (sat_nil p))))))))
def c694 : List Lit := [(1470, false), (81, true), (1473, true), (1478, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true :=
  Snake9.LocalRup.prove_clause [c554, c557, c569, c548, c549, c546, c681, c540] c694 (by decide) p (sat_cons (step554 p h) (sat_cons (step557 p h) (sat_cons (step569 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step546 p h) (sat_cons (step681 p h) (sat_cons (step540 p h) (sat_nil p)))))))))
def c695 : List Lit := [(81, true), (1473, true), (1478, true), (19, false)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true :=
  Snake9.LocalRup.prove_clause [c235, c694, c551, c552, c674, c164, c541, c546, c569, c556, c548, c179, c183] c695 (by decide) p (sat_cons (step235 p h) (sat_cons (step694 p h) (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step674 p h) (sat_cons (step164 p h) (sat_cons (step541 p h) (sat_cons (step546 p h) (sat_cons (step569 p h) (sat_cons (step556 p h) (sat_cons (step548 p h) (sat_cons (step179 p h) (sat_cons (step183 p h) (sat_nil p))))))))))))))
def c696 : List Lit := [(92, true), (81, false), (1473, true)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true :=
  Snake9.LocalRup.prove_clause [c235, c555, c552, c553, c557, c548, c179, c182] c696 (by decide) p (sat_cons (step235 p h) (sat_cons (step555 p h) (sat_cons (step552 p h) (sat_cons (step553 p h) (sat_cons (step557 p h) (sat_cons (step548 p h) (sat_cons (step179 p h) (sat_cons (step182 p h) (sat_nil p)))))))))
def c697 : List Lit := [(1473, true), (1478, true), (19, false)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true :=
  Snake9.LocalRup.prove_clause [c236, c695, c696, c163, c186, c674, c181, c557, c548] c697 (by decide) p (sat_cons (step236 p h) (sat_cons (step695 p h) (sat_cons (step696 p h) (sat_cons (step163 p h) (sat_cons (step186 p h) (sat_cons (step674 p h) (sat_cons (step181 p h) (sat_cons (step557 p h) (sat_cons (step548 p h) (sat_nil p))))))))))
def c698 : List Lit := [(79, false), (1467, true), (86, true), (104, false), (102, false)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true :=
  Snake9.LocalRup.prove_clause [c239, c195, c198, c169, c167, c542, c547] c698 (by decide) p (sat_cons (step239 p h) (sat_cons (step195 p h) (sat_cons (step198 p h) (sat_cons (step169 p h) (sat_cons (step167 p h) (sat_cons (step542 p h) (sat_cons (step547 p h) (sat_nil p))))))))
def c699 : List Lit := [(1362, true), (1365, false), (52, true), (1400, true), (1320, false)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true :=
  Snake9.LocalRup.prove_clause [c396, c402, c408, c665, c439, c389, c672, c386, c432, c433, c443, c409, c357, c403, c661, c398, c318, c690] c699 (by decide) p (sat_cons (step396 p h) (sat_cons (step402 p h) (sat_cons (step408 p h) (sat_cons (step665 p h) (sat_cons (step439 p h) (sat_cons (step389 p h) (sat_cons (step672 p h) (sat_cons (step386 p h) (sat_cons (step432 p h) (sat_cons (step433 p h) (sat_cons (step443 p h) (sat_cons (step409 p h) (sat_cons (step357 p h) (sat_cons (step403 p h) (sat_cons (step661 p h) (sat_cons (step398 p h) (sat_cons (step318 p h) (sat_cons (step690 p h) (sat_nil p)))))))))))))))))))
def c700 : List Lit := [(1329, true), (1309, false)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true :=
  Snake9.LocalRup.prove_clause [c642, c18, c348, c666, c357, c349, c661, c343, c316, c338, c314, c16] c700 (by decide) p (sat_cons (step642 p h) (sat_cons (step18 p h) (sat_cons (step348 p h) (sat_cons (step666 p h) (sat_cons (step357 p h) (sat_cons (step349 p h) (sat_cons (step661 p h) (sat_cons (step343 p h) (sat_cons (step316 p h) (sat_cons (step338 p h) (sat_cons (step314 p h) (sat_cons (step16 p h) (sat_nil p)))))))))))))
def c701 : List Lit := [(47, true), (1302, true), (1320, false), (1376, true), (1400, true)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true :=
  Snake9.LocalRup.prove_clause [c204, c202, c325, c659, c13, c661, c316, c313, c6, c396, c314, c393, c699, c414, c405, c403, c395, c398, c685, c67, c5] c701 (by decide) p (sat_cons (step204 p h) (sat_cons (step202 p h) (sat_cons (step325 p h) (sat_cons (step659 p h) (sat_cons (step13 p h) (sat_cons (step661 p h) (sat_cons (step316 p h) (sat_cons (step313 p h) (sat_cons (step6 p h) (sat_cons (step396 p h) (sat_cons (step314 p h) (sat_cons (step393 p h) (sat_cons (step699 p h) (sat_cons (step414 p h) (sat_cons (step405 p h) (sat_cons (step403 p h) (sat_cons (step395 p h) (sat_cons (step398 p h) (sat_cons (step685 p h) (sat_cons (step67 p h) (sat_cons (step5 p h) (sat_nil p))))))))))))))))))))))
def c702 : List Lit := [(1365, false), (1302, true), (1320, false), (1383, true), (1400, true)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true :=
  Snake9.LocalRup.prove_clause [c204, c213, c325, c659, c13, c661, c316, c313, c6, c396, c318, c423, c402, c699, c418, c689, c414, c390, c427, c403, c379, c398, c377, c690, c373, c388, c38, c39, c635] c702 (by decide) p (sat_cons (step204 p h) (sat_cons (step213 p h) (sat_cons (step325 p h) (sat_cons (step659 p h) (sat_cons (step13 p h) (sat_cons (step661 p h) (sat_cons (step316 p h) (sat_cons (step313 p h) (sat_cons (step6 p h) (sat_cons (step396 p h) (sat_cons (step318 p h) (sat_cons (step423 p h) (sat_cons (step402 p h) (sat_cons (step699 p h) (sat_cons (step418 p h) (sat_cons (step689 p h) (sat_cons (step414 p h) (sat_cons (step390 p h) (sat_cons (step427 p h) (sat_cons (step403 p h) (sat_cons (step379 p h) (sat_cons (step398 p h) (sat_cons (step377 p h) (sat_cons (step690 p h) (sat_cons (step373 p h) (sat_cons (step388 p h) (sat_cons (step38 p h) (sat_cons (step39 p h) (sat_cons (step635 p h) (sat_nil p))))))))))))))))))))))))))))))
def c703 : List Lit := [(1302, true), (1320, false), (1383, true), (1400, true)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true :=
  Snake9.LocalRup.prove_clause [c202, c423, c661, c316, c314, c701, c702, c394, c685, c66, c5] c703 (by decide) p (sat_cons (step202 p h) (sat_cons (step423 p h) (sat_cons (step661 p h) (sat_cons (step316 p h) (sat_cons (step314 p h) (sat_cons (step701 p h) (sat_cons (step702 p h) (sat_cons (step394 p h) (sat_cons (step685 p h) (sat_cons (step66 p h) (sat_cons (step5 p h) (sat_nil p))))))))))))
def c704 : List Lit := [(1291, true), (1365, true)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true :=
  Snake9.LocalRup.prove_clause [c202, c394, c393, c314, c685, c66, c5] c704 (by decide) p (sat_cons (step202 p h) (sat_cons (step394 p h) (sat_cons (step393 p h) (sat_cons (step314 p h) (sat_cons (step685 p h) (sat_cons (step66 p h) (sat_cons (step5 p h) (sat_nil p))))))))
def c705 : List Lit := [(1375, false), (1316, false), (1302, false), (1383, true), (1400, true)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true :=
  Snake9.LocalRup.prove_clause [c211, c422, c427, c446, c381, c358, c370, c349, c33, c34, c634, c334, c331] c705 (by decide) p (sat_cons (step211 p h) (sat_cons (step422 p h) (sat_cons (step427 p h) (sat_cons (step446 p h) (sat_cons (step381 p h) (sat_cons (step358 p h) (sat_cons (step370 p h) (sat_cons (step349 p h) (sat_cons (step33 p h) (sat_cons (step34 p h) (sat_cons (step634 p h) (sat_cons (step334 p h) (sat_cons (step331 p h) (sat_nil p))))))))))))))
end B112E166
