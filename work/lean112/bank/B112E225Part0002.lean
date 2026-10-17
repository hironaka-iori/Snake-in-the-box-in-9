import B112E225Part0001
namespace B112E225
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c645 : List Lit := [(1349, false), (83, false)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true :=
  Snake9.LocalRup.prove_clause [c601, c513, c639, c627, c561, c637, c509, c603, c643, c431, c446, c484, c505, c642, c636, c622, c306, c302, c301, c298, c644, c475, c473, c616, c455, c465, c131, c463, c453, c598, c408, c411, c415, c421, c501, c510, c142, c146, c392, c362, c382, c364, c377] c645 (by decide) p (sat_cons (step601 p h) (sat_cons (step513 p h) (sat_cons (step639 p h) (sat_cons (step627 p h) (sat_cons (step561 p h) (sat_cons (step637 p h) (sat_cons (step509 p h) (sat_cons (step603 p h) (sat_cons (step643 p h) (sat_cons (step431 p h) (sat_cons (step446 p h) (sat_cons (step484 p h) (sat_cons (step505 p h) (sat_cons (step642 p h) (sat_cons (step636 p h) (sat_cons (step622 p h) (sat_cons (step306 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_cons (step298 p h) (sat_cons (step644 p h) (sat_cons (step475 p h) (sat_cons (step473 p h) (sat_cons (step616 p h) (sat_cons (step455 p h) (sat_cons (step465 p h) (sat_cons (step131 p h) (sat_cons (step463 p h) (sat_cons (step453 p h) (sat_cons (step598 p h) (sat_cons (step408 p h) (sat_cons (step411 p h) (sat_cons (step415 p h) (sat_cons (step421 p h) (sat_cons (step501 p h) (sat_cons (step510 p h) (sat_cons (step142 p h) (sat_cons (step146 p h) (sat_cons (step392 p h) (sat_cons (step362 p h) (sat_cons (step382 p h) (sat_cons (step364 p h) (sat_cons (step377 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c646 : List Lit := [(1411, true), (96, true), (83, false)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true :=
  Snake9.LocalRup.prove_clause [c645, c401, c399, c642, c622, c306, c302, c301, c298, c475, c473, c455, c465, c453, c463, c142, c147] c646 (by decide) p (sat_cons (step645 p h) (sat_cons (step401 p h) (sat_cons (step399 p h) (sat_cons (step642 p h) (sat_cons (step622 p h) (sat_cons (step306 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_cons (step298 p h) (sat_cons (step475 p h) (sat_cons (step473 p h) (sat_cons (step455 p h) (sat_cons (step465 p h) (sat_cons (step453 p h) (sat_cons (step463 p h) (sat_cons (step142 p h) (sat_cons (step147 p h) (sat_nil p))))))))))))))))))
def c647 : List Lit := [(102, false), (40, false), (96, true), (83, false)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true :=
  Snake9.LocalRup.prove_clause [c513, c645, c401, c399, c637, c509, c641, c144, c145, c453, c463, c455, c465, c476] c647 (by decide) p (sat_cons (step513 p h) (sat_cons (step645 p h) (sat_cons (step401 p h) (sat_cons (step399 p h) (sat_cons (step637 p h) (sat_cons (step509 p h) (sat_cons (step641 p h) (sat_cons (step144 p h) (sat_cons (step145 p h) (sat_cons (step453 p h) (sat_cons (step463 p h) (sat_cons (step455 p h) (sat_cons (step465 p h) (sat_cons (step476 p h) (sat_nil p)))))))))))))))
def c648 : List Lit := [(1371, false), (96, true), (83, false)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true :=
  Snake9.LocalRup.prove_clause [c513, c639, c627, c561, c637, c509, c603, c643, c431, c446, c646, c485, c502, c419, c416, c412, c641, c622, c306, c302, c301, c298, c308, c293, c289, c499, c489, c498, c449, c510, c432, c392, c427, c382, c377, c364, c362, c647, c142, c463, c465, c476, c455, c453, c118, c75, c76, c410] c648 (by decide) p (sat_cons (step513 p h) (sat_cons (step639 p h) (sat_cons (step627 p h) (sat_cons (step561 p h) (sat_cons (step637 p h) (sat_cons (step509 p h) (sat_cons (step603 p h) (sat_cons (step643 p h) (sat_cons (step431 p h) (sat_cons (step446 p h) (sat_cons (step646 p h) (sat_cons (step485 p h) (sat_cons (step502 p h) (sat_cons (step419 p h) (sat_cons (step416 p h) (sat_cons (step412 p h) (sat_cons (step641 p h) (sat_cons (step622 p h) (sat_cons (step306 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_cons (step298 p h) (sat_cons (step308 p h) (sat_cons (step293 p h) (sat_cons (step289 p h) (sat_cons (step499 p h) (sat_cons (step489 p h) (sat_cons (step498 p h) (sat_cons (step449 p h) (sat_cons (step510 p h) (sat_cons (step432 p h) (sat_cons (step392 p h) (sat_cons (step427 p h) (sat_cons (step382 p h) (sat_cons (step377 p h) (sat_cons (step364 p h) (sat_cons (step362 p h) (sat_cons (step647 p h) (sat_cons (step142 p h) (sat_cons (step463 p h) (sat_cons (step465 p h) (sat_cons (step476 p h) (sat_cons (step455 p h) (sat_cons (step453 p h) (sat_cons (step118 p h) (sat_cons (step75 p h) (sat_cons (step76 p h) (sat_cons (step410 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c649 : List Lit := [(102, true), (96, true), (83, false)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true :=
  Snake9.LocalRup.prove_clause [c513, c648, c418, c415, c411, c409, c408, c413, c69, c637, c509, c641, c622, c306, c302, c301, c298, c308, c293, c289, c142, c118, c463, c453, c465, c455, c476] c649 (by decide) p (sat_cons (step513 p h) (sat_cons (step648 p h) (sat_cons (step418 p h) (sat_cons (step415 p h) (sat_cons (step411 p h) (sat_cons (step409 p h) (sat_cons (step408 p h) (sat_cons (step413 p h) (sat_cons (step69 p h) (sat_cons (step637 p h) (sat_cons (step509 p h) (sat_cons (step641 p h) (sat_cons (step622 p h) (sat_cons (step306 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_cons (step298 p h) (sat_cons (step308 p h) (sat_cons (step293 p h) (sat_cons (step289 p h) (sat_cons (step142 p h) (sat_cons (step118 p h) (sat_cons (step463 p h) (sat_cons (step453 p h) (sat_cons (step465 p h) (sat_cons (step455 p h) (sat_cons (step476 p h) (sat_nil p))))))))))))))))))))))))))))
def c650 : List Lit := [(96, true), (83, false)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true :=
  Snake9.LocalRup.prove_clause [c561, c627, c639, c513, c643, c431, c637, c509, c641, c603, c646, c648, c418, c415, c417, c411, c407, c408, c409, c596, c649, c647, c362, c364, c377, c382, c392, c510, c493, c489, c449, c447, c550, c440] c650 (by decide) p (sat_cons (step561 p h) (sat_cons (step627 p h) (sat_cons (step639 p h) (sat_cons (step513 p h) (sat_cons (step643 p h) (sat_cons (step431 p h) (sat_cons (step637 p h) (sat_cons (step509 p h) (sat_cons (step641 p h) (sat_cons (step603 p h) (sat_cons (step646 p h) (sat_cons (step648 p h) (sat_cons (step418 p h) (sat_cons (step415 p h) (sat_cons (step417 p h) (sat_cons (step411 p h) (sat_cons (step407 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step596 p h) (sat_cons (step649 p h) (sat_cons (step647 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step377 p h) (sat_cons (step382 p h) (sat_cons (step392 p h) (sat_cons (step510 p h) (sat_cons (step493 p h) (sat_cons (step489 p h) (sat_cons (step449 p h) (sat_cons (step447 p h) (sat_cons (step550 p h) (sat_cons (step440 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c651 : List Lit := [(102, false), (83, false)]
theorem step651 (p : Nat → Bool) (h : Constraints p) : clause p c651 = true :=
  Snake9.LocalRup.prove_clause [c513, c636, c650, c131, c645, c401, c399, c637, c509, c641, c642, c474, c622, c308, c292, c291, c290, c597, c460, c467, c468, c476, c463, c457, c147, c452] c651 (by decide) p (sat_cons (step513 p h) (sat_cons (step636 p h) (sat_cons (step650 p h) (sat_cons (step131 p h) (sat_cons (step645 p h) (sat_cons (step401 p h) (sat_cons (step399 p h) (sat_cons (step637 p h) (sat_cons (step509 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step474 p h) (sat_cons (step622 p h) (sat_cons (step308 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step290 p h) (sat_cons (step597 p h) (sat_cons (step460 p h) (sat_cons (step467 p h) (sat_cons (step468 p h) (sat_cons (step476 p h) (sat_cons (step463 p h) (sat_cons (step457 p h) (sat_cons (step147 p h) (sat_cons (step452 p h) (sat_nil p)))))))))))))))))))))))))))
def c652 : List Lit := [(83, false)]
theorem step652 (p : Nat → Bool) (h : Constraints p) : clause p c652 = true :=
  Snake9.LocalRup.prove_clause [c513, c622, c306, c302, c301, c298, c637, c509, c641, c642, c474, c650, c651, c142, c463, c468, c459, c460, c570] c652 (by decide) p (sat_cons (step513 p h) (sat_cons (step622 p h) (sat_cons (step306 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_cons (step298 p h) (sat_cons (step637 p h) (sat_cons (step509 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step474 p h) (sat_cons (step650 p h) (sat_cons (step651 p h) (sat_cons (step142 p h) (sat_cons (step463 p h) (sat_cons (step468 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step570 p h) (sat_nil p))))))))))))))))))))
def c653 : List Lit := [(1332, true)]
theorem step653 (p : Nat → Bool) (h : Constraints p) : clause p c653 = true :=
  Snake9.LocalRup.prove_clause [c639, c628, c391] c653 (by decide) p (sat_cons (step639 p h) (sat_cons (step628 p h) (sat_cons (step391 p h) (sat_nil p))))
def c654 : List Lit := [(1381, true)]
theorem step654 (p : Nat → Bool) (h : Constraints p) : clause p c654 = true :=
  Snake9.LocalRup.prove_clause [c652, c426] c654 (by decide) p (sat_cons (step652 p h) (sat_cons (step426 p h) (sat_nil p)))
def c655 : List Lit := [(1432, false)]
theorem step655 (p : Nat → Bool) (h : Constraints p) : clause p c655 = true :=
  Snake9.LocalRup.prove_clause [c653, c513, c509] c655 (by decide) p (sat_cons (step653 p h) (sat_cons (step513 p h) (sat_cons (step509 p h) (sat_nil p))))
def c656 : List Lit := [(1383, true)]
theorem step656 (p : Nat → Bool) (h : Constraints p) : clause p c656 = true :=
  Snake9.LocalRup.prove_clause [c654, c429] c656 (by decide) p (sat_cons (step654 p h) (sat_cons (step429 p h) (sat_nil p)))
def c657 : List Lit := [(1374, false)]
theorem step657 (p : Nat → Bool) (h : Constraints p) : clause p c657 = true :=
  Snake9.LocalRup.prove_clause [c655, c602, c507] c657 (by decide) p (sat_cons (step655 p h) (sat_cons (step602 p h) (sat_cons (step507 p h) (sat_nil p))))
def c658 : List Lit := [(1412, false)]
theorem step658 (p : Nat → Bool) (h : Constraints p) : clause p c658 = true :=
  Snake9.LocalRup.prove_clause [c655, c641] c658 (by decide) p (sat_cons (step655 p h) (sat_cons (step641 p h) (sat_nil p)))
def c659 : List Lit := [(1401, false)]
theorem step659 (p : Nat → Bool) (h : Constraints p) : clause p c659 = true :=
  Snake9.LocalRup.prove_clause [c658, c478] c659 (by decide) p (sat_cons (step658 p h) (sat_cons (step478 p h) (sat_nil p)))
def c660 : List Lit := [(96, false), (102, true), (91, true)]
theorem step660 (p : Nat → Bool) (h : Constraints p) : clause p c660 = true :=
  Snake9.LocalRup.prove_clause [c167, c652, c658, c526, c456, c474, c134, c129, c290, c291, c292, c309, c302, c301, c298, c142, c463, c468, c459, c460, c570] c660 (by decide) p (sat_cons (step167 p h) (sat_cons (step652 p h) (sat_cons (step658 p h) (sat_cons (step526 p h) (sat_cons (step456 p h) (sat_cons (step474 p h) (sat_cons (step134 p h) (sat_cons (step129 p h) (sat_cons (step290 p h) (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step309 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_cons (step298 p h) (sat_cons (step142 p h) (sat_cons (step463 p h) (sat_cons (step468 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step570 p h) (sat_nil p))))))))))))))))))))))
def c661 : List Lit := [(102, true), (91, true)]
theorem step661 (p : Nat → Bool) (h : Constraints p) : clause p c661 = true :=
  Snake9.LocalRup.prove_clause [c659, c658, c526, c164, c458, c660, c451, c453, c457, c476, c465, c463, c142, c298, c301, c302, c309, c293, c289, c118, c117, c515, c122] c661 (by decide) p (sat_cons (step659 p h) (sat_cons (step658 p h) (sat_cons (step526 p h) (sat_cons (step164 p h) (sat_cons (step458 p h) (sat_cons (step660 p h) (sat_cons (step451 p h) (sat_cons (step453 p h) (sat_cons (step457 p h) (sat_cons (step476 p h) (sat_cons (step465 p h) (sat_cons (step463 p h) (sat_cons (step142 p h) (sat_cons (step298 p h) (sat_cons (step301 p h) (sat_cons (step302 p h) (sat_cons (step309 p h) (sat_cons (step293 p h) (sat_cons (step289 p h) (sat_cons (step118 p h) (sat_cons (step117 p h) (sat_cons (step515 p h) (sat_cons (step122 p h) (sat_nil p))))))))))))))))))))))))
def c662 : List Lit := [(96, true), (91, true)]
theorem step662 (p : Nat → Bool) (h : Constraints p) : clause p c662 = true :=
  Snake9.LocalRup.prove_clause [c659, c547, c658, c561, c627, c639, c513, c661, c456, c616, c481, c458, c451, c623, c453, c457, c399, c476, c401, c465, c420, c463, c146, c362, c364, c377, c382, c392, c510, c501, c498, c421, c485, c415, c571] c662 (by decide) p (sat_cons (step659 p h) (sat_cons (step547 p h) (sat_cons (step658 p h) (sat_cons (step561 p h) (sat_cons (step627 p h) (sat_cons (step639 p h) (sat_cons (step513 p h) (sat_cons (step661 p h) (sat_cons (step456 p h) (sat_cons (step616 p h) (sat_cons (step481 p h) (sat_cons (step458 p h) (sat_cons (step451 p h) (sat_cons (step623 p h) (sat_cons (step453 p h) (sat_cons (step457 p h) (sat_cons (step399 p h) (sat_cons (step476 p h) (sat_cons (step401 p h) (sat_cons (step465 p h) (sat_cons (step420 p h) (sat_cons (step463 p h) (sat_cons (step146 p h) (sat_cons (step362 p h) (sat_cons (step364 p h) (sat_cons (step377 p h) (sat_cons (step382 p h) (sat_cons (step392 p h) (sat_cons (step510 p h) (sat_cons (step501 p h) (sat_cons (step498 p h) (sat_cons (step421 p h) (sat_cons (step485 p h) (sat_cons (step415 p h) (sat_cons (step571 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c663 : List Lit := [(1350, false), (1411, false)]
theorem step663 (p : Nat → Bool) (h : Constraints p) : clause p c663 = true :=
  Snake9.LocalRup.prove_clause [c547, c655, c481, c505, c423, c424, c502, c415, c485, c571] c663 (by decide) p (sat_cons (step547 p h) (sat_cons (step655 p h) (sat_cons (step481 p h) (sat_cons (step505 p h) (sat_cons (step423 p h) (sat_cons (step424 p h) (sat_cons (step502 p h) (sat_cons (step415 p h) (sat_cons (step485 p h) (sat_cons (step571 p h) (sat_nil p)))))))))))
def c664 : List Lit := [(91, true)]
theorem step664 (p : Nat → Bool) (h : Constraints p) : clause p c664 = true :=
  Snake9.LocalRup.prove_clause [c652, c167, c658, c513, c639, c627, c520, c323, c517, c156, c456, c134, c616, c474, c567, c511, c393, c383, c661, c662, c129, c290, c291, c292, c308, c310, c315, c318, c321, c268, c229, c243, c244, c225, c241, c236, c222, c224, c240, c235, c219, c211, c239, c48, c214, c215, c210, c47, c213, c209, c663, c569, c619, c468, c459, c460, c570] c664 (by decide) p (sat_cons (step652 p h) (sat_cons (step167 p h) (sat_cons (step658 p h) (sat_cons (step513 p h) (sat_cons (step639 p h) (sat_cons (step627 p h) (sat_cons (step520 p h) (sat_cons (step323 p h) (sat_cons (step517 p h) (sat_cons (step156 p h) (sat_cons (step456 p h) (sat_cons (step134 p h) (sat_cons (step616 p h) (sat_cons (step474 p h) (sat_cons (step567 p h) (sat_cons (step511 p h) (sat_cons (step393 p h) (sat_cons (step383 p h) (sat_cons (step661 p h) (sat_cons (step662 p h) (sat_cons (step129 p h) (sat_cons (step290 p h) (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step308 p h) (sat_cons (step310 p h) (sat_cons (step315 p h) (sat_cons (step318 p h) (sat_cons (step321 p h) (sat_cons (step268 p h) (sat_cons (step229 p h) (sat_cons (step243 p h) (sat_cons (step244 p h) (sat_cons (step225 p h) (sat_cons (step241 p h) (sat_cons (step236 p h) (sat_cons (step222 p h) (sat_cons (step224 p h) (sat_cons (step240 p h) (sat_cons (step235 p h) (sat_cons (step219 p h) (sat_cons (step211 p h) (sat_cons (step239 p h) (sat_cons (step48 p h) (sat_cons (step214 p h) (sat_cons (step215 p h) (sat_cons (step210 p h) (sat_cons (step47 p h) (sat_cons (step213 p h) (sat_cons (step209 p h) (sat_cons (step663 p h) (sat_cons (step569 p h) (sat_cons (step619 p h) (sat_cons (step468 p h) (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step570 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c665 : List Lit := [(1402, true), (96, false)]
theorem step665 (p : Nat → Bool) (h : Constraints p) : clause p c665 = true :=
  Snake9.LocalRup.prove_clause [c459, c460, c570] c665 (by decide) p (sat_cons (step459 p h) (sat_cons (step460 p h) (sat_cons (step570 p h) (sat_nil p))))
def c666 : List Lit := [(1393, true), (1362, true)]
theorem step666 (p : Nat → Bool) (h : Constraints p) : clause p c666 = true :=
  Snake9.LocalRup.prove_clause [c656, c654, c411, c409, c408, c413, c450, c447, c574, c438, c449, c430, c432, c550, c575, c440] c666 (by decide) p (sat_cons (step656 p h) (sat_cons (step654 p h) (sat_cons (step411 p h) (sat_cons (step409 p h) (sat_cons (step408 p h) (sat_cons (step413 p h) (sat_cons (step450 p h) (sat_cons (step447 p h) (sat_cons (step574 p h) (sat_cons (step438 p h) (sat_cons (step449 p h) (sat_cons (step430 p h) (sat_cons (step432 p h) (sat_cons (step550 p h) (sat_cons (step575 p h) (sat_cons (step440 p h) (sat_nil p)))))))))))))))))
def c667 : List Lit := [(102, false), (1407, true), (40, false), (59, false)]
theorem step667 (p : Nat → Bool) (h : Constraints p) : clause p c667 = true :=
  Snake9.LocalRup.prove_clause [c658, c144, c145, c463, c465, c468, c476, c665, c455, c453] c667 (by decide) p (sat_cons (step658 p h) (sat_cons (step144 p h) (sat_cons (step145 p h) (sat_cons (step463 p h) (sat_cons (step465 p h) (sat_cons (step468 p h) (sat_cons (step476 p h) (sat_cons (step665 p h) (sat_cons (step455 p h) (sat_cons (step453 p h) (sat_nil p)))))))))))
def c668 : List Lit := [(102, true), (1421, false), (59, false)]
theorem step668 (p : Nat → Bool) (h : Constraints p) : clause p c668 = true :=
  Snake9.LocalRup.prove_clause [c655, c513, c639, c627, c561, c529, c323, c155, c493, c510, c392, c382, c377, c364, c362, c366, c499, c420, c403, c397, c51, c238, c242, c243, c245, c268, c237, c317, c234, c321, c44, c229, c46, c225, c30, c224, c29, c212, c207, c208] c668 (by decide) p (sat_cons (step655 p h) (sat_cons (step513 p h) (sat_cons (step639 p h) (sat_cons (step627 p h) (sat_cons (step561 p h) (sat_cons (step529 p h) (sat_cons (step323 p h) (sat_cons (step155 p h) (sat_cons (step493 p h) (sat_cons (step510 p h) (sat_cons (step392 p h) (sat_cons (step382 p h) (sat_cons (step377 p h) (sat_cons (step364 p h) (sat_cons (step362 p h) (sat_cons (step366 p h) (sat_cons (step499 p h) (sat_cons (step420 p h) (sat_cons (step403 p h) (sat_cons (step397 p h) (sat_cons (step51 p h) (sat_cons (step238 p h) (sat_cons (step242 p h) (sat_cons (step243 p h) (sat_cons (step245 p h) (sat_cons (step268 p h) (sat_cons (step237 p h) (sat_cons (step317 p h) (sat_cons (step234 p h) (sat_cons (step321 p h) (sat_cons (step44 p h) (sat_cons (step229 p h) (sat_cons (step46 p h) (sat_cons (step225 p h) (sat_cons (step30 p h) (sat_cons (step224 p h) (sat_cons (step29 p h) (sat_cons (step212 p h) (sat_cons (step207 p h) (sat_cons (step208 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c669 : List Lit := [(40, false), (102, false), (59, false)]
theorem step669 (p : Nat → Bool) (h : Constraints p) : clause p c669 = true :=
  Snake9.LocalRup.prove_clause [c658, c144, c667, c452, c474, c454] c669 (by decide) p (sat_cons (step658 p h) (sat_cons (step144 p h) (sat_cons (step667 p h) (sat_cons (step452 p h) (sat_cons (step474 p h) (sat_cons (step454 p h) (sat_nil p)))))))
def c670 : List Lit := [(1421, false), (59, false)]
theorem step670 (p : Nat → Bool) (h : Constraints p) : clause p c670 = true :=
  Snake9.LocalRup.prove_clause [c513, c639, c627, c561, c493, c510, c392, c382, c377, c364, c362, c668, c669] c670 (by decide) p (sat_cons (step513 p h) (sat_cons (step639 p h) (sat_cons (step627 p h) (sat_cons (step561 p h) (sat_cons (step493 p h) (sat_cons (step510 p h) (sat_cons (step392 p h) (sat_cons (step382 p h) (sat_cons (step377 p h) (sat_cons (step364 p h) (sat_cons (step362 p h) (sat_cons (step668 p h) (sat_cons (step669 p h) (sat_nil p))))))))))))))
def c671 : List Lit := [(1431, true), (1371, false), (1411, false)]
theorem step671 (p : Nat → Bool) (h : Constraints p) : clause p c671 = true :=
  Snake9.LocalRup.prove_clause [c547, c656, c481, c501, c498, c419, c485, c416, c446, c412, c437, c580, c414, c408, c409, c582] c671 (by decide) p (sat_cons (step547 p h) (sat_cons (step656 p h) (sat_cons (step481 p h) (sat_cons (step501 p h) (sat_cons (step498 p h) (sat_cons (step419 p h) (sat_cons (step485 p h) (sat_cons (step416 p h) (sat_cons (step446 p h) (sat_cons (step412 p h) (sat_cons (step437 p h) (sat_cons (step580 p h) (sat_cons (step414 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step582 p h) (sat_nil p)))))))))))))))))
def c672 : List Lit := [(1301, true), (59, false)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true :=
  Snake9.LocalRup.prove_clause [c323, c154, c364, c366, c362, c669, c51, c238, c242, c243, c268, c317, c321, c229, c225, c224, c212, c208, c207, c29, c28, c30, c34] c672 (by decide) p (sat_cons (step323 p h) (sat_cons (step154 p h) (sat_cons (step364 p h) (sat_cons (step366 p h) (sat_cons (step362 p h) (sat_cons (step669 p h) (sat_cons (step51 p h) (sat_cons (step238 p h) (sat_cons (step242 p h) (sat_cons (step243 p h) (sat_cons (step268 p h) (sat_cons (step317 p h) (sat_cons (step321 p h) (sat_cons (step229 p h) (sat_cons (step225 p h) (sat_cons (step224 p h) (sat_cons (step212 p h) (sat_cons (step208 p h) (sat_cons (step207 p h) (sat_cons (step29 p h) (sat_cons (step28 p h) (sat_cons (step30 p h) (sat_cons (step34 p h) (sat_nil p))))))))))))))))))))))))
def c673 : List Lit := [(1411, false), (59, false)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true :=
  Snake9.LocalRup.prove_clause [c561, c627, c639, c513, c672, c377, c382, c392, c510, c670, c489, c671, c666, c418, c415] c673 (by decide) p (sat_cons (step561 p h) (sat_cons (step627 p h) (sat_cons (step639 p h) (sat_cons (step513 p h) (sat_cons (step672 p h) (sat_cons (step377 p h) (sat_cons (step382 p h) (sat_cons (step392 p h) (sat_cons (step510 p h) (sat_cons (step670 p h) (sat_cons (step489 p h) (sat_cons (step671 p h) (sat_cons (step666 p h) (sat_cons (step418 p h) (sat_cons (step415 p h) (sat_nil p))))))))))))))))
def c674 : List Lit := [(1404, false), (1411, true)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true :=
  Snake9.LocalRup.prove_clause [c471, c465, c468, c473, c665, c454, c451] c674 (by decide) p (sat_cons (step471 p h) (sat_cons (step465 p h) (sat_cons (step468 p h) (sat_cons (step473 p h) (sat_cons (step665 p h) (sat_cons (step454 p h) (sat_cons (step451 p h) (sat_nil p))))))))
def c675 : List Lit := [(96, true), (59, false)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true :=
  Snake9.LocalRup.prove_clause [c652, c167, c664, c518, c522, c673, c674, c463, c475, c455, c133, c453, c115, c147, c278, c142, c279, c298, c281, c301, c285, c302, c313, c306] c675 (by decide) p (sat_cons (step652 p h) (sat_cons (step167 p h) (sat_cons (step664 p h) (sat_cons (step518 p h) (sat_cons (step522 p h) (sat_cons (step673 p h) (sat_cons (step674 p h) (sat_cons (step463 p h) (sat_cons (step475 p h) (sat_cons (step455 p h) (sat_cons (step133 p h) (sat_cons (step453 p h) (sat_cons (step115 p h) (sat_cons (step147 p h) (sat_cons (step278 p h) (sat_cons (step142 p h) (sat_cons (step279 p h) (sat_cons (step298 p h) (sat_cons (step281 p h) (sat_cons (step301 p h) (sat_cons (step285 p h) (sat_cons (step302 p h) (sat_cons (step313 p h) (sat_cons (step306 p h) (sat_nil p)))))))))))))))))))))))))
def c676 : List Lit := [(92, false), (59, false), (101, false)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true :=
  Snake9.LocalRup.prove_clause [c520, c147, c51, c142, c238, c298, c242, c301, c243, c302, c268, c306, c318, c310] c676 (by decide) p (sat_cons (step520 p h) (sat_cons (step147 p h) (sat_cons (step51 p h) (sat_cons (step142 p h) (sat_cons (step238 p h) (sat_cons (step298 p h) (sat_cons (step242 p h) (sat_cons (step301 p h) (sat_cons (step243 p h) (sat_cons (step302 p h) (sat_cons (step268 p h) (sat_cons (step306 p h) (sat_cons (step318 p h) (sat_cons (step310 p h) (sat_nil p)))))))))))))))
def c677 : List Lit := [(59, false)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true :=
  Snake9.LocalRup.prove_clause [c673, c674, c463, c675, c665, c467, c473, c454, c452, c676] c677 (by decide) p (sat_cons (step673 p h) (sat_cons (step674 p h) (sat_cons (step463 p h) (sat_cons (step675 p h) (sat_cons (step665 p h) (sat_cons (step467 p h) (sat_cons (step473 p h) (sat_cons (step454 p h) (sat_cons (step452 p h) (sat_cons (step676 p h) (sat_nil p)))))))))))
def c678 : List Lit := [(1346, true)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true :=
  Snake9.LocalRup.prove_clause [c677, c399] c678 (by decide) p (sat_cons (step677 p h) (sat_cons (step399 p h) (sat_nil p)))
def c679 : List Lit := [(1349, true)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true :=
  Snake9.LocalRup.prove_clause [c678, c401] c679 (by decide) p (sat_cons (step678 p h) (sat_cons (step401 p h) (sat_nil p)))
def c680 : List Lit := [(1371, true)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true :=
  Snake9.LocalRup.prove_clause [c679, c420] c680 (by decide) p (sat_cons (step679 p h) (sat_cons (step420 p h) (sat_nil p)))
def c681 : List Lit := [(1421, false)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true :=
  Snake9.LocalRup.prove_clause [c680, c655, c499] c681 (by decide) p (sat_cons (step680 p h) (sat_cons (step655 p h) (sat_cons (step499 p h) (sat_nil p))))
def c682 : List Lit := [(403, false), (92, false), (102, true)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true :=
  Snake9.LocalRup.prove_clause [c526, c520, c517, c156, c677, c657, c655, c601, c306, c309, c310, c293, c318, c289, c268, c118, c117, c243, c244, c515, c241, c236, c408, c240, c235, c411, c239, c48, c415, c47, c569, c424, c425, c505, c416, c484, c412, c414, c580] c682 (by decide) p (sat_cons (step526 p h) (sat_cons (step520 p h) (sat_cons (step517 p h) (sat_cons (step156 p h) (sat_cons (step677 p h) (sat_cons (step657 p h) (sat_cons (step655 p h) (sat_cons (step601 p h) (sat_cons (step306 p h) (sat_cons (step309 p h) (sat_cons (step310 p h) (sat_cons (step293 p h) (sat_cons (step318 p h) (sat_cons (step289 p h) (sat_cons (step268 p h) (sat_cons (step118 p h) (sat_cons (step117 p h) (sat_cons (step243 p h) (sat_cons (step244 p h) (sat_cons (step515 p h) (sat_cons (step241 p h) (sat_cons (step236 p h) (sat_cons (step408 p h) (sat_cons (step240 p h) (sat_cons (step235 p h) (sat_cons (step411 p h) (sat_cons (step239 p h) (sat_cons (step48 p h) (sat_cons (step415 p h) (sat_cons (step47 p h) (sat_cons (step569 p h) (sat_cons (step424 p h) (sat_cons (step425 p h) (sat_cons (step505 p h) (sat_cons (step416 p h) (sat_cons (step484 p h) (sat_cons (step412 p h) (sat_cons (step414 p h) (sat_cons (step580 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c683 : List Lit := [(1411, false)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true :=
  Snake9.LocalRup.prove_clause [c547, c681, c679, c655, c656, c481, c489, c505, c666, c422, c415, c416, c421, c412, c502, c485, c446, c580, c437, c414, c408, c409, c582] c683 (by decide) p (sat_cons (step547 p h) (sat_cons (step681 p h) (sat_cons (step679 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step481 p h) (sat_cons (step489 p h) (sat_cons (step505 p h) (sat_cons (step666 p h) (sat_cons (step422 p h) (sat_cons (step415 p h) (sat_cons (step416 p h) (sat_cons (step421 p h) (sat_cons (step412 p h) (sat_cons (step502 p h) (sat_cons (step485 p h) (sat_cons (step446 p h) (sat_cons (step580 p h) (sat_cons (step437 p h) (sat_cons (step414 p h) (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step582 p h) (sat_nil p))))))))))))))))))))))))
def c684 : List Lit := [(1400, false)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true :=
  Snake9.LocalRup.prove_clause [c683, c475] c684 (by decide) p (sat_cons (step683 p h) (sat_cons (step475 p h) (sat_nil p)))
def c685 : List Lit := [(1404, false)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true :=
  Snake9.LocalRup.prove_clause [c683, c674] c685 (by decide) p (sat_cons (step683 p h) (sat_cons (step674 p h) (sat_nil p)))
def c686 : List Lit := [(1398, false)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true :=
  Snake9.LocalRup.prove_clause [c684, c455] c686 (by decide) p (sat_cons (step684 p h) (sat_cons (step455 p h) (sat_nil p)))
def c687 : List Lit := [(101, true)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true :=
  Snake9.LocalRup.prove_clause [c685, c463] c687 (by decide) p (sat_cons (step685 p h) (sat_cons (step463 p h) (sat_nil p)))
def c688 : List Lit := [(92, true)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true :=
  Snake9.LocalRup.prove_clause [c686, c683, c452, c453, c454, c665, c473, c467] c688 (by decide) p (sat_cons (step686 p h) (sat_cons (step683 p h) (sat_cons (step452 p h) (sat_cons (step453 p h) (sat_cons (step454 p h) (sat_cons (step665 p h) (sat_cons (step473 p h) (sat_cons (step467 p h) (sat_nil p)))))))))
def c689 : List Lit := [(102, true)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true :=
  Snake9.LocalRup.prove_clause [c687, c688, c142, c682, c298, c302, c301] c689 (by decide) p (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step142 p h) (sat_cons (step682 p h) (sat_cons (step298 p h) (sat_cons (step302 p h) (sat_cons (step301 p h) (sat_nil p))))))))
def c690 : List Lit := [(40, false)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true :=
  Snake9.LocalRup.prove_clause [c689, c687, c688, c146] c690 (by decide) p (sat_cons (step689 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step146 p h) (sat_nil p)))))
def c691 : List Lit := [(1299, true)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true :=
  Snake9.LocalRup.prove_clause [c690, c362] c691 (by decide) p (sat_cons (step690 p h) (sat_cons (step362 p h) (sat_nil p)))
def c692 : List Lit := [(1301, true)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true :=
  Snake9.LocalRup.prove_clause [c691, c364] c692 (by decide) p (sat_cons (step691 p h) (sat_cons (step364 p h) (sat_nil p)))
def c693 : List Lit := [(1313, true)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true :=
  Snake9.LocalRup.prove_clause [c692, c561, c377] c693 (by decide) p (sat_cons (step692 p h) (sat_cons (step561 p h) (sat_cons (step377 p h) (sat_nil p))))
def c694 : List Lit := [(1321, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true :=
  Snake9.LocalRup.prove_clause [c693, c627, c382] c694 (by decide) p (sat_cons (step693 p h) (sat_cons (step627 p h) (sat_cons (step382 p h) (sat_nil p))))
def c695 : List Lit := [(1333, true)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true :=
  Snake9.LocalRup.prove_clause [c694, c639, c392] c695 (by decide) p (sat_cons (step694 p h) (sat_cons (step639 p h) (sat_cons (step392 p h) (sat_nil p))))
def c696 : List Lit := [(1431, false)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true :=
  Snake9.LocalRup.prove_clause [c695, c513, c510] c696 (by decide) p (sat_cons (step695 p h) (sat_cons (step513 p h) (sat_cons (step510 p h) (sat_nil p))))
def c697 : List Lit := [(1373, false)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true :=
  Snake9.LocalRup.prove_clause [c696, c602, c504] c697 (by decide) p (sat_cons (step696 p h) (sat_cons (step602 p h) (sat_cons (step504 p h) (sat_nil p))))
def c698 : List Lit := [(1420, false)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true :=
  Snake9.LocalRup.prove_clause [c696, c680, c498] c698 (by decide) p (sat_cons (step696 p h) (sat_cons (step680 p h) (sat_cons (step498 p h) (sat_nil p))))
def c699 : List Lit := [(1366, false)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true :=
  Snake9.LocalRup.prove_clause [c697, c679, c422] c699 (by decide) p (sat_cons (step697 p h) (sat_cons (step679 p h) (sat_cons (step422 p h) (sat_nil p))))
def c700 : List Lit := [(76, false)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true :=
  Snake9.LocalRup.prove_clause [c697, c688, c664, c687, c598] c700 (by decide) p (sat_cons (step697 p h) (sat_cons (step688 p h) (sat_cons (step664 p h) (sat_cons (step687 p h) (sat_cons (step598 p h) (sat_nil p))))))
def c701 : List Lit := [(1393, false)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true :=
  Snake9.LocalRup.prove_clause [c698, c601, c488] c701 (by decide) p (sat_cons (step698 p h) (sat_cons (step601 p h) (sat_cons (step488 p h) (sat_nil p))))
def c702 : List Lit := [(1363, false)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true :=
  Snake9.LocalRup.prove_clause [c699, c416] c702 (by decide) p (sat_cons (step699 p h) (sat_cons (step416 p h) (sat_nil p)))
def c703 : List Lit := [(1360, true)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true :=
  Snake9.LocalRup.prove_clause [c700, c408] c703 (by decide) p (sat_cons (step700 p h) (sat_cons (step408 p h) (sat_nil p)))
def c704 : List Lit := [(1362, true)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true :=
  Snake9.LocalRup.prove_clause [c701, c666] c704 (by decide) p (sat_cons (step701 p h) (sat_cons (step666 p h) (sat_nil p)))
def c705 : List Lit := [(1361, false)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true :=
  Snake9.LocalRup.prove_clause [c702, c412] c705 (by decide) p (sat_cons (step702 p h) (sat_cons (step412 p h) (sat_nil p)))
def c706 : List Lit := [(73, true)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true :=
  Snake9.LocalRup.prove_clause [c703, c702, c414] c706 (by decide) p (sat_cons (step703 p h) (sat_cons (step702 p h) (sat_cons (step414 p h) (sat_nil p))))
def c707 : List Lit := [(1365, true)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true :=
  Snake9.LocalRup.prove_clause [c704, c415] c707 (by decide) p (sat_cons (step704 p h) (sat_cons (step415 p h) (sat_nil p)))
def c708 : List Lit := [(1392, true)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true :=
  Snake9.LocalRup.prove_clause [c706, c705, c580] c708 (by decide) p (sat_cons (step706 p h) (sat_cons (step705 p h) (sat_cons (step580 p h) (sat_nil p))))
end B112E225
