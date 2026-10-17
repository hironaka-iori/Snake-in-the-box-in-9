import B112E154Part0001
namespace B112E154
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c578 : List Lit := [(78, false)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true :=
  Snake9.LocalRup.prove_clause [c576, c573, c574, c96] c578 (by decide) p (sat_cons (step576 p h) (sat_cons (step573 p h) (sat_cons (step574 p h) (sat_cons (step96 p h) (sat_nil p)))))
def c579 : List Lit := [(1320, true)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true :=
  Snake9.LocalRup.prove_clause [c578, c379] c579 (by decide) p (sat_cons (step578 p h) (sat_cons (step379 p h) (sat_nil p)))
def c580 : List Lit := [(1322, true)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true :=
  Snake9.LocalRup.prove_clause [c579, c381] c580 (by decide) p (sat_cons (step579 p h) (sat_cons (step381 p h) (sat_nil p)))
def c581 : List Lit := [(1331, true)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true :=
  Snake9.LocalRup.prove_clause [c580, c578, c573, c392, c391, c382, c388, c380, c538] c581 (by decide) p (sat_cons (step580 p h) (sat_cons (step578 p h) (sat_cons (step573 p h) (sat_cons (step392 p h) (sat_cons (step391 p h) (sat_cons (step382 p h) (sat_cons (step388 p h) (sat_cons (step380 p h) (sat_cons (step538 p h) (sat_nil p))))))))))
def c582 : List Lit := [(1358, true)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true :=
  Snake9.LocalRup.prove_clause [c581, c502, c421] c582 (by decide) p (sat_cons (step581 p h) (sat_cons (step502 p h) (sat_cons (step421 p h) (sat_nil p))))
def c583 : List Lit := [(1351, false)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true :=
  Snake9.LocalRup.prove_clause [c581, c492, c423] c583 (by decide) p (sat_cons (step581 p h) (sat_cons (step492 p h) (sat_cons (step423 p h) (sat_nil p))))
def c584 : List Lit := [(1369, true)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true :=
  Snake9.LocalRup.prove_clause [c582, c481] c584 (by decide) p (sat_cons (step582 p h) (sat_cons (step481 p h) (sat_nil p)))
def c585 : List Lit := [(97, true)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true :=
  Snake9.LocalRup.prove_clause [c583, c504] c585 (by decide) p (sat_cons (step583 p h) (sat_cons (step504 p h) (sat_nil p)))
def c586 : List Lit := [(1273, false)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true :=
  Snake9.LocalRup.prove_clause [c584, c445, c442] c586 (by decide) p (sat_cons (step584 p h) (sat_cons (step445 p h) (sat_cons (step442 p h) (sat_nil p))))
def c587 : List Lit := [(1338, true)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true :=
  Snake9.LocalRup.prove_clause [c585, c505] c587 (by decide) p (sat_cons (step585 p h) (sat_cons (step505 p h) (sat_nil p)))
def c588 : List Lit := [(1262, false)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true :=
  Snake9.LocalRup.prove_clause [c586, c484, c337] c588 (by decide) p (sat_cons (step586 p h) (sat_cons (step484 p h) (sat_cons (step337 p h) (sat_nil p))))
def c589 : List Lit := [(1346, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true :=
  Snake9.LocalRup.prove_clause [c587, c583, c411] c589 (by decide) p (sat_cons (step587 p h) (sat_cons (step583 p h) (sat_cons (step411 p h) (sat_nil p))))
def c590 : List Lit := [(1311, true), (1252, false)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true :=
  Snake9.LocalRup.prove_clause [c588, c541, c484, c445, c158, c576, c573, c502, c167, c578, c166, c332, c290, c287, c371, c485, c476, c354, c327, c348, c474, c336, c347, c441, c80, c482, c95, c424, c111, c388, c393, c382, c380, c110, c35, c36, c283] c590 (by decide) p (sat_cons (step588 p h) (sat_cons (step541 p h) (sat_cons (step484 p h) (sat_cons (step445 p h) (sat_cons (step158 p h) (sat_cons (step576 p h) (sat_cons (step573 p h) (sat_cons (step502 p h) (sat_cons (step167 p h) (sat_cons (step578 p h) (sat_cons (step166 p h) (sat_cons (step332 p h) (sat_cons (step290 p h) (sat_cons (step287 p h) (sat_cons (step371 p h) (sat_cons (step485 p h) (sat_cons (step476 p h) (sat_cons (step354 p h) (sat_cons (step327 p h) (sat_cons (step348 p h) (sat_cons (step474 p h) (sat_cons (step336 p h) (sat_cons (step347 p h) (sat_cons (step441 p h) (sat_cons (step80 p h) (sat_cons (step482 p h) (sat_cons (step95 p h) (sat_cons (step424 p h) (sat_cons (step111 p h) (sat_cons (step388 p h) (sat_cons (step393 p h) (sat_cons (step382 p h) (sat_cons (step380 p h) (sat_cons (step110 p h) (sat_cons (step35 p h) (sat_cons (step36 p h) (sat_cons (step283 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c591 : List Lit := [(1233, true)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true :=
  Snake9.LocalRup.prove_clause [c515, c541, c144, c289, c292, c286, c277, c279, c281, c282, c275, c28, c7, c9] c591 (by decide) p (sat_cons (step515 p h) (sat_cons (step541 p h) (sat_cons (step144 p h) (sat_cons (step289 p h) (sat_cons (step292 p h) (sat_cons (step286 p h) (sat_cons (step277 p h) (sat_cons (step279 p h) (sat_cons (step281 p h) (sat_cons (step282 p h) (sat_cons (step275 p h) (sat_cons (step28 p h) (sat_cons (step7 p h) (sat_cons (step9 p h) (sat_nil p)))))))))))))))
def c592 : List Lit := [(1252, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true :=
  Snake9.LocalRup.prove_clause [c591, c582, c484, c445, c590, c327, c431, c336, c441] c592 (by decide) p (sat_cons (step591 p h) (sat_cons (step582 p h) (sat_cons (step484 p h) (sat_cons (step445 p h) (sat_cons (step590 p h) (sat_cons (step327 p h) (sat_cons (step431 p h) (sat_cons (step336 p h) (sat_cons (step441 p h) (sat_nil p))))))))))
def c593 : List Lit := [(1248, false)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true :=
  Snake9.LocalRup.prove_clause [c592, c315] c593 (by decide) p (sat_cons (step592 p h) (sat_cons (step315 p h) (sat_nil p)))
def c594 : List Lit := [(1245, false)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true :=
  Snake9.LocalRup.prove_clause [c593, c464] c594 (by decide) p (sat_cons (step593 p h) (sat_cons (step464 p h) (sat_nil p)))
def c595 : List Lit := [(1244, false)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true :=
  Snake9.LocalRup.prove_clause [c593, c312] c595 (by decide) p (sat_cons (step593 p h) (sat_cons (step312 p h) (sat_nil p)))
def c596 : List Lit := [(50, true)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true :=
  Snake9.LocalRup.prove_clause [c594, c306] c596 (by decide) p (sat_cons (step594 p h) (sat_cons (step306 p h) (sat_nil p)))
def c597 : List Lit := [(47, true)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true :=
  Snake9.LocalRup.prove_clause [c594, c307] c597 (by decide) p (sat_cons (step594 p h) (sat_cons (step307 p h) (sat_nil p)))
def c598 : List Lit := [(46, true)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true :=
  Snake9.LocalRup.prove_clause [c595, c462] c598 (by decide) p (sat_cons (step595 p h) (sat_cons (step462 p h) (sat_nil p)))
def c599 : List Lit := [(49, true)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true :=
  Snake9.LocalRup.prove_clause [c597, c152, c64] c599 (by decide) p (sat_cons (step597 p h) (sat_cons (step152 p h) (sat_cons (step64 p h) (sat_nil p))))
def c600 : List Lit := [(48, true)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true :=
  Snake9.LocalRup.prove_clause [c597, c152, c65] c600 (by decide) p (sat_cons (step597 p h) (sat_cons (step152 p h) (sat_cons (step65 p h) (sat_nil p))))
def c601 : List Lit := [(1350, true)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true :=
  Snake9.LocalRup.prove_clause [c587, c600, c597, c577, c158, c171, c573, c576, c599, c598, c596, c153, c412, c410, c404, c405, c402, c399, c400, c69, c501, c350, c398, c347, c394, c80, c126, c94, c63, c71] c601 (by decide) p (sat_cons (step587 p h) (sat_cons (step600 p h) (sat_cons (step597 p h) (sat_cons (step577 p h) (sat_cons (step158 p h) (sat_cons (step171 p h) (sat_cons (step573 p h) (sat_cons (step576 p h) (sat_cons (step599 p h) (sat_cons (step598 p h) (sat_cons (step596 p h) (sat_cons (step153 p h) (sat_cons (step412 p h) (sat_cons (step410 p h) (sat_cons (step404 p h) (sat_cons (step405 p h) (sat_cons (step402 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step69 p h) (sat_cons (step501 p h) (sat_cons (step350 p h) (sat_cons (step398 p h) (sat_cons (step347 p h) (sat_cons (step394 p h) (sat_cons (step80 p h) (sat_cons (step126 p h) (sat_cons (step94 p h) (sat_cons (step63 p h) (sat_cons (step71 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c602 : List Lit := [(1359, true)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true :=
  Snake9.LocalRup.prove_clause [c601, c581, c422] c602 (by decide) p (sat_cons (step601 p h) (sat_cons (step581 p h) (sat_cons (step422 p h) (sat_nil p))))
def c603 : List Lit := [(1311, false)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true :=
  Snake9.LocalRup.prove_clause [c602, c491, c432] c603 (by decide) p (sat_cons (step602 p h) (sat_cons (step491 p h) (sat_cons (step432 p h) (sat_nil p))))
def c604 : List Lit := [(1289, false)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true :=
  Snake9.LocalRup.prove_clause [c603, c371] c604 (by decide) p (sat_cons (step603 p h) (sat_cons (step371 p h) (sat_nil p)))
def c605 : List Lit := [(1285, false)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true :=
  Snake9.LocalRup.prove_clause [c604, c476] c605 (by decide) p (sat_cons (step604 p h) (sat_cons (step476 p h) (sat_nil p)))
def c606 : List Lit := [(1283, false)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true :=
  Snake9.LocalRup.prove_clause [c605, c348] c606 (by decide) p (sat_cons (step605 p h) (sat_cons (step348 p h) (sat_nil p)))
def c607 : List Lit := [(59, true)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true :=
  Snake9.LocalRup.prove_clause [c605, c349] c607 (by decide) p (sat_cons (step605 p h) (sat_cons (step349 p h) (sat_nil p)))
def c608 : List Lit := [(60, true)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true :=
  Snake9.LocalRup.prove_clause [c606, c347] c608 (by decide) p (sat_cons (step606 p h) (sat_cons (step347 p h) (sat_nil p)))
def c609 : List Lit := [(101, false)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true :=
  Snake9.LocalRup.prove_clause [c607, c597, c600, c69] c609 (by decide) p (sat_cons (step607 p h) (sat_cons (step597 p h) (sat_cons (step600 p h) (sat_cons (step69 p h) (sat_nil p)))))
def c610 : List Lit := [(77, true)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true :=
  Snake9.LocalRup.prove_clause [c608, c158, c80] c610 (by decide) p (sat_cons (step608 p h) (sat_cons (step158 p h) (sat_cons (step80 p h) (sat_nil p))))
def c611 : List Lit := [(1343, true)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true :=
  Snake9.LocalRup.prove_clause [c609, c402] c611 (by decide) p (sat_cons (step609 p h) (sat_cons (step402 p h) (sat_nil p)))
def c612 : List Lit := [(29, false)]
theorem step612 (p : Nat → Bool) (h : Constraints p) : clause p c612 = true :=
  Snake9.LocalRup.prove_clause [c610, c576, c573, c94] c612 (by decide) p (sat_cons (step610 p h) (sat_cons (step576 p h) (sat_cons (step573 p h) (sat_cons (step94 p h) (sat_nil p)))))
def c613 : List Lit := [(1345, true)]
theorem step613 (p : Nat → Bool) (h : Constraints p) : clause p c613 = true :=
  Snake9.LocalRup.prove_clause [c611, c404] c613 (by decide) p (sat_cons (step611 p h) (sat_cons (step404 p h) (sat_nil p)))
def c614 : List Lit := [(1341, false)]
theorem step614 (p : Nat → Bool) (h : Constraints p) : clause p c614 = true :=
  Snake9.LocalRup.prove_clause [c611, c589, c406] c614 (by decide) p (sat_cons (step611 p h) (sat_cons (step589 p h) (sat_cons (step406 p h) (sat_nil p))))
def c615 : List Lit := [(52, true)]
theorem step615 (p : Nat → Bool) (h : Constraints p) : clause p c615 = true :=
  Snake9.LocalRup.prove_clause [c612, c153, c596, c71] c615 (by decide) p (sat_cons (step612 p h) (sat_cons (step153 p h) (sat_cons (step596 p h) (sat_cons (step71 p h) (sat_nil p)))))
def c616 : List Lit := [(1339, false)]
theorem step616 (p : Nat → Bool) (h : Constraints p) : clause p c616 = true :=
  Snake9.LocalRup.prove_clause [c613, c583, c413] c616 (by decide) p (sat_cons (step613 p h) (sat_cons (step583 p h) (sat_cons (step413 p h) (sat_nil p))))
def c617 : List Lit := [(95, true)]
theorem step617 (p : Nat → Bool) (h : Constraints p) : clause p c617 = true :=
  Snake9.LocalRup.prove_clause [c614, c399] c617 (by decide) p (sat_cons (step614 p h) (sat_cons (step399 p h) (sat_nil p)))
def c618 : List Lit := [(94, true)]
theorem step618 (p : Nat → Bool) (h : Constraints p) : clause p c618 = true :=
  Snake9.LocalRup.prove_clause [c614, c400] c618 (by decide) p (sat_cons (step614 p h) (sat_cons (step400 p h) (sat_nil p)))
def c619 : List Lit := [(92, false)]
theorem step619 (p : Nat → Bool) (h : Constraints p) : clause p c619 = true :=
  Snake9.LocalRup.prove_clause [c615, c598, c599, c63] c619 (by decide) p (sat_cons (step615 p h) (sat_cons (step598 p h) (sat_cons (step599 p h) (sat_cons (step63 p h) (sat_nil p)))))
def c620 : List Lit := [(88, false)]
theorem step620 (p : Nat → Bool) (h : Constraints p) : clause p c620 = true :=
  Snake9.LocalRup.prove_clause [c618, c617, c501] c620 (by decide) p (sat_cons (step618 p h) (sat_cons (step617 p h) (sat_cons (step501 p h) (sat_nil p))))
def c621 : List Lit := [(93, false)]
theorem step621 (p : Nat → Bool) (h : Constraints p) : clause p c621 = true :=
  Snake9.LocalRup.prove_clause [c619, c171, c126] c621 (by decide) p (sat_cons (step619 p h) (sat_cons (step171 p h) (sat_cons (step126 p h) (sat_nil p))))
def c622 : List Lit := [(1336, false)]
theorem step622 (p : Nat → Bool) (h : Constraints p) : clause p c622 = true :=
  Snake9.LocalRup.prove_clause [c620, c616, c398] c622 (by decide) p (sat_cons (step620 p h) (sat_cons (step616 p h) (sat_cons (step398 p h) (sat_nil p))))
def c623 : List Lit := []
theorem step623 (p : Nat → Bool) (h : Constraints p) : clause p c623 = true :=
  Snake9.LocalRup.prove_clause [c621, c622, c394] c623 (by decide) p (sat_cons (step621 p h) (sat_cons (step622 p h) (sat_cons (step394 p h) (sat_nil p))))
end B112E154
