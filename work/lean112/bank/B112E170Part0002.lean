import B112E170Part0001
namespace B112E170
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c580 : List Lit := [(1225, false)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true :=
  Snake9.TreeRup.prove_clause [c562, c578, c577, c455, c240, c544, c545, c146, c546, c145, c148, c573, c507, c449, c352, c274, c260, c569, c461, c54, c518, c175, c178, c198, c199, c238, c196, c237, c194, c212, c213, c193, c211, c208, c192, c210, c206, c207, c191, c209, c204, c202, c453, c203, c201, c81, c74, c80, c76, c79, c68, c579, c374, c372, c368, c365, c366, c89, c516, c88, c396, c85, c427, c262, c431, c265, c447, c267, c348, c467] c580 (by decide) p (sat_cons (step562 p h) (sat_cons (step578 p h) (sat_cons (step577 p h) (sat_cons (step455 p h) (sat_cons (step240 p h) (sat_cons (step544 p h) (sat_cons (step545 p h) (sat_cons (step146 p h) (sat_cons (step546 p h) (sat_cons (step145 p h) (sat_cons (step148 p h) (sat_cons (step573 p h) (sat_cons (step507 p h) (sat_cons (step449 p h) (sat_cons (step352 p h) (sat_cons (step274 p h) (sat_cons (step260 p h) (sat_cons (step569 p h) (sat_cons (step461 p h) (sat_cons (step54 p h) (sat_cons (step518 p h) (sat_cons (step175 p h) (sat_cons (step178 p h) (sat_cons (step198 p h) (sat_cons (step199 p h) (sat_cons (step238 p h) (sat_cons (step196 p h) (sat_cons (step237 p h) (sat_cons (step194 p h) (sat_cons (step212 p h) (sat_cons (step213 p h) (sat_cons (step193 p h) (sat_cons (step211 p h) (sat_cons (step208 p h) (sat_cons (step192 p h) (sat_cons (step210 p h) (sat_cons (step206 p h) (sat_cons (step207 p h) (sat_cons (step191 p h) (sat_cons (step209 p h) (sat_cons (step204 p h) (sat_cons (step202 p h) (sat_cons (step453 p h) (sat_cons (step203 p h) (sat_cons (step201 p h) (sat_cons (step81 p h) (sat_cons (step74 p h) (sat_cons (step80 p h) (sat_cons (step76 p h) (sat_cons (step79 p h) (sat_cons (step68 p h) (sat_cons (step579 p h) (sat_cons (step374 p h) (sat_cons (step372 p h) (sat_cons (step368 p h) (sat_cons (step365 p h) (sat_cons (step366 p h) (sat_cons (step89 p h) (sat_cons (step516 p h) (sat_cons (step88 p h) (sat_cons (step396 p h) (sat_cons (step85 p h) (sat_cons (step427 p h) (sat_cons (step262 p h) (sat_cons (step431 p h) (sat_cons (step265 p h) (sat_cons (step447 p h) (sat_cons (step267 p h) (sat_cons (step348 p h) (sat_cons (step467 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c581 : List Lit := [(1218, false)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true :=
  Snake9.LocalRup.prove_clause [c580, c475, c330] c581 (by decide) p (sat_cons (step580 p h) (sat_cons (step475 p h) (sat_cons (step330 p h) (sat_nil p))))
def c582 : List Lit := [(1201, false)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true :=
  Snake9.LocalRup.prove_clause [c580, c543, c334] c582 (by decide) p (sat_cons (step580 p h) (sat_cons (step543 p h) (sat_cons (step334 p h) (sat_nil p))))
def c583 : List Lit := [(1214, false)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true :=
  Snake9.LocalRup.prove_clause [c581, c552, c322] c583 (by decide) p (sat_cons (step581 p h) (sat_cons (step552 p h) (sat_cons (step322 p h) (sat_nil p))))
def c584 : List Lit := [(1193, false)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true :=
  Snake9.LocalRup.prove_clause [c582, c297] c584 (by decide) p (sat_cons (step582 p h) (sat_cons (step297 p h) (sat_nil p)))
def c585 : List Lit := [(44, true)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true :=
  Snake9.LocalRup.prove_clause [c583, c549, c315] c585 (by decide) p (sat_cons (step583 p h) (sat_cons (step549 p h) (sat_cons (step315 p h) (sat_nil p))))
def c586 : List Lit := [(8, false)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true :=
  Snake9.LocalRup.prove_clause [c585, c577, c578, c54] c586 (by decide) p (sat_cons (step585 p h) (sat_cons (step577 p h) (sat_cons (step578 p h) (sat_cons (step54 p h) (sat_nil p)))))
def c587 : List Lit := [(1161, true)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true :=
  Snake9.LocalRup.prove_clause [c586, c569] c587 (by decide) p (sat_cons (step586 p h) (sat_cons (step569 p h) (sat_nil p)))
def c588 : List Lit := [(1183, true)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true :=
  Snake9.LocalRup.prove_clause [c587, c274] c588 (by decide) p (sat_cons (step587 p h) (sat_cons (step274 p h) (sat_nil p)))
def c589 : List Lit := [(1175, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true :=
  Snake9.LocalRup.prove_clause [c587, c565, c275] c589 (by decide) p (sat_cons (step587 p h) (sat_cons (step565 p h) (sat_cons (step275 p h) (sat_nil p))))
def c590 : List Lit := [(1236, true)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true :=
  Snake9.LocalRup.prove_clause [c588, c550, c351] c590 (by decide) p (sat_cons (step588 p h) (sat_cons (step550 p h) (sat_cons (step351 p h) (sat_nil p))))
def c591 : List Lit := [(1172, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true :=
  Snake9.LocalRup.prove_clause [c589, c267] c591 (by decide) p (sat_cons (step589 p h) (sat_cons (step267 p h) (sat_nil p)))
def c592 : List Lit := [(1328, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true :=
  Snake9.LocalRup.prove_clause [c590, c449, c447] c592 (by decide) p (sat_cons (step590 p h) (sat_cons (step449 p h) (sat_cons (step447 p h) (sat_nil p))))
def c593 : List Lit := [(1170, false)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true :=
  Snake9.LocalRup.prove_clause [c591, c265] c593 (by decide) p (sat_cons (step591 p h) (sat_cons (step265 p h) (sat_nil p)))
def c594 : List Lit := [(1272, false)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true :=
  Snake9.LocalRup.prove_clause [c592, c559, c434] c594 (by decide) p (sat_cons (step592 p h) (sat_cons (step559 p h) (sat_cons (step434 p h) (sat_nil p))))
def c595 : List Lit := [(23, true)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true :=
  Snake9.LocalRup.prove_clause [c593, c262] c595 (by decide) p (sat_cons (step593 p h) (sat_cons (step262 p h) (sat_nil p)))
def c596 : List Lit := [(22, true)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true :=
  Snake9.LocalRup.prove_clause [c593, c263] c596 (by decide) p (sat_cons (step593 p h) (sat_cons (step263 p h) (sat_nil p)))
def c597 : List Lit := [(1266, false)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true :=
  Snake9.LocalRup.prove_clause [c594, c374] c597 (by decide) p (sat_cons (step594 p h) (sat_cons (step374 p h) (sat_nil p)))
def c598 : List Lit := [(1263, true)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true :=
  Snake9.LocalRup.prove_clause [c595, c596, c584, c502] c598 (by decide) p (sat_cons (step595 p h) (sat_cons (step596 p h) (sat_cons (step584 p h) (sat_cons (step502 p h) (sat_nil p)))))
def c599 : List Lit := []
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true :=
  Snake9.LocalRup.prove_clause [c598, c597, c372] c599 (by decide) p (sat_cons (step598 p h) (sat_cons (step597 p h) (sat_cons (step372 p h) (sat_nil p))))
end B112E170
