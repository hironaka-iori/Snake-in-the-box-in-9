import B112E205Part0002
namespace B112E205
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c779 : List Lit := [(1502, false)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true :=
  Snake9.LocalRup.prove_clause [c778, c556] c779 (by decide) p (sat_cons (step778 p h) (sat_cons (step556 p h) (sat_nil p)))
def c780 : List Lit := [(1482, false)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true :=
  Snake9.LocalRup.prove_clause [c778, c665, c561] c780 (by decide) p (sat_cons (step778 p h) (sat_cons (step665 p h) (sat_cons (step561 p h) (sat_nil p))))
def c781 : List Lit := [(1490, false)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true :=
  Snake9.LocalRup.prove_clause [c779, c664, c551] c781 (by decide) p (sat_cons (step779 p h) (sat_cons (step664 p h) (sat_cons (step551 p h) (sat_nil p))))
def c782 : List Lit := [(1476, true)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true :=
  Snake9.LocalRup.prove_clause [c781, c651] c782 (by decide) p (sat_cons (step781 p h) (sat_cons (step651 p h) (sat_nil p)))
def c783 : List Lit := [(1478, true)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true :=
  Snake9.LocalRup.prove_clause [c782, c511] c783 (by decide) p (sat_cons (step782 p h) (sat_cons (step511 p h) (sat_nil p)))
def c784 : List Lit := [(1481, true)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true :=
  Snake9.LocalRup.prove_clause [c783, c516] c784 (by decide) p (sat_cons (step783 p h) (sat_cons (step516 p h) (sat_nil p)))
def c785 : List Lit := [(1473, false)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true :=
  Snake9.LocalRup.prove_clause [c783, c780, c520] c785 (by decide) p (sat_cons (step783 p h) (sat_cons (step780 p h) (sat_cons (step520 p h) (sat_nil p))))
def c786 : List Lit := [(1508, true)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true :=
  Snake9.LocalRup.prove_clause [c784, c665, c557] c786 (by decide) p (sat_cons (step784 p h) (sat_cons (step665 p h) (sat_cons (step557 p h) (sat_nil p))))
def c787 : List Lit := [(1448, true)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true :=
  Snake9.LocalRup.prove_clause [c785, c622] c787 (by decide) p (sat_cons (step785 p h) (sat_cons (step622 p h) (sat_nil p)))
def c788 : List Lit := [(1461, false)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true :=
  Snake9.LocalRup.prove_clause [c786, c777, c571] c788 (by decide) p (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step571 p h) (sat_nil p))))
def c789 : List Lit := [(1452, true)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true :=
  Snake9.LocalRup.prove_clause [c787, c477] c789 (by decide) p (sat_cons (step787 p h) (sat_cons (step477 p h) (sat_nil p)))
def c790 : List Lit := []
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true :=
  Snake9.LocalRup.prove_clause [c788, c789, c768, c494] c790 (by decide) p (sat_cons (step788 p h) (sat_cons (step789 p h) (sat_cons (step768 p h) (sat_cons (step494 p h) (sat_nil p)))))
end B112E205
