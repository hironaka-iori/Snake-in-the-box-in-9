import B112E027Part0053
namespace B112E027
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4906 : List Lit := [(1606, false)]
theorem step4906 (p : Nat → Bool) (h : Constraints p) : clause p c4906 = true :=
  Snake9.LocalRup.prove_clause [c4904, c4890, c1385] c4906 (by decide) p (sat_cons (step4904 p h) (sat_cons (step4890 p h) (sat_cons (step1385 p h) (sat_nil p))))
def c4907 : List Lit := [(1598, true)]
theorem step4907 (p : Nat → Bool) (h : Constraints p) : clause p c4907 = true :=
  Snake9.LocalRup.prove_clause [c4905, c1748] c4907 (by decide) p (sat_cons (step4905 p h) (sat_cons (step1748 p h) (sat_nil p)))
def c4908 : List Lit := [(1605, true)]
theorem step4908 (p : Nat → Bool) (h : Constraints p) : clause p c4908 = true :=
  Snake9.LocalRup.prove_clause [c4907, c1224] c4908 (by decide) p (sat_cons (step4907 p h) (sat_cons (step1224 p h) (sat_nil p)))
def c4909 : List Lit := [(1575, false)]
theorem step4909 (p : Nat → Bool) (h : Constraints p) : clause p c4909 = true :=
  Snake9.LocalRup.prove_clause [c4907, c4906, c1232] c4909 (by decide) p (sat_cons (step4907 p h) (sat_cons (step4906 p h) (sat_cons (step1232 p h) (sat_nil p))))
def c4910 : List Lit := [(1684, true)]
theorem step4910 (p : Nat → Bool) (h : Constraints p) : clause p c4910 = true :=
  Snake9.LocalRup.prove_clause [c4908, c4904, c1379] c4910 (by decide) p (sat_cons (step4908 p h) (sat_cons (step4904 p h) (sat_cons (step1379 p h) (sat_nil p))))
def c4911 : List Lit := [(1564, false)]
theorem step4911 (p : Nat → Bool) (h : Constraints p) : clause p c4911 = true :=
  Snake9.LocalRup.prove_clause [c4909, c1173] c4911 (by decide) p (sat_cons (step4909 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c4912 : List Lit := [(1551, false)]
theorem step4912 (p : Nat → Bool) (h : Constraints p) : clause p c4912 = true :=
  Snake9.LocalRup.prove_clause [c4910, c1763] c4912 (by decide) p (sat_cons (step4910 p h) (sat_cons (step1763 p h) (sat_nil p)))
def c4913 : List Lit := [(59, true)]
theorem step4913 (p : Nat → Bool) (h : Constraints p) : clause p c4913 = true :=
  Snake9.LocalRup.prove_clause [c4911, c1155] c4913 (by decide) p (sat_cons (step4911 p h) (sat_cons (step1155 p h) (sat_nil p)))
def c4914 : List Lit := [(1521, true)]
theorem step4914 (p : Nat → Bool) (h : Constraints p) : clause p c4914 = true :=
  Snake9.LocalRup.prove_clause [c4913, c1504] c4914 (by decide) p (sat_cons (step4913 p h) (sat_cons (step1504 p h) (sat_nil p)))
def c4915 : List Lit := [(1533, false)]
theorem step4915 (p : Nat → Bool) (h : Constraints p) : clause p c4915 = true :=
  Snake9.LocalRup.prove_clause [c4912, c4887, c1132] c4915 (by decide) p (sat_cons (step4912 p h) (sat_cons (step4887 p h) (sat_cons (step1132 p h) (sat_nil p))))
def c4916 : List Lit := []
theorem step4916 (p : Nat → Bool) (h : Constraints p) : clause p c4916 = true :=
  Snake9.LocalRup.prove_clause [c4915, c4914, c1558] c4916 (by decide) p (sat_cons (step4915 p h) (sat_cons (step4914 p h) (sat_cons (step1558 p h) (sat_nil p))))
end B112E027
