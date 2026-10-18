import B112E024Part0056
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5010 : List Lit := [(54, false)]
theorem step5010 (p : Nat → Bool) (h : Constraints p) : clause p c5010 = true :=
  Snake9.LocalRup.prove_clause [c5008, c4991, c4837, c4957, c4613, c4961, c2271] c5010 (by decide) p (sat_cons (step5008 p h) (sat_cons (step4991 p h) (sat_cons (step4837 p h) (sat_cons (step4957 p h) (sat_cons (step4613 p h) (sat_cons (step4961 p h) (sat_cons (step2271 p h) (sat_nil p))))))))
def c5011 : List Lit := [(1627, false)]
theorem step5011 (p : Nat → Bool) (h : Constraints p) : clause p c5011 = true :=
  Snake9.LocalRup.prove_clause [c5009, c4957, c4852] c5011 (by decide) p (sat_cons (step5009 p h) (sat_cons (step4957 p h) (sat_cons (step4852 p h) (sat_nil p))))
def c5012 : List Lit := [(1642, false)]
theorem step5012 (p : Nat → Bool) (h : Constraints p) : clause p c5012 = true :=
  Snake9.LocalRup.prove_clause [c5009, c4961, c1290] c5012 (by decide) p (sat_cons (step5009 p h) (sat_cons (step4961 p h) (sat_cons (step1290 p h) (sat_nil p))))
def c5013 : List Lit := [(1727, true)]
theorem step5013 (p : Nat → Bool) (h : Constraints p) : clause p c5013 = true :=
  Snake9.LocalRup.prove_clause [c5009, c4991, c1283] c5013 (by decide) p (sat_cons (step5009 p h) (sat_cons (step4991 p h) (sat_cons (step1283 p h) (sat_nil p))))
def c5014 : List Lit := [(1624, false)]
theorem step5014 (p : Nat → Bool) (h : Constraints p) : clause p c5014 = true :=
  Snake9.LocalRup.prove_clause [c5011, c4838, c1097] c5014 (by decide) p (sat_cons (step5011 p h) (sat_cons (step4838 p h) (sat_cons (step1097 p h) (sat_nil p))))
def c5015 : List Lit := [(71, false)]
theorem step5015 (p : Nat → Bool) (h : Constraints p) : clause p c5015 = true :=
  Snake9.LocalRup.prove_clause [c5012, c4989, c4957, c4105] c5015 (by decide) p (sat_cons (step5012 p h) (sat_cons (step4989 p h) (sat_cons (step4957 p h) (sat_cons (step4105 p h) (sat_nil p)))))
def c5016 : List Lit := [(1577, false)]
theorem step5016 (p : Nat → Bool) (h : Constraints p) : clause p c5016 = true :=
  Snake9.LocalRup.prove_clause [c5013, c1689] c5016 (by decide) p (sat_cons (step5013 p h) (sat_cons (step1689 p h) (sat_nil p)))
def c5017 : List Lit := [(1536, false)]
theorem step5017 (p : Nat → Bool) (h : Constraints p) : clause p c5017 = true :=
  Snake9.LocalRup.prove_clause [c5016, c5010, c4939] c5017 (by decide) p (sat_cons (step5016 p h) (sat_cons (step5010 p h) (sat_cons (step4939 p h) (sat_nil p))))
def c5018 : List Lit := [(55, true)]
theorem step5018 (p : Nat → Bool) (h : Constraints p) : clause p c5018 = true :=
  Snake9.LocalRup.prove_clause [c5017, c942] c5018 (by decide) p (sat_cons (step5017 p h) (sat_cons (step942 p h) (sat_nil p)))
def c5019 : List Lit := [(90, true)]
theorem step5019 (p : Nat → Bool) (h : Constraints p) : clause p c5019 = true :=
  Snake9.LocalRup.prove_clause [c5018, c5015, c1578] c5019 (by decide) p (sat_cons (step5018 p h) (sat_cons (step5015 p h) (sat_cons (step1578 p h) (sat_nil p))))
def c5020 : List Lit := [(110, false)]
theorem step5020 (p : Nat → Bool) (h : Constraints p) : clause p c5020 = true :=
  Snake9.LocalRup.prove_clause [c5019, c4951, c5018, c444] c5020 (by decide) p (sat_cons (step5019 p h) (sat_cons (step4951 p h) (sat_cons (step5018 p h) (sat_cons (step444 p h) (sat_nil p)))))
def c5021 : List Lit := [(89, false)]
theorem step5021 (p : Nat → Bool) (h : Constraints p) : clause p c5021 = true :=
  Snake9.LocalRup.prove_clause [c5019, c5018, c4951, c440] c5021 (by decide) p (sat_cons (step5019 p h) (sat_cons (step5018 p h) (sat_cons (step4951 p h) (sat_cons (step440 p h) (sat_nil p)))))
def c5022 : List Lit := [(111, true)]
theorem step5022 (p : Nat → Bool) (h : Constraints p) : clause p c5022 = true :=
  Snake9.LocalRup.prove_clause [c5020, c4986, c1200] c5022 (by decide) p (sat_cons (step5020 p h) (sat_cons (step4986 p h) (sat_cons (step1200 p h) (sat_nil p))))
def c5023 : List Lit := [(1623, true)]
theorem step5023 (p : Nat → Bool) (h : Constraints p) : clause p c5023 = true :=
  Snake9.LocalRup.prove_clause [c5021, c1090] c5023 (by decide) p (sat_cons (step5021 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c5024 : List Lit := [(86, true)]
theorem step5024 (p : Nat → Bool) (h : Constraints p) : clause p c5024 = true :=
  Snake9.LocalRup.prove_clause [c5021, c5014, c1092] c5024 (by decide) p (sat_cons (step5021 p h) (sat_cons (step5014 p h) (sat_cons (step1092 p h) (sat_nil p))))
def c5025 : List Lit := [(1622, false)]
theorem step5025 (p : Nat → Bool) (h : Constraints p) : clause p c5025 = true :=
  Snake9.LocalRup.prove_clause [c5023, c5011, c1099] c5025 (by decide) p (sat_cons (step5023 p h) (sat_cons (step5011 p h) (sat_cons (step1099 p h) (sat_nil p))))
def c5026 : List Lit := [(108, true)]
theorem step5026 (p : Nat → Bool) (h : Constraints p) : clause p c5026 = true :=
  Snake9.LocalRup.prove_clause [c5024, c4985, c2051] c5026 (by decide) p (sat_cons (step5024 p h) (sat_cons (step4985 p h) (sat_cons (step2051 p h) (sat_nil p))))
def c5027 : List Lit := [(81, true)]
theorem step5027 (p : Nat → Bool) (h : Constraints p) : clause p c5027 = true :=
  Snake9.LocalRup.prove_clause [c5025, c4837, c1089] c5027 (by decide) p (sat_cons (step5025 p h) (sat_cons (step4837 p h) (sat_cons (step1089 p h) (sat_nil p))))
def c5028 : List Lit := [(104, false)]
theorem step5028 (p : Nat → Bool) (h : Constraints p) : clause p c5028 = true :=
  Snake9.LocalRup.prove_clause [c5026, c4950, c5027, c522] c5028 (by decide) p (sat_cons (step5026 p h) (sat_cons (step4950 p h) (sat_cons (step5027 p h) (sat_cons (step522 p h) (sat_nil p)))))
def c5029 : List Lit := [(109, false)]
theorem step5029 (p : Nat → Bool) (h : Constraints p) : clause p c5029 = true :=
  Snake9.LocalRup.prove_clause [c5026, c4950, c5022, c539] c5029 (by decide) p (sat_cons (step5026 p h) (sat_cons (step4950 p h) (sat_cons (step5022 p h) (sat_cons (step539 p h) (sat_nil p)))))
def c5030 : List Lit := []
theorem step5030 (p : Nat → Bool) (h : Constraints p) : clause p c5030 = true :=
  Snake9.LocalRup.prove_clause [c5028, c5029, c5026, c1630] c5030 (by decide) p (sat_cons (step5028 p h) (sat_cons (step5029 p h) (sat_cons (step5026 p h) (sat_cons (step1630 p h) (sat_nil p)))))
end B112E024
