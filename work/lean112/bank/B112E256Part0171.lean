import B112E256Part0170
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c12788 : List Lit := [(18, true)]
theorem step12788 (p : Nat → Bool) (h : Constraints p) : clause p c12788 = true :=
  Snake9.LocalRup.prove_clause [c12786, c1139] c12788 (by decide) p (sat_cons (step12786 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c12789 : List Lit := [(917, true)]
theorem step12789 (p : Nat → Bool) (h : Constraints p) : clause p c12789 = true :=
  Snake9.LocalRup.prove_clause [c12787, c1249] c12789 (by decide) p (sat_cons (step12787 p h) (sat_cons (step1249 p h) (sat_nil p)))
def c12790 : List Lit := [(954, true)]
theorem step12790 (p : Nat → Bool) (h : Constraints p) : clause p c12790 = true :=
  Snake9.LocalRup.prove_clause [c12787, c12786, c12671] c12790 (by decide) p (sat_cons (step12787 p h) (sat_cons (step12786 p h) (sat_cons (step12671 p h) (sat_nil p))))
def c12791 : List Lit := [(921, true)]
theorem step12791 (p : Nat → Bool) (h : Constraints p) : clause p c12791 = true :=
  Snake9.LocalRup.prove_clause [c12789, c1257] c12791 (by decide) p (sat_cons (step12789 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c12792 : List Lit := [(900, false)]
theorem step12792 (p : Nat → Bool) (h : Constraints p) : clause p c12792 = true :=
  Snake9.LocalRup.prove_clause [c12790, c12764, c1421] c12792 (by decide) p (sat_cons (step12790 p h) (sat_cons (step12764 p h) (sat_cons (step1421 p h) (sat_nil p))))
def c12793 : List Lit := [(976, true)]
theorem step12793 (p : Nat → Bool) (h : Constraints p) : clause p c12793 = true :=
  Snake9.LocalRup.prove_clause [c12790, c12772, c1413] c12793 (by decide) p (sat_cons (step12790 p h) (sat_cons (step12772 p h) (sat_cons (step1413 p h) (sat_nil p))))
def c12794 : List Lit := [(946, false)]
theorem step12794 (p : Nat → Bool) (h : Constraints p) : clause p c12794 = true :=
  Snake9.LocalRup.prove_clause [c12791, c12735, c1333] c12794 (by decide) p (sat_cons (step12791 p h) (sat_cons (step12735 p h) (sat_cons (step1333 p h) (sat_nil p))))
def c12795 : List Lit := [(867, false)]
theorem step12795 (p : Nat → Bool) (h : Constraints p) : clause p c12795 = true :=
  Snake9.LocalRup.prove_clause [c12792, c12770, c1230] c12795 (by decide) p (sat_cons (step12792 p h) (sat_cons (step12770 p h) (sat_cons (step1230 p h) (sat_nil p))))
def c12796 : List Lit := [(1121, false)]
theorem step12796 (p : Nat → Bool) (h : Constraints p) : clause p c12796 = true :=
  Snake9.LocalRup.prove_clause [c12793, c2076] c12796 (by decide) p (sat_cons (step12793 p h) (sat_cons (step2076 p h) (sat_nil p)))
def c12797 : List Lit := [(860, false)]
theorem step12797 (p : Nat → Bool) (h : Constraints p) : clause p c12797 = true :=
  Snake9.LocalRup.prove_clause [c12795, c12768, c1137] c12797 (by decide) p (sat_cons (step12795 p h) (sat_cons (step12768 p h) (sat_cons (step1137 p h) (sat_nil p))))
def c12798 : List Lit := [(993, false)]
theorem step12798 (p : Nat → Bool) (h : Constraints p) : clause p c12798 = true :=
  Snake9.LocalRup.prove_clause [c12796, c12773, c12758, c12740, c12786, c12628] c12798 (by decide) p (sat_cons (step12796 p h) (sat_cons (step12773 p h) (sat_cons (step12758 p h) (sat_cons (step12740 p h) (sat_cons (step12786 p h) (sat_cons (step12628 p h) (sat_nil p)))))))
def c12799 : List Lit := [(857, false)]
theorem step12799 (p : Nat → Bool) (h : Constraints p) : clause p c12799 = true :=
  Snake9.LocalRup.prove_clause [c12797, c12748, c1116] c12799 (by decide) p (sat_cons (step12797 p h) (sat_cons (step12748 p h) (sat_cons (step1116 p h) (sat_nil p))))
def c12800 : List Lit := [(941, true)]
theorem step12800 (p : Nat → Bool) (h : Constraints p) : clause p c12800 = true :=
  Snake9.LocalRup.prove_clause [c12798, c12636] c12800 (by decide) p (sat_cons (step12798 p h) (sat_cons (step12636 p h) (sat_nil p)))
def c12801 : List Lit := [(11, true)]
theorem step12801 (p : Nat → Bool) (h : Constraints p) : clause p c12801 = true :=
  Snake9.LocalRup.prove_clause [c12799, c12742, c1111] c12801 (by decide) p (sat_cons (step12799 p h) (sat_cons (step12742 p h) (sat_cons (step1111 p h) (sat_nil p))))
def c12802 : List Lit := [(932, false)]
theorem step12802 (p : Nat → Bool) (h : Constraints p) : clause p c12802 = true :=
  Snake9.LocalRup.prove_clause [c12800, c12794, c1310] c12802 (by decide) p (sat_cons (step12800 p h) (sat_cons (step12794 p h) (sat_cons (step1310 p h) (sat_nil p))))
def c12803 : List Lit := []
theorem step12803 (p : Nat → Bool) (h : Constraints p) : clause p c12803 = true :=
  Snake9.LocalRup.prove_clause [c12801, c12802, c12788, c2443] c12803 (by decide) p (sat_cons (step12801 p h) (sat_cons (step12802 p h) (sat_cons (step12788 p h) (sat_cons (step2443 p h) (sat_nil p)))))
end B112E256
