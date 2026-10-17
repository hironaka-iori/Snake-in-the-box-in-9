import B112E123Part0006
namespace B112E123
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1159 : List Lit := [(758, false)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1152, c365] c1159 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1152 p h) (sat_cons (step365 p h) (sat_nil p))))
def c1160 : List Lit := [(5, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c1159, c1127, c360] c1160 (by decide) p (sat_cons (step1159 p h) (sat_cons (step1127 p h) (sat_cons (step360 p h) (sat_nil p))))
def c1161 : List Lit := [(32, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c1160, c1109, c1145, c1139, c1059] c1161 (by decide) p (sat_cons (step1160 p h) (sat_cons (step1109 p h) (sat_cons (step1145 p h) (sat_cons (step1139 p h) (sat_cons (step1059 p h) (sat_nil p))))))
def c1162 : List Lit := [(19, false)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1143, c1126, c941] c1162 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1143 p h) (sat_cons (step1126 p h) (sat_cons (step941 p h) (sat_nil p)))))
def c1163 : List Lit := [(10, false)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1157, c1126, c1146, c1148, c984] c1163 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1126 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step984 p h) (sat_nil p)))))))
def c1164 : List Lit := [(14, true)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c1162, c1126, c1143, c1160, c1052] c1164 (by decide) p (sat_cons (step1162 p h) (sat_cons (step1126 p h) (sat_cons (step1143 p h) (sat_cons (step1160 p h) (sat_cons (step1052 p h) (sat_nil p))))))
def c1165 : List Lit := [(13, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c1163, c1157, c826] c1165 (by decide) p (sat_cons (step1163 p h) (sat_cons (step1157 p h) (sat_cons (step826 p h) (sat_nil p))))
def c1166 : List Lit := []
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c1165, c1164, c1156, c1148, c74] c1166 (by decide) p (sat_cons (step1165 p h) (sat_cons (step1164 p h) (sat_cons (step1156 p h) (sat_cons (step1148 p h) (sat_cons (step74 p h) (sat_nil p))))))
end B112E123
