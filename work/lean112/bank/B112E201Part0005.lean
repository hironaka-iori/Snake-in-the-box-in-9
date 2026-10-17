import B112E201Part0004
namespace B112E201
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c992 : List Lit := [(1471, false)]
theorem step992 (p : Nat → Bool) (h : Constraints p) : clause p c992 = true :=
  Snake9.LocalRup.prove_clause [c987, c596] c992 (by decide) p (sat_cons (step987 p h) (sat_cons (step596 p h) (sat_nil p)))
def c993 : List Lit := [(85, true)]
theorem step993 (p : Nat → Bool) (h : Constraints p) : clause p c993 = true :=
  Snake9.LocalRup.prove_clause [c987, c597] c993 (by decide) p (sat_cons (step987 p h) (sat_cons (step597 p h) (sat_nil p)))
def c994 : List Lit := [(1490, false)]
theorem step994 (p : Nat → Bool) (h : Constraints p) : clause p c994 = true :=
  Snake9.LocalRup.prove_clause [c989, c874, c635] c994 (by decide) p (sat_cons (step989 p h) (sat_cons (step874 p h) (sat_cons (step635 p h) (sat_nil p))))
def c995 : List Lit := [(43, true)]
theorem step995 (p : Nat → Bool) (h : Constraints p) : clause p c995 = true :=
  Snake9.LocalRup.prove_clause [c990, c969, c495] c995 (by decide) p (sat_cons (step990 p h) (sat_cons (step969 p h) (sat_cons (step495 p h) (sat_nil p))))
def c996 : List Lit := [(88, true)]
theorem step996 (p : Nat → Bool) (h : Constraints p) : clause p c996 = true :=
  Snake9.LocalRup.prove_clause [c992, c593] c996 (by decide) p (sat_cons (step992 p h) (sat_cons (step593 p h) (sat_nil p)))
def c997 : List Lit := [(87, true)]
theorem step997 (p : Nat → Bool) (h : Constraints p) : clause p c997 = true :=
  Snake9.LocalRup.prove_clause [c992, c594] c997 (by decide) p (sat_cons (step992 p h) (sat_cons (step594 p h) (sat_nil p)))
def c998 : List Lit := [(92, true)]
theorem step998 (p : Nat → Bool) (h : Constraints p) : clause p c998 = true :=
  Snake9.LocalRup.prove_clause [c997, c855, c152] c998 (by decide) p (sat_cons (step997 p h) (sat_cons (step855 p h) (sat_cons (step152 p h) (sat_nil p))))
def c999 : List Lit := [(86, true)]
theorem step999 (p : Nat → Bool) (h : Constraints p) : clause p c999 = true :=
  Snake9.LocalRup.prove_clause [c997, c855, c153] c999 (by decide) p (sat_cons (step997 p h) (sat_cons (step855 p h) (sat_cons (step153 p h) (sat_nil p))))
def c1000 : List Lit := [(91, true)]
theorem step1000 (p : Nat → Bool) (h : Constraints p) : clause p c1000 = true :=
  Snake9.LocalRup.prove_clause [c998, c222, c961, c159] c1000 (by decide) p (sat_cons (step998 p h) (sat_cons (step222 p h) (sat_cons (step961 p h) (sat_cons (step159 p h) (sat_nil p)))))
def c1001 : List Lit := [(79, false)]
theorem step1001 (p : Nat → Bool) (h : Constraints p) : clause p c1001 = true :=
  Snake9.LocalRup.prove_clause [c999, c993, c997, c151] c1001 (by decide) p (sat_cons (step999 p h) (sat_cons (step993 p h) (sat_cons (step997 p h) (sat_cons (step151 p h) (sat_nil p)))))
def c1002 : List Lit := [(1453, true)]
theorem step1002 (p : Nat → Bool) (h : Constraints p) : clause p c1002 = true :=
  Snake9.LocalRup.prove_clause [c1000, c1001, c996, c991, c994, c958, c995, c976, c898] c1002 (by decide) p (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step996 p h) (sat_cons (step991 p h) (sat_cons (step994 p h) (sat_cons (step958 p h) (sat_cons (step995 p h) (sat_cons (step976 p h) (sat_cons (step898 p h) (sat_nil p))))))))))
def c1003 : List Lit := [(1444, true)]
theorem step1003 (p : Nat → Bool) (h : Constraints p) : clause p c1003 = true :=
  Snake9.LocalRup.prove_clause [c1001, c569] c1003 (by decide) p (sat_cons (step1001 p h) (sat_cons (step569 p h) (sat_nil p)))
def c1004 : List Lit := [(1434, false)]
theorem step1004 (p : Nat → Bool) (h : Constraints p) : clause p c1004 = true :=
  Snake9.LocalRup.prove_clause [c1002, c983, c592] c1004 (by decide) p (sat_cons (step1002 p h) (sat_cons (step983 p h) (sat_cons (step592 p h) (sat_nil p))))
def c1005 : List Lit := [(72, false)]
theorem step1005 (p : Nat → Bool) (h : Constraints p) : clause p c1005 = true :=
  Snake9.LocalRup.prove_clause [c1004, c974, c899] c1005 (by decide) p (sat_cons (step1004 p h) (sat_cons (step974 p h) (sat_cons (step899 p h) (sat_nil p))))
def c1006 : List Lit := [(1439, true)]
theorem step1006 (p : Nat → Bool) (h : Constraints p) : clause p c1006 = true :=
  Snake9.LocalRup.prove_clause [c1005, c566] c1006 (by decide) p (sat_cons (step1005 p h) (sat_cons (step566 p h) (sat_nil p)))
def c1007 : List Lit := [(1441, true)]
theorem step1007 (p : Nat → Bool) (h : Constraints p) : clause p c1007 = true :=
  Snake9.LocalRup.prove_clause [c1006, c567] c1007 (by decide) p (sat_cons (step1006 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1008 : List Lit := [(1449, false)]
theorem step1008 (p : Nat → Bool) (h : Constraints p) : clause p c1008 = true :=
  Snake9.LocalRup.prove_clause [c1007, c988, c585] c1008 (by decide) p (sat_cons (step1007 p h) (sat_cons (step988 p h) (sat_cons (step585 p h) (sat_nil p))))
def c1009 : List Lit := [(1445, false)]
theorem step1009 (p : Nat → Bool) (h : Constraints p) : clause p c1009 = true :=
  Snake9.LocalRup.prove_clause [c1008, c579] c1009 (by decide) p (sat_cons (step1008 p h) (sat_cons (step579 p h) (sat_nil p)))
def c1010 : List Lit := [(1446, false)]
theorem step1010 (p : Nat → Bool) (h : Constraints p) : clause p c1010 = true :=
  Snake9.LocalRup.prove_clause [c1008, c1003, c577] c1010 (by decide) p (sat_cons (step1008 p h) (sat_cons (step1003 p h) (sat_cons (step577 p h) (sat_nil p))))
def c1011 : List Lit := [(77, true)]
theorem step1011 (p : Nat → Bool) (h : Constraints p) : clause p c1011 = true :=
  Snake9.LocalRup.prove_clause [c1009, c1001, c571] c1011 (by decide) p (sat_cons (step1009 p h) (sat_cons (step1001 p h) (sat_cons (step571 p h) (sat_nil p))))
def c1012 : List Lit := [(80, true)]
theorem step1012 (p : Nat → Bool) (h : Constraints p) : clause p c1012 = true :=
  Snake9.LocalRup.prove_clause [c1010, c573] c1012 (by decide) p (sat_cons (step1010 p h) (sat_cons (step573 p h) (sat_nil p)))
def c1013 : List Lit := [(81, false)]
theorem step1013 (p : Nat → Bool) (h : Constraints p) : clause p c1013 = true :=
  Snake9.LocalRup.prove_clause [c1011, c1012, c1000, c145] c1013 (by decide) p (sat_cons (step1011 p h) (sat_cons (step1012 p h) (sat_cons (step1000 p h) (sat_cons (step145 p h) (sat_nil p)))))
def c1014 : List Lit := [(90, false)]
theorem step1014 (p : Nat → Bool) (h : Constraints p) : clause p c1014 = true :=
  Snake9.LocalRup.prove_clause [c1012, c1000, c996, c156] c1014 (by decide) p (sat_cons (step1012 p h) (sat_cons (step1000 p h) (sat_cons (step996 p h) (sat_cons (step156 p h) (sat_nil p)))))
def c1015 : List Lit := [(76, true)]
theorem step1015 (p : Nat → Bool) (h : Constraints p) : clause p c1015 = true :=
  Snake9.LocalRup.prove_clause [c1014, c1013, c856, c1012, c143] c1015 (by decide) p (sat_cons (step1014 p h) (sat_cons (step1013 p h) (sat_cons (step856 p h) (sat_cons (step1012 p h) (sat_cons (step143 p h) (sat_nil p))))))
def c1016 : List Lit := [(15, false)]
theorem step1016 (p : Nat → Bool) (h : Constraints p) : clause p c1016 = true :=
  Snake9.LocalRup.prove_clause [c1015, c1012, c1011, c139] c1016 (by decide) p (sat_cons (step1015 p h) (sat_cons (step1012 p h) (sat_cons (step1011 p h) (sat_cons (step139 p h) (sat_nil p)))))
def c1017 : List Lit := [(1331, true)]
theorem step1017 (p : Nat → Bool) (h : Constraints p) : clause p c1017 = true :=
  Snake9.LocalRup.prove_clause [c1016, c433] c1017 (by decide) p (sat_cons (step1016 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1018 : List Lit := [(19, true)]
theorem step1018 (p : Nat → Bool) (h : Constraints p) : clause p c1018 = true :=
  Snake9.LocalRup.prove_clause [c1016, c959, c434] c1018 (by decide) p (sat_cons (step1016 p h) (sat_cons (step959 p h) (sat_cons (step434 p h) (sat_nil p))))
def c1019 : List Lit := [(14, true)]
theorem step1019 (p : Nat → Bool) (h : Constraints p) : clause p c1019 = true :=
  Snake9.LocalRup.prove_clause [c1017, c958, c438] c1019 (by decide) p (sat_cons (step1017 p h) (sat_cons (step958 p h) (sat_cons (step438 p h) (sat_nil p))))
def c1020 : List Lit := [(16, true)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true :=
  Snake9.LocalRup.prove_clause [c1019, c955, c935] c1020 (by decide) p (sat_cons (step1019 p h) (sat_cons (step955 p h) (sat_cons (step935 p h) (sat_nil p))))
def c1021 : List Lit := []
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true :=
  Snake9.LocalRup.prove_clause [c1020, c1019, c1018, c1011, c41] c1021 (by decide) p (sat_cons (step1020 p h) (sat_cons (step1019 p h) (sat_cons (step1018 p h) (sat_cons (step1011 p h) (sat_cons (step41 p h) (sat_nil p))))))
end B112E201
