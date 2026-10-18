import B112E094Part0003
namespace B112E094
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c887 : List Lit := [(1375, true), (81, true), (87, true)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true :=
  Snake9.LocalRup.prove_clause [c873, c537, c538, c834, c832, c104, c886] c887 (by decide) p (sat_cons (step873 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step834 p h) (sat_cons (step832 p h) (sat_cons (step104 p h) (sat_cons (step886 p h) (sat_nil p))))))))
def c888 : List Lit := [(47, true), (1415, false)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true :=
  Snake9.LocalRup.prove_clause [c882, c598, c850, c845, c462, c439, c446, c449, c783, c460, c708, c843, c666, c848, c607] c888 (by decide) p (sat_cons (step882 p h) (sat_cons (step598 p h) (sat_cons (step850 p h) (sat_cons (step845 p h) (sat_cons (step462 p h) (sat_cons (step439 p h) (sat_cons (step446 p h) (sat_cons (step449 p h) (sat_cons (step783 p h) (sat_cons (step460 p h) (sat_cons (step708 p h) (sat_cons (step843 p h) (sat_cons (step666 p h) (sat_cons (step848 p h) (sat_cons (step607 p h) (sat_nil p))))))))))))))))
def c889 : List Lit := [(1416, false)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true :=
  Snake9.LocalRup.prove_clause [c885, c882, c599, c608, c849, c666, c844, c726, c461] c889 (by decide) p (sat_cons (step885 p h) (sat_cons (step882 p h) (sat_cons (step599 p h) (sat_cons (step608 p h) (sat_cons (step849 p h) (sat_cons (step666 p h) (sat_cons (step844 p h) (sat_cons (step726 p h) (sat_cons (step461 p h) (sat_nil p))))))))))
def c890 : List Lit := [(1376, false)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true :=
  Snake9.LocalRup.prove_clause [c889, c876] c890 (by decide) p (sat_cons (step889 p h) (sat_cons (step876 p h) (sat_nil p)))
def c891 : List Lit := [(1386, true), (87, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.LocalRup.prove_clause [c875, c874, c866, c540, c542, c557, c560, c544, c536, c537, c538, c887, c531, c113] c891 (by decide) p (sat_cons (step875 p h) (sat_cons (step874 p h) (sat_cons (step866 p h) (sat_cons (step540 p h) (sat_cons (step542 p h) (sat_cons (step557 p h) (sat_cons (step560 p h) (sat_cons (step544 p h) (sat_cons (step536 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step887 p h) (sat_cons (step531 p h) (sat_cons (step113 p h) (sat_nil p)))))))))))))))
def c892 : List Lit := [(1386, false)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true :=
  Snake9.LocalRup.prove_clause [c889, c661, c596, c888, c683] c892 (by decide) p (sat_cons (step889 p h) (sat_cons (step661 p h) (sat_cons (step596 p h) (sat_cons (step888 p h) (sat_cons (step683 p h) (sat_nil p))))))
def c893 : List Lit := [(87, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true :=
  Snake9.LocalRup.prove_clause [c892, c891] c893 (by decide) p (sat_cons (step892 p h) (sat_cons (step891 p h) (sat_nil p)))
def c894 : List Lit := [(81, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true :=
  Snake9.LocalRup.prove_clause [c893, c890, c787] c894 (by decide) p (sat_cons (step893 p h) (sat_cons (step890 p h) (sat_cons (step787 p h) (sat_nil p))))
def c895 : List Lit := [(99, false)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true :=
  Snake9.LocalRup.prove_clause [c893, c867, c865, c134] c895 (by decide) p (sat_cons (step893 p h) (sat_cons (step867 p h) (sat_cons (step865 p h) (sat_cons (step134 p h) (sat_nil p)))))
def c896 : List Lit := [(1396, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true :=
  Snake9.LocalRup.prove_clause [c895, c649] c896 (by decide) p (sat_cons (step895 p h) (sat_cons (step649 p h) (sat_nil p)))
def c897 : List Lit := [(1400, true)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true :=
  Snake9.LocalRup.prove_clause [c896, c575] c897 (by decide) p (sat_cons (step896 p h) (sat_cons (step575 p h) (sat_nil p)))
def c898 : List Lit := [(1405, true)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true :=
  Snake9.LocalRup.prove_clause [c897, c654] c898 (by decide) p (sat_cons (step897 p h) (sat_cons (step654 p h) (sat_nil p)))
def c899 : List Lit := [(1375, true), (80, false)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true :=
  Snake9.LocalRup.prove_clause [c894, c537, c538, c113] c899 (by decide) p (sat_cons (step894 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step113 p h) (sat_nil p)))))
def c900 : List Lit := [(1385, false)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true :=
  Snake9.LocalRup.prove_clause [c889, c898, c897, c896, c594, c593, c655, c581, c888, c576, c564, c570, c645, c836, c161] c900 (by decide) p (sat_cons (step889 p h) (sat_cons (step898 p h) (sat_cons (step897 p h) (sat_cons (step896 p h) (sat_cons (step594 p h) (sat_cons (step593 p h) (sat_cons (step655 p h) (sat_cons (step581 p h) (sat_cons (step888 p h) (sat_cons (step576 p h) (sat_cons (step564 p h) (sat_cons (step570 p h) (sat_cons (step645 p h) (sat_cons (step836 p h) (sat_cons (step161 p h) (sat_nil p))))))))))))))))
def c901 : List Lit := [(1374, false)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true :=
  Snake9.LocalRup.prove_clause [c900, c559] c901 (by decide) p (sat_cons (step900 p h) (sat_cons (step559 p h) (sat_nil p)))
def c902 : List Lit := [(1379, false)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true :=
  Snake9.LocalRup.prove_clause [c900, c875, c556] c902 (by decide) p (sat_cons (step900 p h) (sat_cons (step875 p h) (sat_cons (step556 p h) (sat_nil p))))
def c903 : List Lit := [(1371, false)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true :=
  Snake9.LocalRup.prove_clause [c901, c874, c536] c903 (by decide) p (sat_cons (step901 p h) (sat_cons (step874 p h) (sat_cons (step536 p h) (sat_nil p))))
def c904 : List Lit := [(1375, false)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true :=
  Snake9.LocalRup.prove_clause [c902, c543] c904 (by decide) p (sat_cons (step902 p h) (sat_cons (step543 p h) (sat_nil p)))
def c905 : List Lit := [(80, true)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true :=
  Snake9.LocalRup.prove_clause [c903, c866, c531] c905 (by decide) p (sat_cons (step903 p h) (sat_cons (step866 p h) (sat_cons (step531 p h) (sat_nil p))))
def c906 : List Lit := []
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true :=
  Snake9.LocalRup.prove_clause [c904, c905, c899] c906 (by decide) p (sat_cons (step904 p h) (sat_cons (step905 p h) (sat_cons (step899 p h) (sat_nil p))))
end B112E094
