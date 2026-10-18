import B112E034Part0002
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1971 : List Lit := [(4, true), (20, true), (21, false), (38, true)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c853, c73] c1971 (by decide) p (sat_cons (step853 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1972 : List Lit := [(23, false), (22, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c854, c77] c1972 (by decide) p (sat_cons (step854 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1973 : List Lit := [(23, false), (17, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c854, c78] c1973 (by decide) p (sat_cons (step854 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1974 : List Lit := [(24, false), (31, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c855, c79] c1974 (by decide) p (sat_cons (step855 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1975 : List Lit := [(24, false), (26, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c855, c80] c1975 (by decide) p (sat_cons (step855 p h) (sat_cons (step80 p h) (sat_nil p)))
def c1976 : List Lit := [(26, true), (45, true), (25, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c856, c82] c1976 (by decide) p (sat_cons (step856 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1977 : List Lit := [(17, true), (26, true), (25, false)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c856, c83] c1977 (by decide) p (sat_cons (step856 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1978 : List Lit := [(30, true), (31, true), (27, true), (28, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c857, c100] c1978 (by decide) p (sat_cons (step857 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1979 : List Lit := [(30, true), (31, true), (20, true), (28, false)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c857, c101] c1979 (by decide) p (sat_cons (step857 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1980 : List Lit := [(27, true), (20, true), (31, true), (28, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c857, c102] c1980 (by decide) p (sat_cons (step857 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1981 : List Lit := [(30, true), (20, true), (27, true), (28, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c857, c103] c1981 (by decide) p (sat_cons (step857 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1982 : List Lit := [(101, true), (30, true), (29, false)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c858, c105] c1982 (by decide) p (sat_cons (step858 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1983 : List Lit := [(101, true), (29, false), (27, true)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c858, c106] c1983 (by decide) p (sat_cons (step858 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1984 : List Lit := [(30, true), (29, false), (27, true)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c858, c107] c1984 (by decide) p (sat_cons (step858 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1985 : List Lit := [(43, true), (108, true), (38, true), (33, false)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c859, c124] c1985 (by decide) p (sat_cons (step859 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1986 : List Lit := [(32, true), (43, true), (33, false), (108, true)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c859, c125] c1986 (by decide) p (sat_cons (step859 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1987 : List Lit := [(32, true), (108, true), (33, false), (38, true)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c859, c126] c1987 (by decide) p (sat_cons (step859 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1988 : List Lit := [(32, true), (43, true), (33, false), (38, true)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c859, c127] c1988 (by decide) p (sat_cons (step859 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1989 : List Lit := [(39, true), (110, true), (35, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c860, c132] c1989 (by decide) p (sat_cons (step860 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1990 : List Lit := [(34, true), (110, true), (35, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c860, c133] c1990 (by decide) p (sat_cons (step860 p h) (sat_cons (step133 p h) (sat_nil p)))
def c1991 : List Lit := [(34, true), (39, true), (35, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c860, c134] c1991 (by decide) p (sat_cons (step860 p h) (sat_cons (step134 p h) (sat_nil p)))
def c1992 : List Lit := [(114, true), (39, true), (36, false), (38, true)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c861, c138] c1992 (by decide) p (sat_cons (step861 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1993 : List Lit := [(114, true), (39, true), (20, true), (36, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c861, c139] c1993 (by decide) p (sat_cons (step861 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1994 : List Lit := [(36, false), (114, true), (38, true), (20, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c861, c140] c1994 (by decide) p (sat_cons (step861 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1995 : List Lit := [(39, true), (36, false), (38, true), (20, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c861, c141] c1995 (by decide) p (sat_cons (step861 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1996 : List Lit := [(37, false), (115, true), (38, true)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c862, c143] c1996 (by decide) p (sat_cons (step862 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1997 : List Lit := [(32, true), (37, false), (115, true)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c862, c144] c1997 (by decide) p (sat_cons (step862 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1998 : List Lit := [(37, false), (32, true), (38, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c862, c145] c1998 (by decide) p (sat_cons (step862 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1999 : List Lit := [(40, false), (38, true), (49, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c863, c165] c1999 (by decide) p (sat_cons (step863 p h) (sat_cons (step165 p h) (sat_nil p)))
def c2000 : List Lit := [(40, false), (39, true), (38, true)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c863, c166] c2000 (by decide) p (sat_cons (step863 p h) (sat_cons (step166 p h) (sat_nil p)))
def c2001 : List Lit := [(43, true), (42, false), (119, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c864, c170] c2001 (by decide) p (sat_cons (step864 p h) (sat_cons (step170 p h) (sat_nil p)))
def c2002 : List Lit := [(41, true), (42, false), (119, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c864, c171] c2002 (by decide) p (sat_cons (step864 p h) (sat_cons (step171 p h) (sat_nil p)))
def c2003 : List Lit := [(41, true), (43, true), (42, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c864, c172] c2003 (by decide) p (sat_cons (step864 p h) (sat_cons (step172 p h) (sat_nil p)))
def c2004 : List Lit := [(47, true), (44, false), (41, true), (45, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c865, c183] c2004 (by decide) p (sat_cons (step865 p h) (sat_cons (step183 p h) (sat_nil p)))
def c2005 : List Lit := [(41, true), (34, true), (47, true), (44, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c865, c184] c2005 (by decide) p (sat_cons (step865 p h) (sat_cons (step184 p h) (sat_nil p)))
def c2006 : List Lit := [(41, true), (124, true), (46, false), (47, true)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c866, c193] c2006 (by decide) p (sat_cons (step866 p h) (sat_cons (step193 p h) (sat_nil p)))
def c2007 : List Lit := [(124, true), (27, true), (46, false), (47, true)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c866, c194] c2007 (by decide) p (sat_cons (step866 p h) (sat_cons (step194 p h) (sat_nil p)))
def c2008 : List Lit := [(41, true), (124, true), (46, false), (27, true)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c866, c195] c2008 (by decide) p (sat_cons (step866 p h) (sat_cons (step195 p h) (sat_nil p)))
def c2009 : List Lit := [(41, true), (27, true), (46, false), (47, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c866, c196] c2009 (by decide) p (sat_cons (step866 p h) (sat_cons (step196 p h) (sat_nil p)))
def c2010 : List Lit := [(47, true), (49, true), (48, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c867, c200] c2010 (by decide) p (sat_cons (step867 p h) (sat_cons (step200 p h) (sat_nil p)))
def c2011 : List Lit := [(49, true), (48, false), (45, true)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c867, c201] c2011 (by decide) p (sat_cons (step867 p h) (sat_cons (step201 p h) (sat_nil p)))
def c2012 : List Lit := [(47, true), (48, false), (45, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c867, c202] c2012 (by decide) p (sat_cons (step867 p h) (sat_cons (step202 p h) (sat_nil p)))
def c2013 : List Lit := [(50, true), (54, true), (51, false), (87, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c868, c213] c2013 (by decide) p (sat_cons (step868 p h) (sat_cons (step213 p h) (sat_nil p)))
def c2014 : List Lit := [(55, true), (57, true), (52, false), (69, true), (88, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c869, c215] c2014 (by decide) p (sat_cons (step869 p h) (sat_cons (step215 p h) (sat_nil p)))
def c2015 : List Lit := [(50, true), (52, false), (69, true), (57, true), (88, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c869, c216] c2015 (by decide) p (sat_cons (step869 p h) (sat_cons (step216 p h) (sat_nil p)))
def c2016 : List Lit := [(55, true), (50, true), (88, true), (57, true), (52, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c869, c217] c2016 (by decide) p (sat_cons (step869 p h) (sat_cons (step217 p h) (sat_nil p)))
def c2017 : List Lit := [(56, false), (50, true), (57, true), (64, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c870, c234] c2017 (by decide) p (sat_cons (step870 p h) (sat_cons (step234 p h) (sat_nil p)))
def c2018 : List Lit := [(59, true), (50, true), (57, true), (56, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c870, c235] c2018 (by decide) p (sat_cons (step870 p h) (sat_cons (step235 p h) (sat_nil p)))
def c2019 : List Lit := [(66, true), (58, false), (57, true), (75, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c871, c256] c2019 (by decide) p (sat_cons (step871 p h) (sat_cons (step256 p h) (sat_nil p)))
def c2020 : List Lit := [(4, true), (58, false), (57, true), (75, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c871, c257] c2020 (by decide) p (sat_cons (step871 p h) (sat_cons (step257 p h) (sat_nil p)))
def c2021 : List Lit := [(4, true), (58, false), (57, true), (66, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c871, c258] c2021 (by decide) p (sat_cons (step871 p h) (sat_cons (step258 p h) (sat_nil p)))
def c2022 : List Lit := [(60, false), (59, true), (57, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c872, c261] c2022 (by decide) p (sat_cons (step872 p h) (sat_cons (step261 p h) (sat_nil p)))
def c2023 : List Lit := [(55, true), (60, false), (57, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c872, c262] c2023 (by decide) p (sat_cons (step872 p h) (sat_cons (step262 p h) (sat_nil p)))
def c2024 : List Lit := [(63, true), (61, false), (67, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c873, c264] c2024 (by decide) p (sat_cons (step873 p h) (sat_cons (step264 p h) (sat_nil p)))
def c2025 : List Lit := [(54, true), (61, false), (67, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c873, c265] c2025 (by decide) p (sat_cons (step873 p h) (sat_cons (step265 p h) (sat_nil p)))
def c2026 : List Lit := [(61, false), (63, true), (54, true)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c873, c266] c2026 (by decide) p (sat_cons (step873 p h) (sat_cons (step266 p h) (sat_nil p)))
def c2027 : List Lit := [(62, false), (63, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c874, c267] c2027 (by decide) p (sat_cons (step874 p h) (sat_cons (step267 p h) (sat_nil p)))
def c2028 : List Lit := [(62, false), (55, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c874, c268] c2028 (by decide) p (sat_cons (step874 p h) (sat_cons (step268 p h) (sat_nil p)))
def c2029 : List Lit := [(65, false), (66, true), (67, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c875, c277] c2029 (by decide) p (sat_cons (step875 p h) (sat_cons (step277 p h) (sat_nil p)))
def c2030 : List Lit := [(65, false), (64, true), (67, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c875, c278] c2030 (by decide) p (sat_cons (step875 p h) (sat_cons (step278 p h) (sat_nil p)))
def c2031 : List Lit := [(65, false), (64, true), (66, true)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c875, c279] c2031 (by decide) p (sat_cons (step875 p h) (sat_cons (step279 p h) (sat_nil p)))
def c2032 : List Lit := [(70, false), (80, true), (108, true), (75, true)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c876, c305] c2032 (by decide) p (sat_cons (step876 p h) (sat_cons (step305 p h) (sat_nil p)))
def c2033 : List Lit := [(69, true), (80, true), (108, true), (70, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c876, c306] c2033 (by decide) p (sat_cons (step876 p h) (sat_cons (step306 p h) (sat_nil p)))
def c2034 : List Lit := [(69, true), (70, false), (75, true), (108, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c876, c307] c2034 (by decide) p (sat_cons (step876 p h) (sat_cons (step307 p h) (sat_nil p)))
end B112E034
