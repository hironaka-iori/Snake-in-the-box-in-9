import B112E019Part0002
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1998 : List Lit := [(27, false), (26, true), (24, true), (31, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c864, c116] c1998 (by decide) p (sat_cons (step864 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1999 : List Lit := [(31, true), (28, true), (24, true), (29, false), (87, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c865, c128] c1999 (by decide) p (sat_cons (step865 p h) (sat_cons (step128 p h) (sat_nil p)))
def c2000 : List Lit := [(30, false), (31, true)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c866, c129] c2000 (by decide) p (sat_cons (step866 p h) (sat_cons (step129 p h) (sat_nil p)))
def c2001 : List Lit := [(30, false), (26, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c866, c130] c2001 (by decide) p (sat_cons (step866 p h) (sat_cons (step130 p h) (sat_nil p)))
def c2002 : List Lit := [(32, false), (36, true), (35, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c867, c138] c2002 (by decide) p (sat_cons (step867 p h) (sat_cons (step138 p h) (sat_nil p)))
def c2003 : List Lit := [(32, false), (35, true), (33, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c867, c139] c2003 (by decide) p (sat_cons (step867 p h) (sat_cons (step139 p h) (sat_nil p)))
def c2004 : List Lit := [(34, false), (33, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c868, c143] c2004 (by decide) p (sat_cons (step868 p h) (sat_cons (step143 p h) (sat_nil p)))
def c2005 : List Lit := [(34, false), (24, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c868, c144] c2005 (by decide) p (sat_cons (step868 p h) (sat_cons (step144 p h) (sat_nil p)))
def c2006 : List Lit := [(37, false), (35, true), (38, true)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c869, c152] c2006 (by decide) p (sat_cons (step869 p h) (sat_cons (step152 p h) (sat_nil p)))
def c2007 : List Lit := [(36, true), (35, true), (37, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c869, c153] c2007 (by decide) p (sat_cons (step869 p h) (sat_cons (step153 p h) (sat_nil p)))
def c2008 : List Lit := [(39, false), (98, true), (38, true)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c870, c158] c2008 (by decide) p (sat_cons (step870 p h) (sat_cons (step158 p h) (sat_nil p)))
def c2009 : List Lit := [(39, false), (98, true), (31, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c870, c159] c2009 (by decide) p (sat_cons (step870 p h) (sat_cons (step159 p h) (sat_nil p)))
def c2010 : List Lit := [(40, false), (44, true), (99, true)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c871, c161] c2010 (by decide) p (sat_cons (step871 p h) (sat_cons (step161 p h) (sat_nil p)))
def c2011 : List Lit := [(40, false), (99, true), (41, true)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c871, c162] c2011 (by decide) p (sat_cons (step871 p h) (sat_cons (step162 p h) (sat_nil p)))
def c2012 : List Lit := [(40, false), (44, true), (41, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c871, c163] c2012 (by decide) p (sat_cons (step871 p h) (sat_cons (step163 p h) (sat_nil p)))
def c2013 : List Lit := [(42, false), (52, true), (48, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c872, c173] c2013 (by decide) p (sat_cons (step872 p h) (sat_cons (step173 p h) (sat_nil p)))
def c2014 : List Lit := [(52, true), (43, true), (42, false)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c872, c174] c2014 (by decide) p (sat_cons (step872 p h) (sat_cons (step174 p h) (sat_nil p)))
def c2015 : List Lit := [(42, false), (43, true), (48, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c872, c175] c2015 (by decide) p (sat_cons (step872 p h) (sat_cons (step175 p h) (sat_nil p)))
def c2016 : List Lit := [(45, false), (54, true), (46, true), (41, true)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c873, c196] c2016 (by decide) p (sat_cons (step873 p h) (sat_cons (step196 p h) (sat_nil p)))
def c2017 : List Lit := [(45, false), (54, true), (44, true), (41, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c873, c197] c2017 (by decide) p (sat_cons (step873 p h) (sat_cons (step197 p h) (sat_nil p)))
def c2018 : List Lit := [(45, false), (44, true), (46, true), (41, true)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c873, c198] c2018 (by decide) p (sat_cons (step873 p h) (sat_cons (step198 p h) (sat_nil p)))
def c2019 : List Lit := [(47, false), (48, true), (107, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c874, c213] c2019 (by decide) p (sat_cons (step874 p h) (sat_cons (step213 p h) (sat_nil p)))
def c2020 : List Lit := [(47, false), (107, true), (44, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c874, c214] c2020 (by decide) p (sat_cons (step874 p h) (sat_cons (step214 p h) (sat_nil p)))
def c2021 : List Lit := [(47, false), (48, true), (44, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c874, c215] c2021 (by decide) p (sat_cons (step874 p h) (sat_cons (step215 p h) (sat_nil p)))
def c2022 : List Lit := [(49, false), (55, true), (113, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c875, c224] c2022 (by decide) p (sat_cons (step875 p h) (sat_cons (step224 p h) (sat_nil p)))
def c2023 : List Lit := [(52, true), (113, true), (49, false)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c875, c225] c2023 (by decide) p (sat_cons (step875 p h) (sat_cons (step225 p h) (sat_nil p)))
def c2024 : List Lit := [(50, false), (115, true), (52, true), (18, true), (35, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c876, c233] c2024 (by decide) p (sat_cons (step876 p h) (sat_cons (step233 p h) (sat_nil p)))
def c2025 : List Lit := [(53, false), (51, true), (52, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c877, c247] c2025 (by decide) p (sat_cons (step877 p h) (sat_cons (step247 p h) (sat_nil p)))
def c2026 : List Lit := [(54, true), (55, true), (118, true), (56, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c878, c266] c2026 (by decide) p (sat_cons (step878 p h) (sat_cons (step266 p h) (sat_nil p)))
def c2027 : List Lit := [(55, true), (56, false), (46, true), (118, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c878, c267] c2027 (by decide) p (sat_cons (step878 p h) (sat_cons (step267 p h) (sat_nil p)))
def c2028 : List Lit := [(54, true), (56, false), (46, true), (118, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c878, c268] c2028 (by decide) p (sat_cons (step878 p h) (sat_cons (step268 p h) (sat_nil p)))
def c2029 : List Lit := [(57, false), (54, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c879, c269] c2029 (by decide) p (sat_cons (step879 p h) (sat_cons (step269 p h) (sat_nil p)))
def c2030 : List Lit := [(57, false), (51, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c879, c270] c2030 (by decide) p (sat_cons (step879 p h) (sat_cons (step270 p h) (sat_nil p)))
def c2031 : List Lit := [(58, false), (59, false), (76, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1806, c277] c2031 (by decide) p (sat_cons (step1806 p h) (sat_cons (step277 p h) (sat_nil p)))
def c2032 : List Lit := [(58, true), (76, true), (59, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c880, c278] c2032 (by decide) p (sat_cons (step880 p h) (sat_cons (step278 p h) (sat_nil p)))
def c2033 : List Lit := [(64, true), (66, true), (99, true), (62, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c881, c287] c2033 (by decide) p (sat_cons (step881 p h) (sat_cons (step287 p h) (sat_nil p)))
def c2034 : List Lit := [(62, false), (66, true), (63, true), (99, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c881, c288] c2034 (by decide) p (sat_cons (step881 p h) (sat_cons (step288 p h) (sat_nil p)))
def c2035 : List Lit := [(62, false), (64, true), (63, true), (99, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c881, c289] c2035 (by decide) p (sat_cons (step881 p h) (sat_cons (step289 p h) (sat_nil p)))
def c2036 : List Lit := [(64, true), (65, false), (69, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c882, c299] c2036 (by decide) p (sat_cons (step882 p h) (sat_cons (step299 p h) (sat_nil p)))
def c2037 : List Lit := [(68, false), (66, true), (69, true), (107, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c883, c320] c2037 (by decide) p (sat_cons (step883 p h) (sat_cons (step320 p h) (sat_nil p)))
def c2038 : List Lit := [(64, true), (68, false), (69, true), (107, true)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c883, c321] c2038 (by decide) p (sat_cons (step883 p h) (sat_cons (step321 p h) (sat_nil p)))
def c2039 : List Lit := [(68, false), (107, true), (66, true), (64, true)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c883, c322] c2039 (by decide) p (sat_cons (step883 p h) (sat_cons (step322 p h) (sat_nil p)))
def c2040 : List Lit := [(113, true), (70, false), (76, true)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c884, c332] c2040 (by decide) p (sat_cons (step884 p h) (sat_cons (step332 p h) (sat_nil p)))
def c2041 : List Lit := [(70, false), (113, true), (72, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c884, c333] c2041 (by decide) p (sat_cons (step884 p h) (sat_cons (step333 p h) (sat_nil p)))
def c2042 : List Lit := [(70, false), (76, true), (72, true)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c884, c334] c2042 (by decide) p (sat_cons (step884 p h) (sat_cons (step334 p h) (sat_nil p)))
def c2043 : List Lit := [(73, false), (72, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c885, c345] c2043 (by decide) p (sat_cons (step885 p h) (sat_cons (step345 p h) (sat_nil p)))
def c2044 : List Lit := [(73, false), (71, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c885, c346] c2044 (by decide) p (sat_cons (step885 p h) (sat_cons (step346 p h) (sat_nil p)))
def c2045 : List Lit := [(77, false), (76, true), (75, true), (118, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c887, c381] c2045 (by decide) p (sat_cons (step887 p h) (sat_cons (step381 p h) (sat_nil p)))
def c2046 : List Lit := [(77, false), (76, true), (67, true), (118, true)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c887, c382] c2046 (by decide) p (sat_cons (step887 p h) (sat_cons (step382 p h) (sat_nil p)))
def c2047 : List Lit := [(78, false), (75, true)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c888, c383] c2047 (by decide) p (sat_cons (step888 p h) (sat_cons (step383 p h) (sat_nil p)))
def c2048 : List Lit := [(78, false), (71, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c888, c384] c2048 (by decide) p (sat_cons (step888 p h) (sat_cons (step384 p h) (sat_nil p)))
def c2049 : List Lit := [(79, false), (82, true), (81, true), (85, true), (99, true)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c889, c395] c2049 (by decide) p (sat_cons (step889 p h) (sat_cons (step395 p h) (sat_nil p)))
def c2050 : List Lit := [(79, false), (80, true), (81, true), (99, true), (82, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c889, c396] c2050 (by decide) p (sat_cons (step889 p h) (sat_cons (step396 p h) (sat_nil p)))
def c2051 : List Lit := [(81, true), (89, true), (84, false), (82, true)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c891, c435] c2051 (by decide) p (sat_cons (step891 p h) (sat_cons (step435 p h) (sat_nil p)))
def c2052 : List Lit := [(88, false), (89, true), (107, true), (85, true)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c893, c473] c2052 (by decide) p (sat_cons (step893 p h) (sat_cons (step473 p h) (sat_nil p)))
def c2053 : List Lit := [(88, false), (89, true), (82, true), (107, true)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c893, c474] c2053 (by decide) p (sat_cons (step893 p h) (sat_cons (step474 p h) (sat_nil p)))
def c2054 : List Lit := [(88, false), (82, true), (85, true), (107, true)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c893, c475] c2054 (by decide) p (sat_cons (step893 p h) (sat_cons (step475 p h) (sat_nil p)))
def c2055 : List Lit := [(90, false), (92, true), (113, true)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c894, c489] c2055 (by decide) p (sat_cons (step894 p h) (sat_cons (step489 p h) (sat_nil p)))
def c2056 : List Lit := [(90, false), (113, true), (81, true)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c894, c490] c2056 (by decide) p (sat_cons (step894 p h) (sat_cons (step490 p h) (sat_nil p)))
def c2057 : List Lit := [(93, false), (98, true), (92, true)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c895, c505] c2057 (by decide) p (sat_cons (step895 p h) (sat_cons (step505 p h) (sat_nil p)))
def c2058 : List Lit := [(93, false), (98, true), (91, true)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c895, c506] c2058 (by decide) p (sat_cons (step895 p h) (sat_cons (step506 p h) (sat_nil p)))
def c2059 : List Lit := [(36, true), (94, false), (116, true), (95, true)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c896, c511] c2059 (by decide) p (sat_cons (step896 p h) (sat_cons (step511 p h) (sat_nil p)))
def c2060 : List Lit := [(36, true), (94, false), (85, true), (95, true)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c896, c512] c2060 (by decide) p (sat_cons (step896 p h) (sat_cons (step512 p h) (sat_nil p)))
def c2061 : List Lit := [(98, true), (95, true), (118, true), (96, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c897, c522] c2061 (by decide) p (sat_cons (step897 p h) (sat_cons (step522 p h) (sat_nil p)))
end B112E019
