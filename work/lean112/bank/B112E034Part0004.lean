import B112E034Part0003
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2035 : List Lit := [(76, true), (72, false), (71, true), (110, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c877, c314] c2035 (by decide) p (sat_cons (step877 p h) (sat_cons (step314 p h) (sat_nil p)))
def c2036 : List Lit := [(54, true), (76, true), (72, false), (110, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c877, c315] c2036 (by decide) p (sat_cons (step877 p h) (sat_cons (step315 p h) (sat_nil p)))
def c2037 : List Lit := [(54, true), (72, false), (71, true), (110, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c877, c316] c2037 (by decide) p (sat_cons (step877 p h) (sat_cons (step316 p h) (sat_nil p)))
def c2038 : List Lit := [(76, true), (54, true), (72, false), (71, true)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c877, c317] c2038 (by decide) p (sat_cons (step877 p h) (sat_cons (step317 p h) (sat_nil p)))
def c2039 : List Lit := [(76, true), (114, true), (73, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c878, c318] c2039 (by decide) p (sat_cons (step878 p h) (sat_cons (step318 p h) (sat_nil p)))
def c2040 : List Lit := [(114, true), (75, true), (73, false)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c878, c319] c2040 (by decide) p (sat_cons (step878 p h) (sat_cons (step319 p h) (sat_nil p)))
def c2041 : List Lit := [(76, true), (75, true), (73, false)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c878, c320] c2041 (by decide) p (sat_cons (step878 p h) (sat_cons (step320 p h) (sat_nil p)))
def c2042 : List Lit := [(69, true), (115, true), (74, false), (75, true)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c879, c324] c2042 (by decide) p (sat_cons (step879 p h) (sat_cons (step324 p h) (sat_nil p)))
def c2043 : List Lit := [(57, true), (115, true), (74, false), (75, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c879, c325] c2043 (by decide) p (sat_cons (step879 p h) (sat_cons (step325 p h) (sat_nil p)))
def c2044 : List Lit := [(57, true), (69, true), (74, false), (115, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c879, c326] c2044 (by decide) p (sat_cons (step879 p h) (sat_cons (step326 p h) (sat_nil p)))
def c2045 : List Lit := [(57, true), (69, true), (74, false), (75, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c879, c327] c2045 (by decide) p (sat_cons (step879 p h) (sat_cons (step327 p h) (sat_nil p)))
def c2046 : List Lit := [(85, true), (76, true), (77, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c880, c346] c2046 (by decide) p (sat_cons (step880 p h) (sat_cons (step346 p h) (sat_nil p)))
def c2047 : List Lit := [(85, true), (75, true), (77, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c880, c347] c2047 (by decide) p (sat_cons (step880 p h) (sat_cons (step347 p h) (sat_nil p)))
def c2048 : List Lit := [(76, true), (75, true), (77, false)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c880, c348] c2048 (by decide) p (sat_cons (step880 p h) (sat_cons (step348 p h) (sat_nil p)))
def c2049 : List Lit := [(80, true), (79, false), (119, true)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c881, c352] c2049 (by decide) p (sat_cons (step881 p h) (sat_cons (step352 p h) (sat_nil p)))
def c2050 : List Lit := [(78, true), (79, false), (119, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c881, c353] c2050 (by decide) p (sat_cons (step881 p h) (sat_cons (step353 p h) (sat_nil p)))
def c2051 : List Lit := [(80, true), (78, true), (79, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c881, c354] c2051 (by decide) p (sat_cons (step881 p h) (sat_cons (step354 p h) (sat_nil p)))
def c2052 : List Lit := [(81, false), (78, true), (71, true)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c882, c361] c2052 (by decide) p (sat_cons (step882 p h) (sat_cons (step361 p h) (sat_nil p)))
def c2053 : List Lit := [(84, false), (85, true)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c883, c367] c2053 (by decide) p (sat_cons (step883 p h) (sat_cons (step367 p h) (sat_nil p)))
def c2054 : List Lit := [(84, false), (83, true)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c883, c368] c2054 (by decide) p (sat_cons (step883 p h) (sat_cons (step368 p h) (sat_nil p)))
def c2055 : List Lit := [(14, true), (87, true), (106, true), (86, false), (90, true), (88, true), (96, true)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c884, c387] c2055 (by decide) p (sat_cons (step884 p h) (sat_cons (step387 p h) (sat_nil p)))
def c2056 : List Lit := [(91, true), (89, false), (88, true), (108, true), (99, true)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c885, c430] c2056 (by decide) p (sat_cons (step885 p h) (sat_cons (step430 p h) (sat_nil p)))
def c2057 : List Lit := [(91, true), (99, true), (108, true), (89, false), (87, true)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c885, c431] c2057 (by decide) p (sat_cons (step885 p h) (sat_cons (step431 p h) (sat_nil p)))
def c2058 : List Lit := [(99, true), (87, true), (89, false), (88, true), (108, true)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c885, c432] c2058 (by decide) p (sat_cons (step885 p h) (sat_cons (step432 p h) (sat_nil p)))
def c2059 : List Lit := [(91, true), (89, false), (108, true), (88, true), (87, true)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c885, c433] c2059 (by decide) p (sat_cons (step885 p h) (sat_cons (step433 p h) (sat_nil p)))
def c2060 : List Lit := [(91, true), (87, true), (89, false), (99, true), (88, true)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c885, c434] c2060 (by decide) p (sat_cons (step885 p h) (sat_cons (step434 p h) (sat_nil p)))
def c2061 : List Lit := [(114, true), (92, false), (94, true), (87, true)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c886, c450] c2061 (by decide) p (sat_cons (step886 p h) (sat_cons (step450 p h) (sat_nil p)))
def c2062 : List Lit := [(20, true), (114, true), (94, true), (92, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c886, c451] c2062 (by decide) p (sat_cons (step886 p h) (sat_cons (step451 p h) (sat_nil p)))
def c2063 : List Lit := [(20, true), (92, false), (114, true), (87, true)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c886, c452] c2063 (by decide) p (sat_cons (step886 p h) (sat_cons (step452 p h) (sat_nil p)))
def c2064 : List Lit := [(20, true), (94, true), (87, true), (92, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c886, c453] c2064 (by decide) p (sat_cons (step886 p h) (sat_cons (step453 p h) (sat_nil p)))
def c2065 : List Lit := [(101, true), (93, false), (88, true), (115, true)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c887, c457] c2065 (by decide) p (sat_cons (step887 p h) (sat_cons (step457 p h) (sat_nil p)))
def c2066 : List Lit := [(57, true), (93, false), (115, true), (101, true)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c887, c458] c2066 (by decide) p (sat_cons (step887 p h) (sat_cons (step458 p h) (sat_nil p)))
def c2067 : List Lit := [(57, true), (93, false), (88, true), (115, true)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c887, c459] c2067 (by decide) p (sat_cons (step887 p h) (sat_cons (step459 p h) (sat_nil p)))
def c2068 : List Lit := [(57, true), (101, true), (93, false), (88, true)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c887, c460] c2068 (by decide) p (sat_cons (step887 p h) (sat_cons (step460 p h) (sat_nil p)))
def c2069 : List Lit := [(105, true), (94, true), (95, false)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c888, c468] c2069 (by decide) p (sat_cons (step888 p h) (sat_cons (step468 p h) (sat_nil p)))
def c2070 : List Lit := [(91, true), (95, false), (105, true)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c888, c469] c2070 (by decide) p (sat_cons (step888 p h) (sat_cons (step469 p h) (sat_nil p)))
def c2071 : List Lit := [(94, true), (91, true), (95, false)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c888, c470] c2071 (by decide) p (sat_cons (step888 p h) (sat_cons (step470 p h) (sat_nil p)))
def c2072 : List Lit := [(99, true), (119, true), (97, false), (96, true)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c889, c478] c2072 (by decide) p (sat_cons (step889 p h) (sat_cons (step478 p h) (sat_nil p)))
def c2073 : List Lit := [(87, true), (99, true), (119, true), (97, false)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c889, c479] c2073 (by decide) p (sat_cons (step889 p h) (sat_cons (step479 p h) (sat_nil p)))
def c2074 : List Lit := [(87, true), (119, true), (96, true), (97, false)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c889, c480] c2074 (by decide) p (sat_cons (step889 p h) (sat_cons (step480 p h) (sat_nil p)))
def c2075 : List Lit := [(99, true), (87, true), (96, true), (97, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c889, c481] c2075 (by decide) p (sat_cons (step889 p h) (sat_cons (step481 p h) (sat_nil p)))
def c2076 : List Lit := [(101, true), (99, true), (98, false), (96, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c890, c484] c2076 (by decide) p (sat_cons (step890 p h) (sat_cons (step484 p h) (sat_nil p)))
def c2077 : List Lit := [(101, true), (99, true), (98, false), (88, true)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c890, c485] c2077 (by decide) p (sat_cons (step890 p h) (sat_cons (step485 p h) (sat_nil p)))
def c2078 : List Lit := [(101, true), (88, true), (96, true), (98, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c890, c486] c2078 (by decide) p (sat_cons (step890 p h) (sat_cons (step486 p h) (sat_nil p)))
def c2079 : List Lit := [(99, true), (88, true), (98, false), (96, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c890, c487] c2079 (by decide) p (sat_cons (step890 p h) (sat_cons (step487 p h) (sat_nil p)))
def c2080 : List Lit := [(96, true), (100, false), (102, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c891, c494] c2080 (by decide) p (sat_cons (step891 p h) (sat_cons (step494 p h) (sat_nil p)))
def c2081 : List Lit := [(90, true), (100, false), (102, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c891, c495] c2081 (by decide) p (sat_cons (step891 p h) (sat_cons (step495 p h) (sat_nil p)))
def c2082 : List Lit := [(90, true), (96, true), (100, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c891, c496] c2082 (by decide) p (sat_cons (step891 p h) (sat_cons (step496 p h) (sat_nil p)))
def c2083 : List Lit := [(105, true), (104, false), (102, true)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c892, c526] c2083 (by decide) p (sat_cons (step892 p h) (sat_cons (step526 p h) (sat_nil p)))
def c2084 : List Lit := [(101, true), (104, false), (105, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c892, c527] c2084 (by decide) p (sat_cons (step892 p h) (sat_cons (step527 p h) (sat_nil p)))
def c2085 : List Lit := [(101, true), (104, false), (102, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c892, c528] c2085 (by decide) p (sat_cons (step892 p h) (sat_cons (step528 p h) (sat_nil p)))
def c2086 : List Lit := [(69, true), (108, true), (88, true), (107, false), (115, true), (111, true), (106, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c893, c557] c2086 (by decide) p (sat_cons (step893 p h) (sat_cons (step557 p h) (sat_nil p)))
def c2087 : List Lit := [(32, true), (108, true), (106, true), (107, false), (115, true), (88, true), (111, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c893, c558] c2087 (by decide) p (sat_cons (step893 p h) (sat_cons (step558 p h) (sat_nil p)))
def c2088 : List Lit := [(69, true), (32, true), (107, false), (108, true), (106, true), (88, true), (115, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c893, c559] c2088 (by decide) p (sat_cons (step893 p h) (sat_cons (step559 p h) (sat_nil p)))
def c2089 : List Lit := [(123, true), (110, true), (111, true), (112, false), (108, true)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c894, c638] c2089 (by decide) p (sat_cons (step894 p h) (sat_cons (step638 p h) (sat_nil p)))
def c2090 : List Lit := [(123, true), (91, true), (112, false), (108, true), (111, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c894, c639] c2090 (by decide) p (sat_cons (step894 p h) (sat_cons (step639 p h) (sat_nil p)))
def c2091 : List Lit := [(123, true), (91, true), (108, true), (110, true), (112, false)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c894, c640] c2091 (by decide) p (sat_cons (step894 p h) (sat_cons (step640 p h) (sat_nil p)))
def c2092 : List Lit := [(110, true), (91, true), (108, true), (111, true), (112, false)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c894, c641] c2092 (by decide) p (sat_cons (step894 p h) (sat_cons (step641 p h) (sat_nil p)))
def c2093 : List Lit := [(124, true), (114, true), (115, true), (116, true), (113, false)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c895, c646] c2093 (by decide) p (sat_cons (step895 p h) (sat_cons (step646 p h) (sat_nil p)))
def c2094 : List Lit := [(124, true), (116, true), (106, true), (113, false), (115, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c895, c647] c2094 (by decide) p (sat_cons (step895 p h) (sat_cons (step647 p h) (sat_nil p)))
def c2095 : List Lit := [(124, true), (116, true), (114, true), (106, true), (113, false)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c895, c648] c2095 (by decide) p (sat_cons (step895 p h) (sat_cons (step648 p h) (sat_nil p)))
def c2096 : List Lit := [(124, true), (114, true), (113, false), (115, true), (106, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c895, c649] c2096 (by decide) p (sat_cons (step895 p h) (sat_cons (step649 p h) (sat_nil p)))
def c2097 : List Lit := [(114, true), (116, true), (113, false), (115, true), (106, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c895, c650] c2097 (by decide) p (sat_cons (step895 p h) (sat_cons (step650 p h) (sat_nil p)))
def c2098 : List Lit := [(116, true), (118, false), (115, true)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c896, c740] c2098 (by decide) p (sat_cons (step896 p h) (sat_cons (step740 p h) (sat_nil p)))
end B112E034
