import B112E105Part0003
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2185 : List Lit := [(78, true), (118, false), (60, true), (95, true), (106, true), (115, true), (117, true)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c1000, c857] c2185 (by decide) p (sat_cons (step1000 p h) (sat_cons (step857 p h) (sat_nil p)))
def c2186 : List Lit := [(119, false), (123, true), (117, true), (116, true), (107, true)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c1001, c868] c2186 (by decide) p (sat_cons (step1001 p h) (sat_cons (step868 p h) (sat_nil p)))
def c2187 : List Lit := [(119, false), (123, true), (61, true), (117, true), (107, true)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c1001, c869] c2187 (by decide) p (sat_cons (step1001 p h) (sat_cons (step869 p h) (sat_nil p)))
def c2188 : List Lit := [(119, false), (61, true), (117, true), (107, true), (116, true)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c1001, c870] c2188 (by decide) p (sat_cons (step1001 p h) (sat_cons (step870 p h) (sat_nil p)))
def c2189 : List Lit := [(120, false), (123, true), (116, true)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c1002, c872] c2189 (by decide) p (sat_cons (step1002 p h) (sat_cons (step872 p h) (sat_nil p)))
def c2190 : List Lit := [(120, false), (99, true), (123, true)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c1002, c873] c2190 (by decide) p (sat_cons (step1002 p h) (sat_cons (step873 p h) (sat_nil p)))
def c2191 : List Lit := [(99, true), (120, false), (116, true)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c1002, c874] c2191 (by decide) p (sat_cons (step1002 p h) (sat_cons (step874 p h) (sat_nil p)))
def c2192 : List Lit := [(101, true), (83, true), (121, false), (110, true), (117, true), (122, true), (123, true)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c1003, c910] c2192 (by decide) p (sat_cons (step1003 p h) (sat_cons (step910 p h) (sat_nil p)))
def c2193 : List Lit := [(101, true), (123, true), (66, true), (110, true), (117, true), (122, true), (121, false)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c1003, c911] c2193 (by decide) p (sat_cons (step1003 p h) (sat_cons (step911 p h) (sat_nil p)))
def c2194 : List Lit := [(83, true), (117, true), (121, false), (123, true), (110, true), (66, true), (122, true)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c1003, c912] c2194 (by decide) p (sat_cons (step1003 p h) (sat_cons (step912 p h) (sat_nil p)))
def c2195 : List Lit := [(101, true), (123, true), (83, true), (66, true), (117, true), (122, true), (121, false)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c1003, c913] c2195 (by decide) p (sat_cons (step1003 p h) (sat_cons (step913 p h) (sat_nil p)))
def c2196 : List Lit := [(101, true), (122, true), (83, true), (66, true), (110, true), (123, true), (121, false)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c1003, c914] c2196 (by decide) p (sat_cons (step1003 p h) (sat_cons (step914 p h) (sat_nil p)))
def c2197 : List Lit := [(101, true), (83, true), (121, false), (66, true), (110, true), (117, true), (123, true)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c1003, c915] c2197 (by decide) p (sat_cons (step1003 p h) (sat_cons (step915 p h) (sat_nil p)))
def c2198 : List Lit := [(101, true), (83, true), (121, false), (66, true), (110, true), (117, true), (122, true)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c1003, c916] c2198 (by decide) p (sat_cons (step1003 p h) (sat_cons (step916 p h) (sat_nil p)))
def c2199 : List Lit := [(124, false), (122, true), (123, true)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c1004, c940] c2199 (by decide) p (sat_cons (step1004 p h) (sat_cons (step940 p h) (sat_nil p)))
def c2200 : List Lit := [(124, false), (123, true), (113, true)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c1004, c941] c2200 (by decide) p (sat_cons (step1004 p h) (sat_cons (step941 p h) (sat_nil p)))
def c2201 : List Lit := [(124, false), (122, true), (113, true)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c1004, c942] c2201 (by decide) p (sat_cons (step1004 p h) (sat_cons (step942 p h) (sat_nil p)))
def c2202 : List Lit := [(267, false), (269, false)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c1972, c1020] c2202 (by decide) p (sat_cons (step1972 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c2203 : List Lit := [(265, false), (271, false)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1024] c2203 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c2204 : List Lit := [(259, false), (273, false)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c1946, c1028] c2204 (by decide) p (sat_cons (step1946 p h) (sat_cons (step1028 p h) (sat_nil p)))
def c2205 : List Lit := [(146, false), (147, false)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c1976, c1033] c2205 (by decide) p (sat_cons (step1976 p h) (sat_cons (step1033 p h) (sat_nil p)))
def c2206 : List Lit := [(293, false), (299, false)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c1958, c1050] c2206 (by decide) p (sat_cons (step1958 p h) (sat_cons (step1050 p h) (sat_nil p)))
def c2207 : List Lit := [(287, false), (301, false)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c1945, c1054] c2207 (by decide) p (sat_cons (step1945 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c2208 : List Lit := [(275, false), (303, false)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c1938, c1059] c2208 (by decide) p (sat_cons (step1938 p h) (sat_cons (step1059 p h) (sat_nil p)))
def c2209 : List Lit := [(323, false), (329, false)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c1957, c1079] c2209 (by decide) p (sat_cons (step1957 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c2210 : List Lit := [(317, false), (331, false)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c1944, c1083] c2210 (by decide) p (sat_cons (step1944 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c2211 : List Lit := [(335, false), (337, false)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1088] c2211 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1088 p h) (sat_nil p)))
def c2212 : List Lit := [(339, false), (345, false)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c1956, c1095] c2212 (by decide) p (sat_cons (step1956 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c2213 : List Lit := [(183, false), (184, false)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c1975, c1101] c2213 (by decide) p (sat_cons (step1975 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c2214 : List Lit := [(355, false), (357, false)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c1969, c1105] c2214 (by decide) p (sat_cons (step1969 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c2215 : List Lit := [(353, false), (359, false)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1110] c2215 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1110 p h) (sat_nil p)))
def c2216 : List Lit := [(347, false), (361, false)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c1943, c1114] c2216 (by decide) p (sat_cons (step1943 p h) (sat_cons (step1114 p h) (sat_nil p)))
def c2217 : List Lit := [(363, false), (333, false)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c1937, c1119] c2217 (by decide) p (sat_cons (step1937 p h) (sat_cons (step1119 p h) (sat_nil p)))
def c2218 : List Lit := [(305, false), (365, false)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c1934, c1124] c2218 (by decide) p (sat_cons (step1934 p h) (sat_cons (step1124 p h) (sat_nil p)))
def c2219 : List Lit := [(373, false), (375, false)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c1968, c1132] c2219 (by decide) p (sat_cons (step1968 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c2220 : List Lit := [(371, false), (377, false)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c1954, c1136] c2220 (by decide) p (sat_cons (step1954 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c2221 : List Lit := [(387, false), (389, false)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c1967, c1145] c2221 (by decide) p (sat_cons (step1967 p h) (sat_cons (step1145 p h) (sat_nil p)))
def c2222 : List Lit := [(385, false), (391, false)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c1953, c1149] c2222 (by decide) p (sat_cons (step1953 p h) (sat_cons (step1149 p h) (sat_nil p)))
def c2223 : List Lit := [(379, false), (393, false)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c1942, c1153] c2223 (by decide) p (sat_cons (step1942 p h) (sat_cons (step1153 p h) (sat_nil p)))
def c2224 : List Lit := [(403, false), (405, false)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c1966, c1163] c2224 (by decide) p (sat_cons (step1966 p h) (sat_cons (step1163 p h) (sat_nil p)))
def c2225 : List Lit := [(401, false), (407, false)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1167] c2225 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1167 p h) (sat_nil p)))
def c2226 : List Lit := [(417, false), (419, false)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c1965, c1175] c2226 (by decide) p (sat_cons (step1965 p h) (sat_cons (step1175 p h) (sat_nil p)))
def c2227 : List Lit := [(415, false), (421, false)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c1951, c1179] c2227 (by decide) p (sat_cons (step1951 p h) (sat_cons (step1179 p h) (sat_nil p)))
def c2228 : List Lit := [(409, false), (423, false)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c1941, c1183] c2228 (by decide) p (sat_cons (step1941 p h) (sat_cons (step1183 p h) (sat_nil p)))
def c2229 : List Lit := [(395, false), (425, false)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c1936, c1188] c2229 (by decide) p (sat_cons (step1936 p h) (sat_cons (step1188 p h) (sat_nil p)))
def c2230 : List Lit := [(433, false), (435, false)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c1964, c1196] c2230 (by decide) p (sat_cons (step1964 p h) (sat_cons (step1196 p h) (sat_nil p)))
def c2231 : List Lit := [(229, false), (230, false)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c1974, c1205] c2231 (by decide) p (sat_cons (step1974 p h) (sat_cons (step1205 p h) (sat_nil p)))
def c2232 : List Lit := [(447, false), (449, false)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c1963, c1210] c2232 (by decide) p (sat_cons (step1963 p h) (sat_cons (step1210 p h) (sat_nil p)))
def c2233 : List Lit := [(445, false), (451, false)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c1949, c1215] c2233 (by decide) p (sat_cons (step1949 p h) (sat_cons (step1215 p h) (sat_nil p)))
def c2234 : List Lit := [(439, false), (453, false)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c1940, c1219] c2234 (by decide) p (sat_cons (step1940 p h) (sat_cons (step1219 p h) (sat_nil p)))
def c2235 : List Lit := [(239, false), (240, false)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c1973, c1226] c2235 (by decide) p (sat_cons (step1973 p h) (sat_cons (step1226 p h) (sat_nil p)))
def c2236 : List Lit := [(461, false), (467, false)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c1948, c1233] c2236 (by decide) p (sat_cons (step1948 p h) (sat_cons (step1233 p h) (sat_nil p)))
def c2237 : List Lit := [(477, false), (479, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c1961, c1240] c2237 (by decide) p (sat_cons (step1961 p h) (sat_cons (step1240 p h) (sat_nil p)))
def c2238 : List Lit := [(475, false), (481, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c1947, c1244] c2238 (by decide) p (sat_cons (step1947 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c2239 : List Lit := [(469, false), (483, false)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c1939, c1248] c2239 (by decide) p (sat_cons (step1939 p h) (sat_cons (step1248 p h) (sat_nil p)))
def c2240 : List Lit := [(455, false), (485, false)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c1935, c1253] c2240 (by decide) p (sat_cons (step1935 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c2241 : List Lit := [(427, false), (487, false)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c1933, c1258] c2241 (by decide) p (sat_cons (step1933 p h) (sat_cons (step1258 p h) (sat_nil p)))
def c2242 : List Lit := [(367, false), (489, false)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1261] c2242 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c2243 : List Lit := [(1550, false), (1559, true)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1345] c2243 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1345 p h) (sat_nil p)))
def c2244 : List Lit := [(1551, false), (1560, true)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1346] c2244 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1346 p h) (sat_nil p)))
def c2245 : List Lit := [(1552, false), (1561, true)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1347] c2245 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1347 p h) (sat_nil p)))
def c2246 : List Lit := [(1553, false), (1562, true)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1348] c2246 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1348 p h) (sat_nil p)))
def c2247 : List Lit := [(1527, false), (1559, true)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c1980, c1349] c2247 (by decide) p (sat_cons (step1980 p h) (sat_cons (step1349 p h) (sat_nil p)))
def c2248 : List Lit := [(1560, true), (1528, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1980, c1355] c2248 (by decide) p (sat_cons (step1980 p h) (sat_cons (step1355 p h) (sat_nil p)))
end B112E105
