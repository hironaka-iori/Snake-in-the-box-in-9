import B112E105Inputs
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1929 : List Lit := [(10, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c23, c22] c1929 (by decide) p (sat_cons (step23 p h) (sat_cons (step22 p h) (sat_nil p)))
def c1930 : List Lit := [(5, false), (11, false)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c1929, c23, c24] c1930 (by decide) p (sat_cons (step1929 p h) (sat_cons (step23 p h) (sat_cons (step24 p h) (sat_nil p))))
def c1931 : List Lit := [(134, true), (5, true), (11, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c1929, c25] c1931 (by decide) p (sat_cons (step1929 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1932 : List Lit := [(1, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c943, c1] c1932 (by decide) p (sat_cons (step943 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1933 : List Lit := [(490, false)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1260] c1933 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1260 p h) (sat_nil p)))
def c1934 : List Lit := [(368, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1262] c1934 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1262 p h) (sat_nil p)))
def c1935 : List Lit := [(488, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c1933, c1256] c1935 (by decide) p (sat_cons (step1933 p h) (sat_cons (step1256 p h) (sat_nil p)))
def c1936 : List Lit := [(428, false)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1933, c1259] c1936 (by decide) p (sat_cons (step1933 p h) (sat_cons (step1259 p h) (sat_nil p)))
def c1937 : List Lit := [(366, false)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c1934, c1122] c1937 (by decide) p (sat_cons (step1934 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c1938 : List Lit := [(306, false)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c1934, c1125] c1938 (by decide) p (sat_cons (step1934 p h) (sat_cons (step1125 p h) (sat_nil p)))
def c1939 : List Lit := [(486, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c1935, c1251] c1939 (by decide) p (sat_cons (step1935 p h) (sat_cons (step1251 p h) (sat_nil p)))
def c1940 : List Lit := [(456, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c1935, c1254] c1940 (by decide) p (sat_cons (step1935 p h) (sat_cons (step1254 p h) (sat_nil p)))
def c1941 : List Lit := [(426, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c1936, c1186] c1941 (by decide) p (sat_cons (step1936 p h) (sat_cons (step1186 p h) (sat_nil p)))
def c1942 : List Lit := [(396, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c1936, c1189] c1942 (by decide) p (sat_cons (step1936 p h) (sat_cons (step1189 p h) (sat_nil p)))
def c1943 : List Lit := [(364, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1937, c1117] c1943 (by decide) p (sat_cons (step1937 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c1944 : List Lit := [(334, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c1937, c1120] c1944 (by decide) p (sat_cons (step1937 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c1945 : List Lit := [(304, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c1938, c1057] c1945 (by decide) p (sat_cons (step1938 p h) (sat_cons (step1057 p h) (sat_nil p)))
def c1946 : List Lit := [(276, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c1938, c1060] c1946 (by decide) p (sat_cons (step1938 p h) (sat_cons (step1060 p h) (sat_nil p)))
def c1947 : List Lit := [(484, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c1939, c1246] c1947 (by decide) p (sat_cons (step1939 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c1948 : List Lit := [(470, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1939, c1249] c1948 (by decide) p (sat_cons (step1939 p h) (sat_cons (step1249 p h) (sat_nil p)))
def c1949 : List Lit := [(454, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1940, c1217] c1949 (by decide) p (sat_cons (step1940 p h) (sat_cons (step1217 p h) (sat_nil p)))
def c1950 : List Lit := [(440, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c1940, c1220] c1950 (by decide) p (sat_cons (step1940 p h) (sat_cons (step1220 p h) (sat_nil p)))
def c1951 : List Lit := [(424, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c1941, c1181] c1951 (by decide) p (sat_cons (step1941 p h) (sat_cons (step1181 p h) (sat_nil p)))
def c1952 : List Lit := [(410, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c1941, c1184] c1952 (by decide) p (sat_cons (step1941 p h) (sat_cons (step1184 p h) (sat_nil p)))
def c1953 : List Lit := [(394, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c1942, c1151] c1953 (by decide) p (sat_cons (step1942 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c1954 : List Lit := [(380, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1942, c1154] c1954 (by decide) p (sat_cons (step1942 p h) (sat_cons (step1154 p h) (sat_nil p)))
def c1955 : List Lit := [(362, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c1943, c1112] c1955 (by decide) p (sat_cons (step1943 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c1956 : List Lit := [(348, false)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1943, c1115] c1956 (by decide) p (sat_cons (step1943 p h) (sat_cons (step1115 p h) (sat_nil p)))
def c1957 : List Lit := [(332, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1944, c1081] c1957 (by decide) p (sat_cons (step1944 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c1958 : List Lit := [(302, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1945, c1052] c1958 (by decide) p (sat_cons (step1945 p h) (sat_cons (step1052 p h) (sat_nil p)))
def c1959 : List Lit := [(288, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1945, c1055] c1959 (by decide) p (sat_cons (step1945 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c1960 : List Lit := [(274, false)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1946, c1026] c1960 (by decide) p (sat_cons (step1946 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c1961 : List Lit := [(482, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c1947, c1242] c1961 (by decide) p (sat_cons (step1947 p h) (sat_cons (step1242 p h) (sat_nil p)))
def c1962 : List Lit := [(468, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1948, c1231] c1962 (by decide) p (sat_cons (step1948 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c1963 : List Lit := [(452, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1949, c1213] c1963 (by decide) p (sat_cons (step1949 p h) (sat_cons (step1213 p h) (sat_nil p)))
def c1964 : List Lit := [(438, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c1950, c1198] c1964 (by decide) p (sat_cons (step1950 p h) (sat_cons (step1198 p h) (sat_nil p)))
def c1965 : List Lit := [(422, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c1951, c1177] c1965 (by decide) p (sat_cons (step1951 p h) (sat_cons (step1177 p h) (sat_nil p)))
def c1966 : List Lit := [(408, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1165] c1966 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c1967 : List Lit := [(392, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1953, c1147] c1967 (by decide) p (sat_cons (step1953 p h) (sat_cons (step1147 p h) (sat_nil p)))
def c1968 : List Lit := [(378, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1954, c1134] c1968 (by decide) p (sat_cons (step1954 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1969 : List Lit := [(360, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1108] c1969 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1108 p h) (sat_nil p)))
def c1970 : List Lit := [(340, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1956, c1096] c1970 (by decide) p (sat_cons (step1956 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c1971 : List Lit := [(286, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1959, c1038] c1971 (by decide) p (sat_cons (step1959 p h) (sat_cons (step1038 p h) (sat_nil p)))
def c1972 : List Lit := [(272, false)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1022] c1972 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1022 p h) (sat_nil p)))
def c1973 : List Lit := [(466, false)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1962, c1228] c1973 (by decide) p (sat_cons (step1962 p h) (sat_cons (step1228 p h) (sat_nil p)))
def c1974 : List Lit := [(448, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1963, c1211] c1974 (by decide) p (sat_cons (step1963 p h) (sat_cons (step1211 p h) (sat_nil p)))
def c1975 : List Lit := [(356, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1969, c1106] c1975 (by decide) p (sat_cons (step1969 p h) (sat_cons (step1106 p h) (sat_nil p)))
def c1976 : List Lit := [(284, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1971, c1035] c1976 (by decide) p (sat_cons (step1971 p h) (sat_cons (step1035 p h) (sat_nil p)))
def c1977 : List Lit := [(126, true), (128, true), (130, true), (131, true), (134, true), (137, true), (140, true), (141, true), (144, true), (146, true), (147, true), (149, true), (151, true), (152, true), (155, true), (157, true), (159, true), (161, true), (164, true), (165, true), (168, true), (169, true), (172, true), (173, true), (176, true), (178, true), (180, true), (183, true), (184, true), (185, true), (188, true), (190, true), (192, true), (195, true), (196, true), (198, true), (200, true), (202, true), (205, true), (207, true), (209, true), (212, true), (213, true), (215, true), (217, true), (219, true), (222, true), (223, true), (225, true), (226, true), (229, true), (230, true), (231, true), (232, true), (234, true), (237, true), (239, true), (240, true), (241, true), (246, true), (247, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.TreeRup.prove_clause [c943, c944, c945, c946, c947, c948, c949, c950, c951, c952, c953, c954, c955, c956, c957, c958, c959, c960, c961, c962, c963, c964, c965, c966, c967, c968, c969, c970, c971, c972, c973, c974, c975, c976, c977, c978, c979, c980, c981, c982, c983, c984, c985, c986, c987, c988, c989, c990, c991, c992, c993, c994, c995, c996, c997, c998, c999, c1000, c1001, c1002, c1003, c1004, c1264] c1977 (by decide) p (sat_cons (step943 p h) (sat_cons (step944 p h) (sat_cons (step945 p h) (sat_cons (step946 p h) (sat_cons (step947 p h) (sat_cons (step948 p h) (sat_cons (step949 p h) (sat_cons (step950 p h) (sat_cons (step951 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step954 p h) (sat_cons (step955 p h) (sat_cons (step956 p h) (sat_cons (step957 p h) (sat_cons (step958 p h) (sat_cons (step959 p h) (sat_cons (step960 p h) (sat_cons (step961 p h) (sat_cons (step962 p h) (sat_cons (step963 p h) (sat_cons (step964 p h) (sat_cons (step965 p h) (sat_cons (step966 p h) (sat_cons (step967 p h) (sat_cons (step968 p h) (sat_cons (step969 p h) (sat_cons (step970 p h) (sat_cons (step971 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step974 p h) (sat_cons (step975 p h) (sat_cons (step976 p h) (sat_cons (step977 p h) (sat_cons (step978 p h) (sat_cons (step979 p h) (sat_cons (step980 p h) (sat_cons (step981 p h) (sat_cons (step982 p h) (sat_cons (step983 p h) (sat_cons (step984 p h) (sat_cons (step985 p h) (sat_cons (step986 p h) (sat_cons (step987 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step990 p h) (sat_cons (step991 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step1004 p h) (sat_cons (step1264 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1978 : List Lit := [(1526, true)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1285, c1279, c1268, c1273, c1265, c1266, c17, c19] c1978 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1285 p h) (sat_cons (step1279 p h) (sat_cons (step1268 p h) (sat_cons (step1273 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step17 p h) (sat_cons (step19 p h) (sat_nil p))))))))))
def c1979 : List Lit := [(1557, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1343] c1979 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1343 p h) (sat_nil p)))
def c1980 : List Lit := [(1549, true)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1323, c1327, c1315, c1317, c1303, c1313, c1309, c1295, c1296, c121, c57, c114] c1980 (by decide) p (sat_cons (step1323 p h) (sat_cons (step1327 p h) (sat_cons (step1315 p h) (sat_cons (step1317 p h) (sat_cons (step1303 p h) (sat_cons (step1313 p h) (sat_cons (step1309 p h) (sat_cons (step1295 p h) (sat_cons (step1296 p h) (sat_cons (step121 p h) (sat_cons (step57 p h) (sat_cons (step114 p h) (sat_nil p)))))))))))))
def c1981 : List Lit := [(1558, true)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1980, c1978, c1344] c1981 (by decide) p (sat_cons (step1980 p h) (sat_cons (step1978 p h) (sat_cons (step1344 p h) (sat_nil p))))
def c1982 : List Lit := [(1585, true), (1527, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1944, c1934, c1388, c1392, c1380, c1369, c1371, c1378, c1366, c1367, c161, c184, c1073, c1076, c1077, c1080, c1083, c1118, c1067, c1124, c1065, c1058, c1064, c1027, c160, c1012, c131, c1010, c1270, c1008, c1286, c18, c1279, c1273] c1982 (by decide) p (sat_cons (step1944 p h) (sat_cons (step1934 p h) (sat_cons (step1388 p h) (sat_cons (step1392 p h) (sat_cons (step1380 p h) (sat_cons (step1369 p h) (sat_cons (step1371 p h) (sat_cons (step1378 p h) (sat_cons (step1366 p h) (sat_cons (step1367 p h) (sat_cons (step161 p h) (sat_cons (step184 p h) (sat_cons (step1073 p h) (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1080 p h) (sat_cons (step1083 p h) (sat_cons (step1118 p h) (sat_cons (step1067 p h) (sat_cons (step1124 p h) (sat_cons (step1065 p h) (sat_cons (step1058 p h) (sat_cons (step1064 p h) (sat_cons (step1027 p h) (sat_cons (step160 p h) (sat_cons (step1012 p h) (sat_cons (step131 p h) (sat_cons (step1010 p h) (sat_cons (step1270 p h) (sat_cons (step1008 p h) (sat_cons (step1286 p h) (sat_cons (step18 p h) (sat_cons (step1279 p h) (sat_cons (step1273 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1983 : List Lit := [(1608, true)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1956, c1430, c1434, c1422, c1424, c1408, c1410, c1419, c1417, c1405, c1406, c1402, c1403, c236, c257, c295, c191, c254, c207, c1089, c1084, c1092, c1087, c1095] c1983 (by decide) p (sat_cons (step1956 p h) (sat_cons (step1430 p h) (sat_cons (step1434 p h) (sat_cons (step1422 p h) (sat_cons (step1424 p h) (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1419 p h) (sat_cons (step1417 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step236 p h) (sat_cons (step257 p h) (sat_cons (step295 p h) (sat_cons (step191 p h) (sat_cons (step254 p h) (sat_cons (step207 p h) (sat_cons (step1089 p h) (sat_cons (step1084 p h) (sat_cons (step1092 p h) (sat_cons (step1087 p h) (sat_cons (step1095 p h) (sat_nil p)))))))))))))))))))))))))
def c1984 : List Lit := [(1585, true), (168, true)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1392, c1380, c1369, c1371, c1378, c1366, c1367, c161, c184] c1984 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1392 p h) (sat_cons (step1380 p h) (sat_cons (step1369 p h) (sat_cons (step1371 p h) (sat_cons (step1378 p h) (sat_cons (step1366 p h) (sat_cons (step1367 p h) (sat_cons (step161 p h) (sat_cons (step184 p h) (sat_nil p)))))))))))
def c1985 : List Lit := [(1724, true), (106, true), (104, false), (85, false)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c1659, c1662, c1664, c1660, c1656, c632] c1985 (by decide) p (sat_cons (step1659 p h) (sat_cons (step1662 p h) (sat_cons (step1664 p h) (sat_cons (step1660 p h) (sat_cons (step1656 p h) (sat_cons (step632 p h) (sat_nil p)))))))
def c1986 : List Lit := [(1716, true), (94, true), (95, true), (83, false), (66, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1642, c1652, c1650, c1643, c1644, c1645, c545, c875, c566] c1986 (by decide) p (sat_cons (step1642 p h) (sat_cons (step1652 p h) (sat_cons (step1650 p h) (sat_cons (step1643 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step545 p h) (sat_cons (step875 p h) (sat_cons (step566 p h) (sat_nil p))))))))))
def c1987 : List Lit := [(107, false), (104, false), (209, true), (89, true), (85, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c985, c632, c1903, c477, c488] c1987 (by decide) p (sat_cons (step985 p h) (sat_cons (step632 p h) (sat_cons (step1903 p h) (sat_cons (step477 p h) (sat_cons (step488 p h) (sat_nil p))))))
def c1988 : List Lit := [(1661, true), (79, true), (80, false), (200, true), (83, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c984, c1532, c1534, c1529, c1526, c438, c460, c468] c1988 (by decide) p (sat_cons (step984 p h) (sat_cons (step1532 p h) (sat_cons (step1534 p h) (sat_cons (step1529 p h) (sat_cons (step1526 p h) (sat_cons (step438 p h) (sat_cons (step460 p h) (sat_cons (step468 p h) (sat_nil p)))))))))
def c1989 : List Lit := [(1535, true), (24, false), (76, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1298, c1299, c104] c1989 (by decide) p (sat_cons (step1298 p h) (sat_cons (step1299 p h) (sat_cons (step104 p h) (sat_nil p))))
def c1990 : List Lit := [(113, false), (1688, true), (74, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1575, c1573, c1587, c1561, c1558, c1577, c1570, c493, c733, c519, c515] c1990 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1575 p h) (sat_cons (step1573 p h) (sat_cons (step1587 p h) (sat_cons (step1561 p h) (sat_cons (step1558 p h) (sat_cons (step1577 p h) (sat_cons (step1570 p h) (sat_cons (step493 p h) (sat_cons (step733 p h) (sat_cons (step519 p h) (sat_cons (step515 p h) (sat_nil p)))))))))))))
def c1991 : List Lit := [(24, false), (1536, true), (76, false), (59, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c105, c106, c1300] c1991 (by decide) p (sat_cons (step105 p h) (sat_cons (step106 p h) (sat_cons (step1300 p h) (sat_nil p))))
def c1992 : List Lit := [(56, false), (1755, true), (112, false), (74, false), (122, true), (1743, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c718, c719, c720, c1691, c1695, c1710, c1700, c1715, c1731] c1992 (by decide) p (sat_cons (step718 p h) (sat_cons (step719 p h) (sat_cons (step720 p h) (sat_cons (step1691 p h) (sat_cons (step1695 p h) (sat_cons (step1710 p h) (sat_cons (step1700 p h) (sat_cons (step1715 p h) (sat_cons (step1731 p h) (sat_nil p))))))))))
end B112E105
