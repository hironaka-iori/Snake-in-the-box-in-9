import B112E055Inputs
namespace B112E055
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1942 : List Lit := [(67, true)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c955, c954] c1942 (by decide) p (sat_cons (step955 p h) (sat_cons (step954 p h) (sat_nil p)))
def c1943 : List Lit := [(61, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c986, c372] c1943 (by decide) p (sat_cons (step986 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1944 : List Lit := [(66, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c989, c387] c1944 (by decide) p (sat_cons (step989 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1945 : List Lit := [(68, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c990, c389] c1945 (by decide) p (sat_cons (step990 p h) (sat_cons (step389 p h) (sat_nil p)))
def c1946 : List Lit := [(506, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1292] c1946 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1292 p h) (sat_nil p)))
def c1947 : List Lit := [(380, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1294] c1947 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1294 p h) (sat_nil p)))
def c1948 : List Lit := [(504, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1946, c1288] c1948 (by decide) p (sat_cons (step1946 p h) (sat_cons (step1288 p h) (sat_nil p)))
def c1949 : List Lit := [(442, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1946, c1291] c1949 (by decide) p (sat_cons (step1946 p h) (sat_cons (step1291 p h) (sat_nil p)))
def c1950 : List Lit := [(378, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c1947, c1144] c1950 (by decide) p (sat_cons (step1947 p h) (sat_cons (step1144 p h) (sat_nil p)))
def c1951 : List Lit := [(316, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c1947, c1147] c1951 (by decide) p (sat_cons (step1947 p h) (sat_cons (step1147 p h) (sat_nil p)))
def c1952 : List Lit := [(502, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c1948, c1283] c1952 (by decide) p (sat_cons (step1948 p h) (sat_cons (step1283 p h) (sat_nil p)))
def c1953 : List Lit := [(472, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c1948, c1286] c1953 (by decide) p (sat_cons (step1948 p h) (sat_cons (step1286 p h) (sat_nil p)))
def c1954 : List Lit := [(440, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1949, c1208] c1954 (by decide) p (sat_cons (step1949 p h) (sat_cons (step1208 p h) (sat_nil p)))
def c1955 : List Lit := [(410, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c1949, c1211] c1955 (by decide) p (sat_cons (step1949 p h) (sat_cons (step1211 p h) (sat_nil p)))
def c1956 : List Lit := [(376, false)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1950, c1139] c1956 (by decide) p (sat_cons (step1950 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c1957 : List Lit := [(346, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1950, c1142] c1957 (by decide) p (sat_cons (step1950 p h) (sat_cons (step1142 p h) (sat_nil p)))
def c1958 : List Lit := [(314, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1951, c1080] c1958 (by decide) p (sat_cons (step1951 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c1959 : List Lit := [(284, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1951, c1083] c1959 (by decide) p (sat_cons (step1951 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c1960 : List Lit := [(500, false)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1278] c1960 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1278 p h) (sat_nil p)))
def c1961 : List Lit := [(486, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1281] c1961 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1281 p h) (sat_nil p)))
def c1962 : List Lit := [(470, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1953, c1246] c1962 (by decide) p (sat_cons (step1953 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c1963 : List Lit := [(456, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1953, c1249] c1963 (by decide) p (sat_cons (step1953 p h) (sat_cons (step1249 p h) (sat_nil p)))
def c1964 : List Lit := [(438, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c1954, c1203] c1964 (by decide) p (sat_cons (step1954 p h) (sat_cons (step1203 p h) (sat_nil p)))
def c1965 : List Lit := [(424, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c1954, c1206] c1965 (by decide) p (sat_cons (step1954 p h) (sat_cons (step1206 p h) (sat_nil p)))
def c1966 : List Lit := [(408, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1175] c1966 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1175 p h) (sat_nil p)))
def c1967 : List Lit := [(394, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1178] c1967 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1178 p h) (sat_nil p)))
def c1968 : List Lit := [(374, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1956, c1134] c1968 (by decide) p (sat_cons (step1956 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1969 : List Lit := [(360, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1956, c1137] c1969 (by decide) p (sat_cons (step1956 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c1970 : List Lit := [(344, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1957, c1105] c1970 (by decide) p (sat_cons (step1957 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c1971 : List Lit := [(330, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1957, c1108] c1971 (by decide) p (sat_cons (step1957 p h) (sat_cons (step1108 p h) (sat_nil p)))
def c1972 : List Lit := [(312, false)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1958, c1075] c1972 (by decide) p (sat_cons (step1958 p h) (sat_cons (step1075 p h) (sat_nil p)))
def c1973 : List Lit := [(298, false)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1958, c1078] c1973 (by decide) p (sat_cons (step1958 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c1974 : List Lit := [(282, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1959, c1043] c1974 (by decide) p (sat_cons (step1959 p h) (sat_cons (step1043 p h) (sat_nil p)))
def c1975 : List Lit := [(268, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1959, c1046] c1975 (by decide) p (sat_cons (step1959 p h) (sat_cons (step1046 p h) (sat_nil p)))
def c1976 : List Lit := [(498, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1273] c1976 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1273 p h) (sat_nil p)))
def c1977 : List Lit := [(492, false)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1276] c1977 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1276 p h) (sat_nil p)))
def c1978 : List Lit := [(468, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1962, c1241] c1978 (by decide) p (sat_cons (step1962 p h) (sat_cons (step1241 p h) (sat_nil p)))
def c1979 : List Lit := [(462, false)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c1962, c1244] c1979 (by decide) p (sat_cons (step1962 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c1980 : List Lit := [(454, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1963, c1223] c1980 (by decide) p (sat_cons (step1963 p h) (sat_cons (step1223 p h) (sat_nil p)))
def c1981 : List Lit := [(448, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1963, c1226] c1981 (by decide) p (sat_cons (step1963 p h) (sat_cons (step1226 p h) (sat_nil p)))
def c1982 : List Lit := [(436, false)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1964, c1200] c1982 (by decide) p (sat_cons (step1964 p h) (sat_cons (step1200 p h) (sat_nil p)))
def c1983 : List Lit := [(416, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1965, c1191] c1983 (by decide) p (sat_cons (step1965 p h) (sat_cons (step1191 p h) (sat_nil p)))
def c1984 : List Lit := [(400, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1966, c1173] c1984 (by decide) p (sat_cons (step1966 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c1985 : List Lit := [(392, false)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c1967, c1158] c1985 (by decide) p (sat_cons (step1967 p h) (sat_cons (step1158 p h) (sat_nil p)))
def c1986 : List Lit := [(366, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1968, c1132] c1986 (by decide) p (sat_cons (step1968 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c1987 : List Lit := [(358, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1969, c1120] c1987 (by decide) p (sat_cons (step1969 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c1988 : List Lit := [(304, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1972, c1073] c1988 (by decide) p (sat_cons (step1972 p h) (sat_cons (step1073 p h) (sat_nil p)))
def c1989 : List Lit := [(290, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1973, c1060] c1989 (by decide) p (sat_cons (step1973 p h) (sat_cons (step1060 p h) (sat_nil p)))
def c1990 : List Lit := [(280, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1974, c1039] c1990 (by decide) p (sat_cons (step1974 p h) (sat_cons (step1039 p h) (sat_nil p)))
def c1991 : List Lit := [(260, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1975, c1029] c1991 (by decide) p (sat_cons (step1975 p h) (sat_cons (step1029 p h) (sat_nil p)))
def c1992 : List Lit := [(488, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1977, c1266] c1992 (by decide) p (sat_cons (step1977 p h) (sat_cons (step1266 p h) (sat_nil p)))
def c1993 : List Lit := [(466, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1237] c1993 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1237 p h) (sat_nil p)))
def c1994 : List Lit := [(446, false)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1981, c1216] c1994 (by decide) p (sat_cons (step1981 p h) (sat_cons (step1216 p h) (sat_nil p)))
def c1995 : List Lit := [(354, false)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1987, c1118] c1995 (by decide) p (sat_cons (step1987 p h) (sat_cons (step1118 p h) (sat_nil p)))
def c1996 : List Lit := [(258, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c1991, c1024] c1996 (by decide) p (sat_cons (step1991 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c1997 : List Lit := [(130, true), (131, true), (133, true), (136, true), (140, true), (141, true), (142, true), (144, true), (146, true), (148, true), (149, true), (151, true), (152, true), (155, true), (157, true), (159, true), (160, true), (162, true), (165, true), (166, true), (168, true), (169, true), (172, true), (173, true), (177, true), (180, true), (181, true), (183, true), (185, true), (186, true), (190, true), (192, true), (195, true), (197, true), (199, true), (200, true), (203, true), (205, true), (207, true), (209, true), (210, true), (213, true), (214, true), (217, true), (221, true), (222, true), (226, true), (227, true), (228, true), (230, true), (232, true), (234, true), (236, true), (238, true), (239, true), (243, true), (244, true), (246, true), (248, true), (249, true), (251, true), (253, true), (255, true)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.TreeRup.prove_clause [c956, c957, c958, c959, c960, c961, c962, c963, c964, c965, c966, c967, c968, c969, c970, c971, c972, c973, c974, c975, c976, c977, c978, c979, c980, c981, c982, c983, c984, c985, c986, c987, c988, c989, c990, c991, c992, c993, c994, c995, c996, c997, c998, c999, c1000, c1001, c1002, c1003, c1004, c1005, c1006, c1007, c1008, c1009, c1010, c1011, c1012, c1013, c1014, c1015, c1016, c1017, c1018, c1019, c1296] c1997 (by decide) p (sat_cons (step956 p h) (sat_cons (step957 p h) (sat_cons (step958 p h) (sat_cons (step959 p h) (sat_cons (step960 p h) (sat_cons (step961 p h) (sat_cons (step962 p h) (sat_cons (step963 p h) (sat_cons (step964 p h) (sat_cons (step965 p h) (sat_cons (step966 p h) (sat_cons (step967 p h) (sat_cons (step968 p h) (sat_cons (step969 p h) (sat_cons (step970 p h) (sat_cons (step971 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step974 p h) (sat_cons (step975 p h) (sat_cons (step976 p h) (sat_cons (step977 p h) (sat_cons (step978 p h) (sat_cons (step979 p h) (sat_cons (step980 p h) (sat_cons (step981 p h) (sat_cons (step982 p h) (sat_cons (step983 p h) (sat_cons (step984 p h) (sat_cons (step985 p h) (sat_cons (step986 p h) (sat_cons (step987 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step990 p h) (sat_cons (step991 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step1004 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step1007 p h) (sat_cons (step1008 p h) (sat_cons (step1009 p h) (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step1012 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step1015 p h) (sat_cons (step1016 p h) (sat_cons (step1017 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step1296 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1998 : List Lit := [(1733, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1579, c1567, c1569, c1556, c1564, c1561, c1562, c1553, c1554, c434, c456, c391] c1998 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1579 p h) (sat_cons (step1567 p h) (sat_cons (step1569 p h) (sat_cons (step1556 p h) (sat_cons (step1564 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1553 p h) (sat_cons (step1554 p h) (sat_cons (step434 p h) (sat_cons (step456 p h) (sat_cons (step391 p h) (sat_nil p))))))))))))))
def c1999 : List Lit := [(1729, true), (1745, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1600, c1598, c1602, c1594, c1595, c575, c1567, c1569, c1564, c1565, c1562, c437, c398, c422] c1999 (by decide) p (sat_cons (step1600 p h) (sat_cons (step1598 p h) (sat_cons (step1602 p h) (sat_cons (step1594 p h) (sat_cons (step1595 p h) (sat_cons (step575 p h) (sat_cons (step1567 p h) (sat_cons (step1569 p h) (sat_cons (step1564 p h) (sat_cons (step1565 p h) (sat_cons (step1562 p h) (sat_cons (step437 p h) (sat_cons (step398 p h) (sat_cons (step422 p h) (sat_nil p)))))))))))))))
def c2000 : List Lit := [(1745, true), (1734, true)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1949, c1576, c1600, c1602, c1597, c1598, c1594, c1595, c512, c575, c1999, c1580, c1556, c1553, c1554, c548, c430, c394, c1152, c1155, c1157, c1176, c1177, c1210, c1171, c1204, c1164, c1189, c1161, c1181, c425, c1180, c1562, c540, c1570, c695, c1565] c2000 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1949 p h) (sat_cons (step1576 p h) (sat_cons (step1600 p h) (sat_cons (step1602 p h) (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step1594 p h) (sat_cons (step1595 p h) (sat_cons (step512 p h) (sat_cons (step575 p h) (sat_cons (step1999 p h) (sat_cons (step1580 p h) (sat_cons (step1556 p h) (sat_cons (step1553 p h) (sat_cons (step1554 p h) (sat_cons (step548 p h) (sat_cons (step430 p h) (sat_cons (step394 p h) (sat_cons (step1152 p h) (sat_cons (step1155 p h) (sat_cons (step1157 p h) (sat_cons (step1176 p h) (sat_cons (step1177 p h) (sat_cons (step1210 p h) (sat_cons (step1171 p h) (sat_cons (step1204 p h) (sat_cons (step1164 p h) (sat_cons (step1189 p h) (sat_cons (step1161 p h) (sat_cons (step1181 p h) (sat_cons (step425 p h) (sat_cons (step1180 p h) (sat_cons (step1562 p h) (sat_cons (step540 p h) (sat_cons (step1570 p h) (sat_cons (step695 p h) (sat_cons (step1565 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2001 : List Lit := [(1727, true), (1719, true), (1726, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1554, c1553, c1564, c1565, c429, c391, c394, c456, c1152, c1563, c1155, c395, c1157, c427, c1177, c1161, c1171, c1164] c2001 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1554 p h) (sat_cons (step1553 p h) (sat_cons (step1564 p h) (sat_cons (step1565 p h) (sat_cons (step429 p h) (sat_cons (step391 p h) (sat_cons (step394 p h) (sat_cons (step456 p h) (sat_cons (step1152 p h) (sat_cons (step1563 p h) (sat_cons (step1155 p h) (sat_cons (step395 p h) (sat_cons (step1157 p h) (sat_cons (step427 p h) (sat_cons (step1177 p h) (sat_cons (step1161 p h) (sat_cons (step1171 p h) (sat_cons (step1164 p h) (sat_nil p))))))))))))))))))))
def c2002 : List Lit := [(1719, true), (1730, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1572, c1568, c1553, c1554, c2001, c1570, c1561, c1562, c428, c391, c394, c456, c1152, c1566, c1155, c395, c1157, c427, c1177, c1161, c1171, c1164] c2002 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1572 p h) (sat_cons (step1568 p h) (sat_cons (step1553 p h) (sat_cons (step1554 p h) (sat_cons (step2001 p h) (sat_cons (step1570 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step428 p h) (sat_cons (step391 p h) (sat_cons (step394 p h) (sat_cons (step456 p h) (sat_cons (step1152 p h) (sat_cons (step1566 p h) (sat_cons (step1155 p h) (sat_cons (step395 p h) (sat_cons (step1157 p h) (sat_cons (step427 p h) (sat_cons (step1177 p h) (sat_cons (step1161 p h) (sat_cons (step1171 p h) (sat_cons (step1164 p h) (sat_nil p))))))))))))))))))))))))
def c2003 : List Lit := [(69, false), (73, true), (1729, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1561, c1567, c1564, c456, c391] c2003 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1561 p h) (sat_cons (step1567 p h) (sat_cons (step1564 p h) (sat_cons (step456 p h) (sat_cons (step391 p h) (sat_nil p)))))))
def c2004 : List Lit := [(5, true), (140, true), (1585, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1301, c1297, c1299, c1300, c1303, c1324, c1311, c1313, c1308, c1309, c1305, c124, c63, c71, c93] c2004 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1301 p h) (sat_cons (step1297 p h) (sat_cons (step1299 p h) (sat_cons (step1300 p h) (sat_cons (step1303 p h) (sat_cons (step1324 p h) (sat_cons (step1311 p h) (sat_cons (step1313 p h) (sat_cons (step1308 p h) (sat_cons (step1309 p h) (sat_cons (step1305 p h) (sat_cons (step124 p h) (sat_cons (step63 p h) (sat_cons (step71 p h) (sat_cons (step93 p h) (sat_nil p)))))))))))))))))
def c2005 : List Lit := [(1607, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1363, c1366, c1355, c1357, c1341, c1352, c1353, c1349, c1338, c210, c201, c181] c2005 (by decide) p (sat_cons (step1363 p h) (sat_cons (step1366 p h) (sat_cons (step1355 p h) (sat_cons (step1357 p h) (sat_cons (step1341 p h) (sat_cons (step1352 p h) (sat_cons (step1353 p h) (sat_cons (step1349 p h) (sat_cons (step1338 p h) (sat_cons (step210 p h) (sat_cons (step201 p h) (sat_cons (step181 p h) (sat_nil p)))))))))))))
end B112E055
