import B112E020Part0004
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1932 : List Lit := [(102, true), (113, false), (119, true), (115, true), (117, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c820, c617] c1932 (by decide) p (sat_cons (step820 p h) (sat_cons (step617 p h) (sat_nil p)))
def c1933 : List Lit := [(114, true), (113, false), (117, true), (102, true), (119, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c820, c618] c1933 (by decide) p (sat_cons (step820 p h) (sat_cons (step618 p h) (sat_nil p)))
def c1934 : List Lit := [(114, true), (119, true), (113, false), (102, true), (115, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c820, c619] c1934 (by decide) p (sat_cons (step820 p h) (sat_cons (step619 p h) (sat_nil p)))
def c1935 : List Lit := [(114, true), (113, false), (115, true), (102, true), (117, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c820, c620] c1935 (by decide) p (sat_cons (step820 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1936 : List Lit := [(114, true), (95, true), (115, true), (116, false), (105, true), (62, true), (120, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c821, c669] c1936 (by decide) p (sat_cons (step821 p h) (sat_cons (step669 p h) (sat_nil p)))
def c1937 : List Lit := [(114, true), (105, true), (79, true), (115, true), (116, false), (62, true), (120, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c821, c670] c1937 (by decide) p (sat_cons (step821 p h) (sat_cons (step670 p h) (sat_nil p)))
def c1938 : List Lit := [(114, true), (95, true), (116, false), (120, true), (105, true), (79, true), (62, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c821, c671] c1938 (by decide) p (sat_cons (step821 p h) (sat_cons (step671 p h) (sat_nil p)))
def c1939 : List Lit := [(117, true), (123, true), (118, false), (115, true)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c822, c684] c1939 (by decide) p (sat_cons (step822 p h) (sat_cons (step684 p h) (sat_nil p)))
def c1940 : List Lit := [(117, true), (118, false), (64, true), (123, true)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c822, c685] c1940 (by decide) p (sat_cons (step822 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1941 : List Lit := [(115, true), (123, true), (64, true), (118, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c822, c686] c1941 (by decide) p (sat_cons (step822 p h) (sat_cons (step686 p h) (sat_nil p)))
def c1942 : List Lit := [(117, true), (118, false), (115, true), (64, true)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c822, c687] c1942 (by decide) p (sat_cons (step822 p h) (sat_cons (step687 p h) (sat_nil p)))
def c1943 : List Lit := [(121, false), (119, true), (117, true), (122, true), (123, true)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c823, c721] c1943 (by decide) p (sat_cons (step823 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1944 : List Lit := [(123, true), (121, false), (119, true), (110, true), (122, true)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c823, c722] c1944 (by decide) p (sat_cons (step823 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1945 : List Lit := [(121, false), (122, true), (110, true), (117, true), (123, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c823, c723] c1945 (by decide) p (sat_cons (step823 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1946 : List Lit := [(121, false), (119, true), (117, true), (123, true), (110, true)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c823, c724] c1946 (by decide) p (sat_cons (step823 p h) (sat_cons (step724 p h) (sat_nil p)))
def c1947 : List Lit := [(121, false), (119, true), (122, true), (110, true), (117, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c823, c725] c1947 (by decide) p (sat_cons (step823 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1948 : List Lit := [(125, false), (249, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1639, c827] c1948 (by decide) p (sat_cons (step1639 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1949 : List Lit := [(259, false), (273, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1627, c843] c1949 (by decide) p (sat_cons (step1627 p h) (sat_cons (step843 p h) (sat_nil p)))
def c1950 : List Lit := [(281, false), (283, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c1638, c850] c1950 (by decide) p (sat_cons (step1638 p h) (sat_cons (step850 p h) (sat_nil p)))
def c1951 : List Lit := [(279, false), (285, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c1634, c854] c1951 (by decide) p (sat_cons (step1634 p h) (sat_cons (step854 p h) (sat_nil p)))
def c1952 : List Lit := [(275, false), (303, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c1620, c864] c1952 (by decide) p (sat_cons (step1620 p h) (sat_cons (step864 p h) (sat_nil p)))
def c1953 : List Lit := [(156, false), (307, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c1637, c869] c1953 (by decide) p (sat_cons (step1637 p h) (sat_cons (step869 p h) (sat_nil p)))
def c1954 : List Lit := [(317, false), (331, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1625, c887] c1954 (by decide) p (sat_cons (step1625 p h) (sat_cons (step887 p h) (sat_nil p)))
def c1955 : List Lit := [(339, false), (345, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c1632, c895] c1955 (by decide) p (sat_cons (step1632 p h) (sat_cons (step895 p h) (sat_nil p)))
def c1956 : List Lit := [(353, false), (359, false)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1631, c904] c1956 (by decide) p (sat_cons (step1631 p h) (sat_cons (step904 p h) (sat_nil p)))
def c1957 : List Lit := [(347, false), (361, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1624, c908] c1957 (by decide) p (sat_cons (step1624 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1958 : List Lit := [(333, false), (363, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1619, c913] c1958 (by decide) p (sat_cons (step1619 p h) (sat_cons (step913 p h) (sat_nil p)))
def c1959 : List Lit := [(305, false), (365, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1616, c918] c1959 (by decide) p (sat_cons (step1616 p h) (sat_cons (step918 p h) (sat_nil p)))
def c1960 : List Lit := [(395, false), (425, false)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1618, c960] c1960 (by decide) p (sat_cons (step1618 p h) (sat_cons (step960 p h) (sat_nil p)))
def c1961 : List Lit := [(225, false), (226, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c1640, c969] c1961 (by decide) p (sat_cons (step1640 p h) (sat_cons (step969 p h) (sat_nil p)))
def c1962 : List Lit := [(439, false), (453, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1622, c980] c1962 (by decide) p (sat_cons (step1622 p h) (sat_cons (step980 p h) (sat_nil p)))
def c1963 : List Lit := [(475, false), (481, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1628, c997] c1963 (by decide) p (sat_cons (step1628 p h) (sat_cons (step997 p h) (sat_nil p)))
def c1964 : List Lit := [(469, false), (483, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c1621, c1001] c1964 (by decide) p (sat_cons (step1621 p h) (sat_cons (step1001 p h) (sat_nil p)))
def c1965 : List Lit := [(455, false), (485, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1005] c1965 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1005 p h) (sat_nil p)))
def c1966 : List Lit := [(427, false), (487, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1010] c1966 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1010 p h) (sat_nil p)))
def c1967 : List Lit := [(367, false), (489, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1015, c1013] c1967 (by decide) p (sat_cons (step1015 p h) (sat_cons (step1013 p h) (sat_nil p)))
def c1968 : List Lit := [(1536, false), (1546, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1090] c1968 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c1969 : List Lit := [(1537, false), (1547, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1091] c1969 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1091 p h) (sat_nil p)))
def c1970 : List Lit := [(1538, false), (1548, true)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1092] c1970 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c1971 : List Lit := [(1539, false), (1549, true)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1093] c1971 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c1972 : List Lit := [(1540, false), (1550, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1094] c1972 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c1973 : List Lit := [(1546, true), (1512, false)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1095] c1973 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c1974 : List Lit := [(1547, true), (1513, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1100] c1974 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1100 p h) (sat_nil p)))
def c1975 : List Lit := [(1548, true), (1514, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1105] c1975 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c1976 : List Lit := [(1515, false), (1549, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1107] c1976 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c1977 : List Lit := [(1561, false), (1574, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1144] c1977 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1144 p h) (sat_nil p)))
def c1978 : List Lit := [(1562, false), (1575, true)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1147] c1978 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1147 p h) (sat_nil p)))
def c1979 : List Lit := [(1563, false), (1576, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c1653, c1150] c1979 (by decide) p (sat_cons (step1653 p h) (sat_cons (step1150 p h) (sat_nil p)))
def c1980 : List Lit := [(1597, false), (1607, true)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1201] c1980 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1201 p h) (sat_nil p)))
def c1981 : List Lit := [(1598, false), (1608, true)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1202] c1981 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1202 p h) (sat_nil p)))
def c1982 : List Lit := [(1599, false), (1609, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1203] c1982 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1203 p h) (sat_nil p)))
def c1983 : List Lit := [(1600, false), (1610, true)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1204] c1983 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1204 p h) (sat_nil p)))
def c1984 : List Lit := [(1601, false), (1611, true)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1205] c1984 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1205 p h) (sat_nil p)))
def c1985 : List Lit := [(1574, false), (1607, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c1654, c1206] c1985 (by decide) p (sat_cons (step1654 p h) (sat_cons (step1206 p h) (sat_nil p)))
def c1986 : List Lit := [(1575, false), (1608, true)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1654, c1212] c1986 (by decide) p (sat_cons (step1654 p h) (sat_cons (step1212 p h) (sat_nil p)))
def c1987 : List Lit := [(1576, false), (1609, true)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1654, c1217] c1987 (by decide) p (sat_cons (step1654 p h) (sat_cons (step1217 p h) (sat_nil p)))
def c1988 : List Lit := [(1629, true), (1608, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1224] c1988 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1224 p h) (sat_nil p)))
def c1989 : List Lit := [(1630, true), (1609, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1225] c1989 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1225 p h) (sat_nil p)))
def c1990 : List Lit := [(1631, true), (1610, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1226] c1990 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1226 p h) (sat_nil p)))
def c1991 : List Lit := [(1611, false), (1632, true)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1227] c1991 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1227 p h) (sat_nil p)))
def c1992 : List Lit := [(1612, false), (1633, true)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1228] c1992 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1228 p h) (sat_nil p)))
def c1993 : List Lit := [(1613, false), (1634, true)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1229] c1993 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c1994 : List Lit := [(1614, false), (1635, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1230] c1994 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c1995 : List Lit := [(1547, false), (1629, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1769, c1238] c1995 (by decide) p (sat_cons (step1769 p h) (sat_cons (step1238 p h) (sat_nil p)))
end B112E020
