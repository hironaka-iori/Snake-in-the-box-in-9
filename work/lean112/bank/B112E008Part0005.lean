import B112E008Part0004
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1927 : List Lit := [(91, true), (88, true), (89, false), (93, true), (101, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c791, c514] c1927 (by decide) p (sat_cons (step791 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1928 : List Lit := [(93, true), (91, true), (101, true), (89, false), (87, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c791, c515] c1928 (by decide) p (sat_cons (step791 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1929 : List Lit := [(93, true), (88, true), (101, true), (89, false), (87, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c791, c516] c1929 (by decide) p (sat_cons (step791 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1930 : List Lit := [(91, true), (88, true), (101, true), (89, false), (87, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c791, c517] c1930 (by decide) p (sat_cons (step791 p h) (sat_cons (step517 p h) (sat_nil p)))
def c1931 : List Lit := [(93, true), (91, true), (88, true), (89, false), (87, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c791, c518] c1931 (by decide) p (sat_cons (step791 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1932 : List Lit := [(91, true), (95, true), (87, true), (90, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c792, c522] c1932 (by decide) p (sat_cons (step792 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1933 : List Lit := [(36, true), (95, true), (90, false), (91, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c792, c523] c1933 (by decide) p (sat_cons (step792 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1934 : List Lit := [(36, true), (95, true), (87, true), (90, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c792, c524] c1934 (by decide) p (sat_cons (step792 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1935 : List Lit := [(36, true), (91, true), (87, true), (90, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c792, c525] c1935 (by decide) p (sat_cons (step792 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1936 : List Lit := [(93, true), (97, false), (108, true), (96, true), (95, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c793, c604] c1936 (by decide) p (sat_cons (step793 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1937 : List Lit := [(95, true), (97, false), (96, true), (91, true), (108, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c793, c605] c1937 (by decide) p (sat_cons (step793 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1938 : List Lit := [(93, true), (97, false), (91, true), (96, true), (108, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c793, c606] c1938 (by decide) p (sat_cons (step793 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1939 : List Lit := [(95, true), (93, true), (91, true), (108, true), (97, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c793, c607] c1939 (by decide) p (sat_cons (step793 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1940 : List Lit := [(93, true), (97, false), (96, true), (91, true), (95, true)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c793, c608] c1940 (by decide) p (sat_cons (step793 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1941 : List Lit := [(101, true), (98, true), (99, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c794, c619] c1941 (by decide) p (sat_cons (step794 p h) (sat_cons (step619 p h) (sat_nil p)))
def c1942 : List Lit := [(101, true), (87, true), (99, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c794, c620] c1942 (by decide) p (sat_cons (step794 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1943 : List Lit := [(98, true), (87, true), (99, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c794, c621] c1943 (by decide) p (sat_cons (step794 p h) (sat_cons (step621 p h) (sat_nil p)))
def c1944 : List Lit := [(43, true), (78, true), (100, false), (88, true), (98, true), (101, true), (104, true)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c795, c635] c1944 (by decide) p (sat_cons (step795 p h) (sat_cons (step635 p h) (sat_nil p)))
def c1945 : List Lit := [(118, true), (106, true), (102, false), (98, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c796, c647] c1945 (by decide) p (sat_cons (step796 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1946 : List Lit := [(118, true), (79, true), (102, false), (98, true)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c796, c648] c1946 (by decide) p (sat_cons (step796 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1947 : List Lit := [(92, true), (106, true), (103, false), (98, true), (104, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c797, c652] c1947 (by decide) p (sat_cons (step797 p h) (sat_cons (step652 p h) (sat_nil p)))
def c1948 : List Lit := [(47, true), (106, true), (103, false), (98, true), (104, true)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c797, c653] c1948 (by decide) p (sat_cons (step797 p h) (sat_cons (step653 p h) (sat_nil p)))
def c1949 : List Lit := [(92, true), (106, true), (103, false), (47, true), (98, true)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c797, c654] c1949 (by decide) p (sat_cons (step797 p h) (sat_cons (step654 p h) (sat_nil p)))
def c1950 : List Lit := [(47, true), (103, false), (92, true), (104, true), (98, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c797, c655] c1950 (by decide) p (sat_cons (step797 p h) (sat_cons (step655 p h) (sat_nil p)))
def c1951 : List Lit := [(108, true), (106, true), (107, false), (104, true)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c798, c692] c1951 (by decide) p (sat_cons (step798 p h) (sat_cons (step692 p h) (sat_nil p)))
def c1952 : List Lit := [(108, true), (106, true), (107, false), (96, true)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c798, c693] c1952 (by decide) p (sat_cons (step798 p h) (sat_cons (step693 p h) (sat_nil p)))
def c1953 : List Lit := [(108, true), (104, true), (96, true), (107, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c798, c694] c1953 (by decide) p (sat_cons (step798 p h) (sat_cons (step694 p h) (sat_nil p)))
def c1954 : List Lit := [(106, true), (104, true), (96, true), (107, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c798, c695] c1954 (by decide) p (sat_cons (step798 p h) (sat_cons (step695 p h) (sat_nil p)))
def c1955 : List Lit := [(109, true), (114, true), (110, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c799, c707] c1955 (by decide) p (sat_cons (step799 p h) (sat_cons (step707 p h) (sat_nil p)))
def c1956 : List Lit := [(114, true), (110, false), (87, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c799, c708] c1956 (by decide) p (sat_cons (step799 p h) (sat_cons (step708 p h) (sat_nil p)))
def c1957 : List Lit := [(109, true), (110, false), (87, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c799, c709] c1957 (by decide) p (sat_cons (step799 p h) (sat_cons (step709 p h) (sat_nil p)))
def c1958 : List Lit := [(120, true), (55, true), (91, true), (112, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c800, c713] c1958 (by decide) p (sat_cons (step800 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1959 : List Lit := [(111, true), (91, true), (55, true), (112, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c800, c714] c1959 (by decide) p (sat_cons (step800 p h) (sat_cons (step714 p h) (sat_nil p)))
def c1960 : List Lit := [(115, true), (113, false), (92, true), (114, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c801, c717] c1960 (by decide) p (sat_cons (step801 p h) (sat_cons (step717 p h) (sat_nil p)))
def c1961 : List Lit := [(109, true), (113, false), (92, true), (114, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c801, c718] c1961 (by decide) p (sat_cons (step801 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1962 : List Lit := [(115, true), (111, true), (116, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c802, c727] c1962 (by decide) p (sat_cons (step802 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1963 : List Lit := [(115, true), (96, true), (116, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c802, c728] c1963 (by decide) p (sat_cons (step802 p h) (sat_cons (step728 p h) (sat_nil p)))
def c1964 : List Lit := [(111, true), (96, true), (116, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c802, c729] c1964 (by decide) p (sat_cons (step802 p h) (sat_cons (step729 p h) (sat_nil p)))
def c1965 : List Lit := [(124, true), (120, true), (119, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c803, c737] c1965 (by decide) p (sat_cons (step803 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1966 : List Lit := [(124, true), (118, true), (119, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c803, c738] c1966 (by decide) p (sat_cons (step803 p h) (sat_cons (step738 p h) (sat_nil p)))
def c1967 : List Lit := [(118, true), (120, true), (119, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c803, c739] c1967 (by decide) p (sat_cons (step803 p h) (sat_cons (step739 p h) (sat_nil p)))
def c1968 : List Lit := [(124, true), (114, true), (121, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c804, c743] c1968 (by decide) p (sat_cons (step804 p h) (sat_cons (step743 p h) (sat_nil p)))
def c1969 : List Lit := [(123, true), (114, true), (121, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c804, c744] c1969 (by decide) p (sat_cons (step804 p h) (sat_cons (step744 p h) (sat_nil p)))
def c1970 : List Lit := [(123, true), (104, true), (122, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c805, c745] c1970 (by decide) p (sat_cons (step805 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1971 : List Lit := [(117, true), (104, true), (122, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c805, c746] c1971 (by decide) p (sat_cons (step805 p h) (sat_cons (step746 p h) (sat_nil p)))
def c1972 : List Lit := [(253, false), (255, false)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1645, c812] c1972 (by decide) p (sat_cons (step1645 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1973 : List Lit := [(251, false), (257, false)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1638, c816] c1973 (by decide) p (sat_cons (step1638 p h) (sat_cons (step816 p h) (sat_nil p)))
def c1974 : List Lit := [(259, false), (273, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1626, c824] c1974 (by decide) p (sat_cons (step1626 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1975 : List Lit := [(140, false), (277, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1644, c829] c1975 (by decide) p (sat_cons (step1644 p h) (sat_cons (step829 p h) (sat_nil p)))
def c1976 : List Lit := [(154, false), (155, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1648, c841] c1976 (by decide) p (sat_cons (step1648 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1977 : List Lit := [(293, false), (299, false)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c1636, c847] c1977 (by decide) p (sat_cons (step1636 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1978 : List Lit := [(287, false), (301, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1625, c851] c1978 (by decide) p (sat_cons (step1625 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1979 : List Lit := [(275, false), (303, false)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c1618, c856] c1979 (by decide) p (sat_cons (step1618 p h) (sat_cons (step856 p h) (sat_nil p)))
def c1980 : List Lit := [(309, false), (315, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1635, c865] c1980 (by decide) p (sat_cons (step1635 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1981 : List Lit := [(323, false), (329, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1634, c874] c1981 (by decide) p (sat_cons (step1634 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1982 : List Lit := [(317, false), (331, false)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1624, c878] c1982 (by decide) p (sat_cons (step1624 p h) (sat_cons (step878 p h) (sat_nil p)))
def c1983 : List Lit := [(173, false), (174, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1647, c882] c1983 (by decide) p (sat_cons (step1647 p h) (sat_cons (step882 p h) (sat_nil p)))
def c1984 : List Lit := [(347, false), (361, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1623, c895] c1984 (by decide) p (sat_cons (step1623 p h) (sat_cons (step895 p h) (sat_nil p)))
def c1985 : List Lit := [(333, false), (363, false)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c1617, c900] c1985 (by decide) p (sat_cons (step1617 p h) (sat_cons (step900 p h) (sat_nil p)))
def c1986 : List Lit := [(305, false), (365, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1614, c905] c1986 (by decide) p (sat_cons (step1614 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1987 : List Lit := [(371, false), (377, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1632, c915] c1987 (by decide) p (sat_cons (step1632 p h) (sat_cons (step915 p h) (sat_nil p)))
def c1988 : List Lit := [(385, false), (391, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1631, c924] c1988 (by decide) p (sat_cons (step1631 p h) (sat_cons (step924 p h) (sat_nil p)))
def c1989 : List Lit := [(379, false), (393, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1622, c928] c1989 (by decide) p (sat_cons (step1622 p h) (sat_cons (step928 p h) (sat_nil p)))
def c1990 : List Lit := [(409, false), (423, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1621, c947] c1990 (by decide) p (sat_cons (step1621 p h) (sat_cons (step947 p h) (sat_nil p)))
end B112E008
