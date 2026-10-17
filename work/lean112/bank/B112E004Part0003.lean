import B112E004Part0002
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1926 : List Lit := [(22, false), (33, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c786, c77] c1926 (by decide) p (sat_cons (step786 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1927 : List Lit := [(22, false), (23, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c786, c78] c1927 (by decide) p (sat_cons (step786 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1928 : List Lit := [(28, false), (27, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c789, c103] c1928 (by decide) p (sat_cons (step789 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1929 : List Lit := [(28, false), (25, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c789, c104] c1929 (by decide) p (sat_cons (step789 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1930 : List Lit := [(30, false), (29, true), (31, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c790, c135] c1930 (by decide) p (sat_cons (step790 p h) (sat_cons (step135 p h) (sat_nil p)))
def c1931 : List Lit := [(30, false), (25, true), (31, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c790, c136] c1931 (by decide) p (sat_cons (step790 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1932 : List Lit := [(25, true), (30, false), (29, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c790, c137] c1932 (by decide) p (sat_cons (step790 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1933 : List Lit := [(33, true), (29, true), (32, false)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c791, c145] c1933 (by decide) p (sat_cons (step791 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1934 : List Lit := [(27, true), (29, true), (32, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c791, c146] c1934 (by decide) p (sat_cons (step791 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1935 : List Lit := [(35, false), (37, true), (39, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c792, c161] c1935 (by decide) p (sat_cons (step792 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1936 : List Lit := [(35, false), (39, true), (34, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c792, c162] c1936 (by decide) p (sat_cons (step792 p h) (sat_cons (step162 p h) (sat_nil p)))
def c1937 : List Lit := [(35, false), (37, true), (34, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c792, c163] c1937 (by decide) p (sat_cons (step792 p h) (sat_cons (step163 p h) (sat_nil p)))
def c1938 : List Lit := [(37, true), (36, false), (57, true), (45, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c793, c166] c1938 (by decide) p (sat_cons (step793 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1939 : List Lit := [(45, true), (57, true), (34, true), (36, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c793, c167] c1939 (by decide) p (sat_cons (step793 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1940 : List Lit := [(36, false), (37, true), (34, true), (57, true)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c793, c168] c1940 (by decide) p (sat_cons (step793 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1941 : List Lit := [(37, true), (36, false), (45, true), (34, true)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c793, c169] c1941 (by decide) p (sat_cons (step793 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1942 : List Lit := [(38, false), (43, true), (49, true), (88, true)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c794, c183] c1942 (by decide) p (sat_cons (step794 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1943 : List Lit := [(38, false), (37, true), (49, true), (88, true)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c794, c184] c1943 (by decide) p (sat_cons (step794 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1944 : List Lit := [(37, true), (43, true), (88, true), (38, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c794, c185] c1944 (by decide) p (sat_cons (step794 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1945 : List Lit := [(37, true), (43, true), (38, false), (49, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c794, c186] c1945 (by decide) p (sat_cons (step794 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1946 : List Lit := [(43, true), (42, false), (41, true), (54, true)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c796, c242] c1946 (by decide) p (sat_cons (step796 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1947 : List Lit := [(43, true), (42, false), (39, true), (54, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c796, c243] c1947 (by decide) p (sat_cons (step796 p h) (sat_cons (step243 p h) (sat_nil p)))
def c1948 : List Lit := [(42, false), (54, true), (39, true), (41, true)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c796, c244] c1948 (by decide) p (sat_cons (step796 p h) (sat_cons (step244 p h) (sat_nil p)))
def c1949 : List Lit := [(43, true), (42, false), (39, true), (41, true)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c796, c245] c1949 (by decide) p (sat_cons (step796 p h) (sat_cons (step245 p h) (sat_nil p)))
def c1950 : List Lit := [(95, true), (45, true), (49, true), (37, true), (46, false), (68, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c798, c282] c1950 (by decide) p (sat_cons (step798 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1951 : List Lit := [(10, true), (95, true), (45, true), (49, true), (46, false), (68, true)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c798, c283] c1951 (by decide) p (sat_cons (step798 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1952 : List Lit := [(10, true), (37, true), (49, true), (45, true), (68, true), (46, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c798, c284] c1952 (by decide) p (sat_cons (step798 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1953 : List Lit := [(47, true), (55, true), (48, false), (49, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c799, c289] c1953 (by decide) p (sat_cons (step799 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1954 : List Lit := [(48, false), (55, true), (49, true), (45, true)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c799, c290] c1954 (by decide) p (sat_cons (step799 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1955 : List Lit := [(47, true), (45, true), (48, false), (55, true)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c799, c291] c1955 (by decide) p (sat_cons (step799 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1956 : List Lit := [(48, false), (45, true), (47, true), (49, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c799, c292] c1956 (by decide) p (sat_cons (step799 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1957 : List Lit := [(54, true), (99, true), (39, true), (72, true), (51, false), (50, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c800, c376] c1957 (by decide) p (sat_cons (step800 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1958 : List Lit := [(54, true), (99, true), (51, false), (50, true), (14, true), (72, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c800, c377] c1958 (by decide) p (sat_cons (step800 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1959 : List Lit := [(14, true), (99, true), (54, true), (39, true), (51, false), (50, true)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c800, c378] c1959 (by decide) p (sat_cons (step800 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1960 : List Lit := [(14, true), (54, true), (39, true), (51, false), (50, true), (72, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c800, c379] c1960 (by decide) p (sat_cons (step800 p h) (sat_cons (step379 p h) (sat_nil p)))
def c1961 : List Lit := [(50, true), (55, true), (100, true), (52, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c801, c383] c1961 (by decide) p (sat_cons (step801 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1962 : List Lit := [(45, true), (55, true), (100, true), (52, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c801, c384] c1962 (by decide) p (sat_cons (step801 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1963 : List Lit := [(45, true), (50, true), (100, true), (52, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c801, c385] c1963 (by decide) p (sat_cons (step801 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1964 : List Lit := [(50, true), (45, true), (55, true), (52, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c801, c386] c1964 (by decide) p (sat_cons (step801 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1965 : List Lit := [(54, true), (47, true), (50, true), (53, false), (55, true)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c802, c392] c1965 (by decide) p (sat_cons (step802 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1966 : List Lit := [(41, true), (54, true), (53, false), (50, true), (55, true)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c802, c393] c1966 (by decide) p (sat_cons (step802 p h) (sat_cons (step393 p h) (sat_nil p)))
def c1967 : List Lit := [(41, true), (47, true), (53, false), (50, true), (55, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c802, c394] c1967 (by decide) p (sat_cons (step802 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1968 : List Lit := [(16, true), (56, false), (54, true), (74, true), (49, true), (55, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c803, c460] c1968 (by decide) p (sat_cons (step803 p h) (sat_cons (step460 p h) (sat_nil p)))
def c1969 : List Lit := [(74, true), (56, false), (43, true), (49, true), (16, true), (54, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c803, c461] c1969 (by decide) p (sat_cons (step803 p h) (sat_cons (step461 p h) (sat_nil p)))
def c1970 : List Lit := [(56, false), (54, true), (43, true), (49, true), (16, true), (55, true)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c803, c462] c1970 (by decide) p (sat_cons (step803 p h) (sat_cons (step462 p h) (sat_nil p)))
def c1971 : List Lit := [(59, false), (69, true)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c804, c472] c1971 (by decide) p (sat_cons (step804 p h) (sat_cons (step472 p h) (sat_nil p)))
def c1972 : List Lit := [(59, false), (58, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c804, c473] c1972 (by decide) p (sat_cons (step804 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1973 : List Lit := [(65, true), (57, true), (60, false)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c805, c475] c1973 (by decide) p (sat_cons (step805 p h) (sat_cons (step475 p h) (sat_nil p)))
def c1974 : List Lit := [(58, true), (57, true), (60, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c805, c476] c1974 (by decide) p (sat_cons (step805 p h) (sat_cons (step476 p h) (sat_nil p)))
def c1975 : List Lit := [(63, true), (72, true), (61, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c806, c478] c1975 (by decide) p (sat_cons (step806 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1976 : List Lit := [(72, true), (61, false), (39, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c806, c479] c1976 (by decide) p (sat_cons (step806 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1977 : List Lit := [(63, true), (61, false), (39, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c806, c480] c1977 (by decide) p (sat_cons (step806 p h) (sat_cons (step480 p h) (sat_nil p)))
def c1978 : List Lit := [(65, true), (63, true), (62, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c807, c482] c1978 (by decide) p (sat_cons (step807 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1979 : List Lit := [(65, true), (57, true), (62, false)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c807, c483] c1979 (by decide) p (sat_cons (step807 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1980 : List Lit := [(63, true), (57, true), (62, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c807, c484] c1980 (by decide) p (sat_cons (step807 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1981 : List Lit := [(65, true), (64, false), (41, true), (110, true)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c808, c491] c1981 (by decide) p (sat_cons (step808 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1982 : List Lit := [(58, true), (64, false), (41, true), (110, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c808, c492] c1982 (by decide) p (sat_cons (step808 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1983 : List Lit := [(68, true), (69, true), (72, true), (67, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c809, c503] c1983 (by decide) p (sat_cons (step809 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1984 : List Lit := [(69, true), (66, true), (72, true), (67, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c809, c504] c1984 (by decide) p (sat_cons (step809 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1985 : List Lit := [(68, true), (72, true), (66, true), (67, false)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c809, c505] c1985 (by decide) p (sat_cons (step809 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1986 : List Lit := [(68, true), (69, true), (67, false), (66, true)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c809, c506] c1986 (by decide) p (sat_cons (step809 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1987 : List Lit := [(69, true), (74, true), (49, true), (70, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c810, c514] c1987 (by decide) p (sat_cons (step810 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1988 : List Lit := [(68, true), (74, true), (49, true), (70, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c810, c515] c1988 (by decide) p (sat_cons (step810 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1989 : List Lit := [(68, true), (69, true), (49, true), (70, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c810, c516] c1989 (by decide) p (sat_cons (step810 p h) (sat_cons (step516 p h) (sat_nil p)))
end B112E004
