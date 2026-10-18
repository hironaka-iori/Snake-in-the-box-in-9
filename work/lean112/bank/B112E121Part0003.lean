import B112E121Part0002
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1916 : List Lit := [(45, true), (20, true), (9, false), (8, true), (12, true), (16, true), (70, true)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c884, c67] c1916 (by decide) p (sat_cons (step884 p h) (sat_cons (step67 p h) (sat_nil p)))
def c1917 : List Lit := [(21, true), (17, true), (13, true), (10, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c885, c70] c1917 (by decide) p (sat_cons (step885 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1918 : List Lit := [(17, true), (21, true), (10, false), (8, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c885, c71] c1918 (by decide) p (sat_cons (step885 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1919 : List Lit := [(21, true), (10, false), (13, true), (8, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c885, c72] c1919 (by decide) p (sat_cons (step885 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1920 : List Lit := [(17, true), (10, false), (13, true), (8, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c885, c73] c1920 (by decide) p (sat_cons (step885 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1921 : List Lit := [(23, true), (12, true), (11, false), (13, true), (8, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c886, c79] c1921 (by decide) p (sat_cons (step886 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1922 : List Lit := [(12, true), (11, false), (8, true), (13, true), (18, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c886, c80] c1922 (by decide) p (sat_cons (step886 p h) (sat_cons (step80 p h) (sat_nil p)))
def c1923 : List Lit := [(26, true), (72, true), (14, false), (13, true)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c887, c177] c1923 (by decide) p (sat_cons (step887 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1924 : List Lit := [(12, true), (72, true), (13, true), (14, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c887, c178] c1924 (by decide) p (sat_cons (step887 p h) (sat_cons (step178 p h) (sat_nil p)))
def c1925 : List Lit := [(12, true), (26, true), (13, true), (14, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c887, c179] c1925 (by decide) p (sat_cons (step887 p h) (sat_cons (step179 p h) (sat_nil p)))
def c1926 : List Lit := [(18, true), (17, true), (19, false), (30, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c888, c203] c1926 (by decide) p (sat_cons (step888 p h) (sat_cons (step203 p h) (sat_nil p)))
def c1927 : List Lit := [(18, true), (30, true), (19, false), (13, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c888, c204] c1927 (by decide) p (sat_cons (step888 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1928 : List Lit := [(17, true), (30, true), (13, true), (19, false)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c888, c205] c1928 (by decide) p (sat_cons (step888 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1929 : List Lit := [(18, true), (17, true), (13, true), (19, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c888, c206] c1929 (by decide) p (sat_cons (step888 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1930 : List Lit := [(23, true), (26, true), (20, true), (24, false)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c889, c286] c1930 (by decide) p (sat_cons (step889 p h) (sat_cons (step286 p h) (sat_nil p)))
def c1931 : List Lit := [(12, true), (26, true), (20, true), (24, false)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c889, c287] c1931 (by decide) p (sat_cons (step889 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1932 : List Lit := [(23, true), (24, false), (20, true), (12, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c889, c288] c1932 (by decide) p (sat_cons (step889 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1933 : List Lit := [(29, true), (27, false), (20, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c890, c337] c1933 (by decide) p (sat_cons (step890 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1934 : List Lit := [(29, true), (27, false), (16, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c890, c338] c1934 (by decide) p (sat_cons (step890 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1935 : List Lit := [(27, false), (20, true), (16, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c890, c339] c1935 (by decide) p (sat_cons (step890 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1936 : List Lit := [(40, true), (21, true), (83, true), (30, true), (28, false), (29, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c891, c343] c1936 (by decide) p (sat_cons (step891 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1937 : List Lit := [(21, true), (40, true), (17, true), (28, false), (30, true), (29, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c891, c344] c1937 (by decide) p (sat_cons (step891 p h) (sat_cons (step344 p h) (sat_nil p)))
def c1938 : List Lit := [(29, true), (30, true), (61, true), (31, false)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c892, c376] c1938 (by decide) p (sat_cons (step892 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1939 : List Lit := [(26, true), (30, true), (61, true), (31, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c892, c377] c1939 (by decide) p (sat_cons (step892 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1940 : List Lit := [(29, true), (26, true), (61, true), (31, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c892, c378] c1940 (by decide) p (sat_cons (step892 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1941 : List Lit := [(26, true), (29, true), (31, false), (30, true)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c892, c379] c1941 (by decide) p (sat_cons (step892 p h) (sat_cons (step379 p h) (sat_nil p)))
def c1942 : List Lit := [(159, true), (35, true), (33, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c1727, c1728, c381] c1942 (by decide) p (sat_cons (step1727 p h) (sat_cons (step1728 p h) (sat_cons (step381 p h) (sat_nil p))))
def c1943 : List Lit := [(159, true), (3, true), (33, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1727, c1728, c382] c1943 (by decide) p (sat_cons (step1727 p h) (sat_cons (step1728 p h) (sat_cons (step382 p h) (sat_nil p))))
def c1944 : List Lit := [(39, true), (33, true), (35, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c895, c384] c1944 (by decide) p (sat_cons (step895 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1945 : List Lit := [(39, true), (35, false), (13, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c895, c385] c1945 (by decide) p (sat_cons (step895 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1946 : List Lit := [(33, true), (35, false), (13, true)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c895, c386] c1946 (by decide) p (sat_cons (step895 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1947 : List Lit := [(16, true), (36, false), (62, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c896, c388] c1947 (by decide) p (sat_cons (step896 p h) (sat_cons (step388 p h) (sat_nil p)))
def c1948 : List Lit := [(37, false), (163, true), (36, true)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1729, c389] c1948 (by decide) p (sat_cons (step1729 p h) (sat_cons (step389 p h) (sat_nil p)))
def c1949 : List Lit := [(42, false), (41, true)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c898, c397] c1949 (by decide) p (sat_cons (step898 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1950 : List Lit := [(42, false), (37, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c898, c398] c1950 (by decide) p (sat_cons (step898 p h) (sat_cons (step398 p h) (sat_nil p)))
def c1951 : List Lit := [(41, true), (40, true), (30, true), (43, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c899, c401] c1951 (by decide) p (sat_cons (step899 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1952 : List Lit := [(40, true), (39, true), (43, false), (30, true)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c899, c402] c1952 (by decide) p (sat_cons (step899 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1953 : List Lit := [(52, true), (44, false), (87, true), (48, true), (45, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c900, c404] c1953 (by decide) p (sat_cons (step900 p h) (sat_cons (step404 p h) (sat_nil p)))
def c1954 : List Lit := [(52, true), (44, false), (87, true), (48, true), (8, true)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c900, c405] c1954 (by decide) p (sat_cons (step900 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1955 : List Lit := [(45, true), (44, false), (87, true), (8, true), (52, true)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c900, c406] c1955 (by decide) p (sat_cons (step900 p h) (sat_cons (step406 p h) (sat_nil p)))
def c1956 : List Lit := [(45, true), (44, false), (8, true), (87, true), (48, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c900, c407] c1956 (by decide) p (sat_cons (step900 p h) (sat_cons (step407 p h) (sat_nil p)))
def c1957 : List Lit := [(45, true), (44, false), (52, true), (48, true), (8, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c900, c408] c1957 (by decide) p (sat_cons (step900 p h) (sat_cons (step408 p h) (sat_nil p)))
def c1958 : List Lit := [(50, true), (91, true), (45, true), (46, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c901, c419] c1958 (by decide) p (sat_cons (step901 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1959 : List Lit := [(50, true), (91, true), (12, true), (46, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c901, c420] c1959 (by decide) p (sat_cons (step901 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1960 : List Lit := [(46, false), (91, true), (45, true), (12, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c901, c421] c1960 (by decide) p (sat_cons (step901 p h) (sat_cons (step421 p h) (sat_nil p)))
def c1961 : List Lit := [(46, false), (50, true), (12, true), (45, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c901, c422] c1961 (by decide) p (sat_cons (step901 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1962 : List Lit := [(47, false), (56, true), (92, true)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c902, c424] c1962 (by decide) p (sat_cons (step902 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1963 : List Lit := [(47, false), (13, true), (92, true)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c902, c425] c1963 (by decide) p (sat_cons (step902 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1964 : List Lit := [(47, false), (13, true), (56, true)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c902, c426] c1964 (by decide) p (sat_cons (step902 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1965 : List Lit := [(50, true), (51, false), (61, true), (99, true)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c903, c434] c1965 (by decide) p (sat_cons (step903 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1966 : List Lit := [(51, false), (49, true), (99, true), (61, true)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c903, c435] c1966 (by decide) p (sat_cons (step903 p h) (sat_cons (step435 p h) (sat_nil p)))
def c1967 : List Lit := [(50, true), (51, false), (61, true), (49, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c903, c436] c1967 (by decide) p (sat_cons (step903 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1968 : List Lit := [(55, true), (45, true), (100, true), (53, false), (52, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c904, c449] c1968 (by decide) p (sat_cons (step904 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1969 : List Lit := [(20, true), (55, true), (100, true), (53, false), (52, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c904, c450] c1969 (by decide) p (sat_cons (step904 p h) (sat_cons (step450 p h) (sat_nil p)))
def c1970 : List Lit := [(55, true), (45, true), (20, true), (53, false), (100, true)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c904, c451] c1970 (by decide) p (sat_cons (step904 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1971 : List Lit := [(52, true), (45, true), (100, true), (20, true), (53, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c904, c452] c1971 (by decide) p (sat_cons (step904 p h) (sat_cons (step452 p h) (sat_nil p)))
def c1972 : List Lit := [(55, true), (53, false), (45, true), (52, true), (20, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c904, c453] c1972 (by decide) p (sat_cons (step904 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1973 : List Lit := [(55, true), (56, true), (54, false), (52, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c905, c456] c1973 (by decide) p (sat_cons (step905 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1974 : List Lit := [(55, true), (56, true), (54, false), (21, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c905, c457] c1974 (by decide) p (sat_cons (step905 p h) (sat_cons (step457 p h) (sat_nil p)))
def c1975 : List Lit := [(52, true), (56, true), (54, false), (21, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c905, c458] c1975 (by decide) p (sat_cons (step905 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1976 : List Lit := [(55, true), (52, true), (21, true), (54, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c905, c459] c1976 (by decide) p (sat_cons (step905 p h) (sat_cons (step459 p h) (sat_nil p)))
def c1977 : List Lit := [(65, true), (52, true), (57, false), (105, true), (48, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c906, c476] c1977 (by decide) p (sat_cons (step906 p h) (sat_cons (step476 p h) (sat_nil p)))
def c1978 : List Lit := [(58, true), (59, false), (61, true)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c907, c479] c1978 (by decide) p (sat_cons (step907 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1979 : List Lit := [(50, true), (59, false), (61, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c907, c480] c1979 (by decide) p (sat_cons (step907 p h) (sat_cons (step480 p h) (sat_nil p)))
end B112E121
