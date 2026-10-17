import B112E097Part0004
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1915 : List Lit := [(78, true), (75, true), (74, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c721, c309] c1915 (by decide) p (sat_cons (step721 p h) (sat_cons (step309 p h) (sat_nil p)))
def c1916 : List Lit := [(75, true), (77, true), (74, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c721, c310] c1916 (by decide) p (sat_cons (step721 p h) (sat_cons (step310 p h) (sat_nil p)))
def c1917 : List Lit := [(75, true), (58, true), (76, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c722, c314] c1917 (by decide) p (sat_cons (step722 p h) (sat_cons (step314 p h) (sat_nil p)))
def c1918 : List Lit := [(66, true), (58, true), (76, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c722, c315] c1918 (by decide) p (sat_cons (step722 p h) (sat_cons (step315 p h) (sat_nil p)))
def c1919 : List Lit := [(78, true), (80, true), (79, false)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c723, c323] c1919 (by decide) p (sat_cons (step723 p h) (sat_cons (step323 p h) (sat_nil p)))
def c1920 : List Lit := [(80, true), (77, true), (79, false)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c723, c324] c1920 (by decide) p (sat_cons (step723 p h) (sat_cons (step324 p h) (sat_nil p)))
def c1921 : List Lit := [(78, true), (77, true), (79, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c723, c325] c1921 (by decide) p (sat_cons (step723 p h) (sat_cons (step325 p h) (sat_nil p)))
def c1922 : List Lit := [(80, true), (81, false), (123, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c724, c330] c1922 (by decide) p (sat_cons (step724 p h) (sat_cons (step330 p h) (sat_nil p)))
def c1923 : List Lit := [(73, true), (81, false), (123, true)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c724, c331] c1923 (by decide) p (sat_cons (step724 p h) (sat_cons (step331 p h) (sat_nil p)))
def c1924 : List Lit := [(80, true), (73, true), (81, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c724, c332] c1924 (by decide) p (sat_cons (step724 p h) (sat_cons (step332 p h) (sat_nil p)))
def c1925 : List Lit := [(84, true), (92, true), (82, false), (102, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c725, c334] c1925 (by decide) p (sat_cons (step725 p h) (sat_cons (step334 p h) (sat_nil p)))
def c1926 : List Lit := [(83, true), (92, true), (82, false), (102, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c725, c335] c1926 (by decide) p (sat_cons (step725 p h) (sat_cons (step335 p h) (sat_nil p)))
def c1927 : List Lit := [(83, true), (84, true), (82, false), (102, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c725, c336] c1927 (by decide) p (sat_cons (step725 p h) (sat_cons (step336 p h) (sat_nil p)))
def c1928 : List Lit := [(83, true), (84, true), (82, false), (92, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c725, c337] c1928 (by decide) p (sat_cons (step725 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1929 : List Lit := [(96, true), (52, true), (88, true), (86, false), (107, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c726, c350] c1929 (by decide) p (sat_cons (step726 p h) (sat_cons (step350 p h) (sat_nil p)))
def c1930 : List Lit := [(96, true), (88, true), (107, true), (86, false), (17, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c726, c351] c1930 (by decide) p (sat_cons (step726 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1931 : List Lit := [(96, true), (52, true), (107, true), (86, false), (17, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c726, c352] c1931 (by decide) p (sat_cons (step726 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1932 : List Lit := [(86, false), (88, true), (17, true), (52, true), (107, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c726, c353] c1932 (by decide) p (sat_cons (step726 p h) (sat_cons (step353 p h) (sat_nil p)))
def c1933 : List Lit := [(96, true), (86, false), (52, true), (88, true), (17, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c726, c354] c1933 (by decide) p (sat_cons (step726 p h) (sat_cons (step354 p h) (sat_nil p)))
def c1934 : List Lit := [(83, true), (87, false), (110, true), (90, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c727, c356] c1934 (by decide) p (sat_cons (step727 p h) (sat_cons (step356 p h) (sat_nil p)))
def c1935 : List Lit := [(19, true), (87, false), (110, true), (90, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c727, c357] c1935 (by decide) p (sat_cons (step727 p h) (sat_cons (step357 p h) (sat_nil p)))
def c1936 : List Lit := [(19, true), (83, true), (87, false), (90, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c727, c358] c1936 (by decide) p (sat_cons (step727 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1937 : List Lit := [(99, true), (90, true), (88, true), (89, false), (85, true), (112, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c728, c372] c1937 (by decide) p (sat_cons (step728 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1938 : List Lit := [(99, true), (56, true), (112, true), (88, true), (89, false), (90, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c728, c373] c1938 (by decide) p (sat_cons (step728 p h) (sat_cons (step373 p h) (sat_nil p)))
def c1939 : List Lit := [(56, true), (85, true), (89, false), (88, true), (99, true), (112, true)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c728, c374] c1939 (by decide) p (sat_cons (step728 p h) (sat_cons (step374 p h) (sat_nil p)))
def c1940 : List Lit := [(93, true), (96, true), (91, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c729, c381] c1940 (by decide) p (sat_cons (step729 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1941 : List Lit := [(96, true), (91, false), (92, true)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c729, c382] c1941 (by decide) p (sat_cons (step729 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1942 : List Lit := [(93, true), (91, false), (92, true)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c729, c383] c1942 (by decide) p (sat_cons (step729 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1943 : List Lit := [(93, true), (58, true), (92, true), (94, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c730, c407] c1943 (by decide) p (sat_cons (step730 p h) (sat_cons (step407 p h) (sat_nil p)))
def c1944 : List Lit := [(83, true), (58, true), (93, true), (94, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c730, c408] c1944 (by decide) p (sat_cons (step730 p h) (sat_cons (step408 p h) (sat_nil p)))
def c1945 : List Lit := [(83, true), (58, true), (94, false), (92, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c730, c409] c1945 (by decide) p (sat_cons (step730 p h) (sat_cons (step409 p h) (sat_nil p)))
def c1946 : List Lit := [(85, true), (117, true), (93, true), (95, false), (99, true)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c731, c414] c1946 (by decide) p (sat_cons (step731 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1947 : List Lit := [(93, true), (24, true), (95, false), (99, true), (117, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c731, c415] c1947 (by decide) p (sat_cons (step731 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1948 : List Lit := [(24, true), (85, true), (117, true), (99, true), (95, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c731, c416] c1948 (by decide) p (sat_cons (step731 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1949 : List Lit := [(24, true), (85, true), (93, true), (99, true), (95, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c731, c417] c1949 (by decide) p (sat_cons (step731 p h) (sat_cons (step417 p h) (sat_nil p)))
def c1950 : List Lit := [(96, true), (98, true), (99, true), (97, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c732, c424] c1950 (by decide) p (sat_cons (step732 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1951 : List Lit := [(98, true), (88, true), (97, false), (99, true)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c732, c425] c1951 (by decide) p (sat_cons (step732 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1952 : List Lit := [(96, true), (88, true), (99, true), (97, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c732, c426] c1952 (by decide) p (sat_cons (step732 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1953 : List Lit := [(96, true), (98, true), (97, false), (88, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c732, c427] c1953 (by decide) p (sat_cons (step732 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1954 : List Lit := [(98, true), (99, true), (100, false), (123, true)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c733, c440] c1954 (by decide) p (sat_cons (step733 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1955 : List Lit := [(90, true), (99, true), (100, false), (123, true)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c733, c441] c1955 (by decide) p (sat_cons (step733 p h) (sat_cons (step441 p h) (sat_nil p)))
def c1956 : List Lit := [(90, true), (98, true), (100, false), (123, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c733, c442] c1956 (by decide) p (sat_cons (step733 p h) (sat_cons (step442 p h) (sat_nil p)))
def c1957 : List Lit := [(90, true), (98, true), (100, false), (99, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c733, c443] c1957 (by decide) p (sat_cons (step733 p h) (sat_cons (step443 p h) (sat_nil p)))
def c1958 : List Lit := [(103, true), (104, true), (107, true), (101, false)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c734, c444] c1958 (by decide) p (sat_cons (step734 p h) (sat_cons (step444 p h) (sat_nil p)))
def c1959 : List Lit := [(104, true), (107, true), (102, true), (101, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c734, c445] c1959 (by decide) p (sat_cons (step734 p h) (sat_cons (step445 p h) (sat_nil p)))
def c1960 : List Lit := [(103, true), (107, true), (101, false), (102, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c734, c446] c1960 (by decide) p (sat_cons (step734 p h) (sat_cons (step446 p h) (sat_nil p)))
def c1961 : List Lit := [(103, true), (104, true), (101, false), (102, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c734, c447] c1961 (by decide) p (sat_cons (step734 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1962 : List Lit := [(103, true), (110, true), (109, false), (112, true), (107, true)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c735, c544] c1962 (by decide) p (sat_cons (step735 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1963 : List Lit := [(112, true), (104, true), (107, true), (111, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c736, c557] c1963 (by decide) p (sat_cons (step736 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1964 : List Lit := [(112, true), (107, true), (88, true), (111, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c736, c558] c1964 (by decide) p (sat_cons (step736 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1965 : List Lit := [(112, true), (104, true), (88, true), (111, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c736, c559] c1965 (by decide) p (sat_cons (step736 p h) (sat_cons (step559 p h) (sat_nil p)))
def c1966 : List Lit := [(104, true), (88, true), (107, true), (111, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c736, c560] c1966 (by decide) p (sat_cons (step736 p h) (sat_cons (step560 p h) (sat_nil p)))
def c1967 : List Lit := [(73, true), (90, true), (113, false), (112, true), (110, true), (123, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c737, c605] c1967 (by decide) p (sat_cons (step737 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1968 : List Lit := [(119, true), (116, true), (114, false), (102, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c738, c608] c1968 (by decide) p (sat_cons (step738 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1969 : List Lit := [(119, true), (116, true), (92, true), (114, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c738, c609] c1969 (by decide) p (sat_cons (step738 p h) (sat_cons (step609 p h) (sat_nil p)))
def c1970 : List Lit := [(119, true), (92, true), (102, true), (114, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c738, c610] c1970 (by decide) p (sat_cons (step738 p h) (sat_cons (step610 p h) (sat_nil p)))
def c1971 : List Lit := [(116, true), (92, true), (102, true), (114, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c738, c611] c1971 (by decide) p (sat_cons (step738 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1972 : List Lit := [(77, true), (104, true), (117, true), (115, false), (116, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c739, c613] c1972 (by decide) p (sat_cons (step739 p h) (sat_cons (step613 p h) (sat_nil p)))
def c1973 : List Lit := [(41, true), (77, true), (115, false), (104, true), (116, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c739, c614] c1973 (by decide) p (sat_cons (step739 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1974 : List Lit := [(117, true), (118, false), (123, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c740, c630] c1974 (by decide) p (sat_cons (step740 p h) (sat_cons (step630 p h) (sat_nil p)))
def c1975 : List Lit := [(118, false), (116, true), (123, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c740, c631] c1975 (by decide) p (sat_cons (step740 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1976 : List Lit := [(117, true), (118, false), (116, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c740, c632] c1976 (by decide) p (sat_cons (step740 p h) (sat_cons (step632 p h) (sat_nil p)))
def c1977 : List Lit := [(120, true), (119, true), (123, true), (121, false)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c741, c640] c1977 (by decide) p (sat_cons (step741 p h) (sat_cons (step640 p h) (sat_nil p)))
def c1978 : List Lit := [(120, true), (110, true), (123, true), (121, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c741, c641] c1978 (by decide) p (sat_cons (step741 p h) (sat_cons (step641 p h) (sat_nil p)))
end B112E097
