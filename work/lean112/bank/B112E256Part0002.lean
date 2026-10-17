import B112E256Part0001
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1972 : List Lit := [(45, true), (51, false), (70, true), (42, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c795, c348] c1972 (by decide) p (sat_cons (step795 p h) (sat_cons (step348 p h) (sat_nil p)))
def c1973 : List Lit := [(51, false), (15, true), (70, true), (42, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c795, c349] c1973 (by decide) p (sat_cons (step795 p h) (sat_cons (step349 p h) (sat_nil p)))
def c1974 : List Lit := [(54, false), (49, true), (44, true), (53, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c797, c367] c1974 (by decide) p (sat_cons (step797 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1975 : List Lit := [(54, false), (49, true), (18, true), (53, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c797, c368] c1975 (by decide) p (sat_cons (step797 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1976 : List Lit := [(44, true), (54, false), (53, true), (18, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c797, c369] c1976 (by decide) p (sat_cons (step797 p h) (sat_cons (step369 p h) (sat_nil p)))
def c1977 : List Lit := [(55, false), (36, true), (57, true), (63, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c798, c374] c1977 (by decide) p (sat_cons (step798 p h) (sat_cons (step374 p h) (sat_nil p)))
def c1978 : List Lit := [(19, true), (55, false), (57, true), (63, true)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c798, c375] c1978 (by decide) p (sat_cons (step798 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1979 : List Lit := [(19, true), (36, true), (55, false), (63, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c798, c376] c1979 (by decide) p (sat_cons (step798 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1980 : List Lit := [(19, true), (36, true), (55, false), (57, true)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c798, c377] c1980 (by decide) p (sat_cons (step798 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1981 : List Lit := [(60, true), (56, false), (65, true)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c799, c379] c1981 (by decide) p (sat_cons (step799 p h) (sat_cons (step379 p h) (sat_nil p)))
def c1982 : List Lit := [(56, false), (58, true), (65, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c799, c380] c1982 (by decide) p (sat_cons (step799 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1983 : List Lit := [(60, true), (42, true), (59, false), (70, true)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c800, c398] c1983 (by decide) p (sat_cons (step800 p h) (sat_cons (step398 p h) (sat_nil p)))
def c1984 : List Lit := [(60, true), (62, true), (59, false), (42, true)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c800, c399] c1984 (by decide) p (sat_cons (step800 p h) (sat_cons (step399 p h) (sat_nil p)))
def c1985 : List Lit := [(64, false), (63, true), (65, true), (67, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c801, c425] c1985 (by decide) p (sat_cons (step801 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1986 : List Lit := [(28, true), (64, false), (67, true), (65, true)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c801, c426] c1986 (by decide) p (sat_cons (step801 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1987 : List Lit := [(28, true), (64, false), (65, true), (63, true)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c801, c427] c1987 (by decide) p (sat_cons (step801 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1988 : List Lit := [(69, false), (70, true)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c803, c474] c1988 (by decide) p (sat_cons (step803 p h) (sat_cons (step474 p h) (sat_nil p)))
def c1989 : List Lit := [(69, false), (63, true)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c803, c475] c1989 (by decide) p (sat_cons (step803 p h) (sat_cons (step475 p h) (sat_nil p)))
def c1990 : List Lit := [(71, false), (70, true), (124, true), (65, true)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c804, c481] c1990 (by decide) p (sat_cons (step804 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1991 : List Lit := [(60, true), (70, true), (71, false), (65, true)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c804, c482] c1991 (by decide) p (sat_cons (step804 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1992 : List Lit := [(72, false), (67, true), (53, true), (126, true), (61, true)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c805, c488] c1992 (by decide) p (sat_cons (step805 p h) (sat_cons (step488 p h) (sat_nil p)))
def c1993 : List Lit := [(73, false), (34, true), (68, true), (70, true)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c806, c493] c1993 (by decide) p (sat_cons (step806 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1994 : List Lit := [(70, true), (73, false), (34, true), (62, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c806, c494] c1994 (by decide) p (sat_cons (step806 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1995 : List Lit := [(76, true), (75, false), (90, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c807, c501] c1995 (by decide) p (sat_cons (step807 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1996 : List Lit := [(75, false), (74, true), (90, true)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c807, c502] c1996 (by decide) p (sat_cons (step807 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1997 : List Lit := [(77, false), (101, true)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c808, c509] c1997 (by decide) p (sat_cons (step808 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1998 : List Lit := [(80, false), (93, true), (105, true), (90, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c809, c524] c1998 (by decide) p (sat_cons (step809 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1999 : List Lit := [(80, false), (78, true), (90, true), (105, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c809, c525] c1999 (by decide) p (sat_cons (step809 p h) (sat_cons (step525 p h) (sat_nil p)))
def c2000 : List Lit := [(78, true), (80, false), (90, true), (93, true)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c809, c526] c2000 (by decide) p (sat_cons (step809 p h) (sat_cons (step526 p h) (sat_nil p)))
def c2001 : List Lit := [(81, false), (91, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c810, c527] c2001 (by decide) p (sat_cons (step810 p h) (sat_cons (step527 p h) (sat_nil p)))
def c2002 : List Lit := [(10, true), (84, true), (83, true), (106, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c535, c528] c2002 (by decide) p (sat_cons (step535 p h) (sat_cons (step528 p h) (sat_nil p)))
def c2003 : List Lit := [(10, false), (83, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c536, c529] c2003 (by decide) p (sat_cons (step536 p h) (sat_cons (step529 p h) (sat_nil p)))
def c2004 : List Lit := [(10, false), (84, false)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c536, c530] c2004 (by decide) p (sat_cons (step536 p h) (sat_cons (step530 p h) (sat_nil p)))
def c2005 : List Lit := [(10, false), (106, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c536, c531] c2005 (by decide) p (sat_cons (step536 p h) (sat_cons (step531 p h) (sat_nil p)))
def c2006 : List Lit := [(83, false), (84, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c536, c532] c2006 (by decide) p (sat_cons (step536 p h) (sat_cons (step532 p h) (sat_nil p)))
def c2007 : List Lit := [(83, false), (106, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c536, c533] c2007 (by decide) p (sat_cons (step536 p h) (sat_cons (step533 p h) (sat_nil p)))
def c2008 : List Lit := [(84, false), (106, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c536, c534] c2008 (by decide) p (sat_cons (step536 p h) (sat_cons (step534 p h) (sat_nil p)))
def c2009 : List Lit := [(109, true), (96, true), (85, false), (90, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c811, c542] c2009 (by decide) p (sat_cons (step811 p h) (sat_cons (step542 p h) (sat_nil p)))
def c2010 : List Lit := [(109, true), (90, true), (83, true), (85, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c811, c543] c2010 (by decide) p (sat_cons (step811 p h) (sat_cons (step543 p h) (sat_nil p)))
def c2011 : List Lit := [(85, false), (90, true), (83, true), (96, true)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c811, c544] c2011 (by decide) p (sat_cons (step811 p h) (sat_cons (step544 p h) (sat_nil p)))
def c2012 : List Lit := [(86, false), (91, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c812, c545] c2012 (by decide) p (sat_cons (step812 p h) (sat_cons (step545 p h) (sat_nil p)))
def c2013 : List Lit := [(87, false), (88, true), (74, true), (14, true), (83, true), (90, true), (111, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c813, c577] c2013 (by decide) p (sat_cons (step813 p h) (sat_cons (step577 p h) (sat_nil p)))
def c2014 : List Lit := [(89, false), (91, true), (90, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c814, c583] c2014 (by decide) p (sat_cons (step814 p h) (sat_cons (step583 p h) (sat_nil p)))
def c2015 : List Lit := [(93, true), (94, false), (101, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c816, c608] c2015 (by decide) p (sat_cons (step816 p h) (sat_cons (step608 p h) (sat_nil p)))
def c2016 : List Lit := [(95, false), (84, true)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c817, c609] c2016 (by decide) p (sat_cons (step817 p h) (sat_cons (step609 p h) (sat_nil p)))
def c2017 : List Lit := [(97, false), (122, true), (101, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c818, c614] c2017 (by decide) p (sat_cons (step818 p h) (sat_cons (step614 p h) (sat_nil p)))
def c2018 : List Lit := [(96, true), (97, false), (101, true)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c818, c615] c2018 (by decide) p (sat_cons (step818 p h) (sat_cons (step615 p h) (sat_nil p)))
def c2019 : List Lit := [(98, false), (124, true), (101, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c819, c616] c2019 (by decide) p (sat_cons (step819 p h) (sat_cons (step616 p h) (sat_nil p)))
def c2020 : List Lit := [(33, true), (96, true), (99, false), (90, true), (93, true), (101, true), (126, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c820, c641] c2020 (by decide) p (sat_cons (step820 p h) (sat_cons (step641 p h) (sat_nil p)))
def c2021 : List Lit := [(91, true), (34, true), (100, false)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c821, c642] c2021 (by decide) p (sat_cons (step821 p h) (sat_cons (step642 p h) (sat_nil p)))
def c2022 : List Lit := [(102, false), (42, true), (103, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c822, c655] c2022 (by decide) p (sat_cons (step822 p h) (sat_cons (step655 p h) (sat_nil p)))
def c2023 : List Lit := [(113, true), (104, false), (43, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c823, c661] c2023 (by decide) p (sat_cons (step823 p h) (sat_cons (step661 p h) (sat_nil p)))
def c2024 : List Lit := [(111, true), (109, true), (106, true), (107, false), (108, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c824, c670] c2024 (by decide) p (sat_cons (step824 p h) (sat_cons (step670 p h) (sat_nil p)))
def c2025 : List Lit := [(115, false), (91, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c828, c706] c2025 (by decide) p (sat_cons (step828 p h) (sat_cons (step706 p h) (sat_nil p)))
def c2026 : List Lit := [(118, true), (124, true), (119, false), (65, true), (122, true)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c830, c726] c2026 (by decide) p (sat_cons (step830 p h) (sat_cons (step726 p h) (sat_nil p)))
def c2027 : List Lit := [(123, false), (70, true), (124, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c832, c752] c2027 (by decide) p (sat_cons (step832 p h) (sat_cons (step752 p h) (sat_nil p)))
def c2028 : List Lit := [(125, false), (113, true), (126, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c833, c755] c2028 (by decide) p (sat_cons (step833 p h) (sat_cons (step755 p h) (sat_nil p)))
def c2029 : List Lit := [(124, true), (126, true), (101, true), (116, true), (127, false)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c834, c769] c2029 (by decide) p (sat_cons (step834 p h) (sat_cons (step769 p h) (sat_nil p)))
def c2030 : List Lit := [(128, false), (255, false)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1886, c838] c2030 (by decide) p (sat_cons (step1886 p h) (sat_cons (step838 p h) (sat_nil p)))
def c2031 : List Lit := [(259, false), (261, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1885, c843] c2031 (by decide) p (sat_cons (step1885 p h) (sat_cons (step843 p h) (sat_nil p)))
def c2032 : List Lit := [(257, false), (263, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c1872, c847] c2032 (by decide) p (sat_cons (step1872 p h) (sat_cons (step847 p h) (sat_nil p)))
def c2033 : List Lit := [(137, false), (138, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c1892, c851] c2033 (by decide) p (sat_cons (step1892 p h) (sat_cons (step851 p h) (sat_nil p)))
def c2034 : List Lit := [(141, false), (142, false)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c1891, c856] c2034 (by decide) p (sat_cons (step1891 p h) (sat_cons (step856 p h) (sat_nil p)))
def c2035 : List Lit := [(271, false), (277, false)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c1871, c862] c2035 (by decide) p (sat_cons (step1871 p h) (sat_cons (step862 p h) (sat_nil p)))
end B112E256
