import B112E121Part0003
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1980 : List Lit := [(50, true), (58, true), (59, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c907, c481] c1980 (by decide) p (sat_cons (step907 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1981 : List Lit := [(58, true), (30, true), (61, true), (60, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c908, c483] c1981 (by decide) p (sat_cons (step908 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1982 : List Lit := [(56, true), (30, true), (61, true), (60, false)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c908, c484] c1982 (by decide) p (sat_cons (step908 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1983 : List Lit := [(65, true), (67, true), (66, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c909, c507] c1983 (by decide) p (sat_cons (step909 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1984 : List Lit := [(67, true), (66, false), (62, true)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c909, c508] c1984 (by decide) p (sat_cons (step909 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1985 : List Lit := [(65, true), (66, false), (62, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c909, c509] c1985 (by decide) p (sat_cons (step909 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1986 : List Lit := [(67, true), (61, true), (68, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c910, c513] c1986 (by decide) p (sat_cons (step910 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1987 : List Lit := [(70, true), (69, false), (87, true), (73, true)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c911, c517] c1987 (by decide) p (sat_cons (step911 p h) (sat_cons (step517 p h) (sat_nil p)))
def c1988 : List Lit := [(8, true), (69, false), (87, true), (73, true)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c911, c518] c1988 (by decide) p (sat_cons (step911 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1989 : List Lit := [(70, true), (69, false), (8, true), (87, true)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c911, c519] c1989 (by decide) p (sat_cons (step911 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1990 : List Lit := [(70, true), (69, false), (8, true), (73, true)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c911, c520] c1990 (by decide) p (sat_cons (step911 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1991 : List Lit := [(82, true), (72, true), (71, false), (92, true)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c912, c535] c1991 (by decide) p (sat_cons (step912 p h) (sat_cons (step535 p h) (sat_nil p)))
def c1992 : List Lit := [(82, true), (71, false), (92, true), (13, true)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c912, c536] c1992 (by decide) p (sat_cons (step912 p h) (sat_cons (step536 p h) (sat_nil p)))
def c1993 : List Lit := [(72, true), (71, false), (92, true), (13, true)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c912, c537] c1993 (by decide) p (sat_cons (step912 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1994 : List Lit := [(82, true), (72, true), (71, false), (13, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c912, c538] c1994 (by decide) p (sat_cons (step912 p h) (sat_cons (step538 p h) (sat_nil p)))
def c1995 : List Lit := [(76, true), (75, true), (77, false), (99, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c914, c557] c1995 (by decide) p (sat_cons (step914 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1996 : List Lit := [(76, true), (72, true), (99, true), (77, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c914, c558] c1996 (by decide) p (sat_cons (step914 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1997 : List Lit := [(75, true), (72, true), (99, true), (77, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c914, c559] c1997 (by decide) p (sat_cons (step914 p h) (sat_cons (step559 p h) (sat_nil p)))
def c1998 : List Lit := [(70, true), (80, true), (100, true), (78, false)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c915, c562] c1998 (by decide) p (sat_cons (step915 p h) (sat_cons (step562 p h) (sat_nil p)))
def c1999 : List Lit := [(20, true), (80, true), (100, true), (78, false)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c915, c563] c1999 (by decide) p (sat_cons (step915 p h) (sat_cons (step563 p h) (sat_nil p)))
def c2000 : List Lit := [(70, true), (20, true), (100, true), (78, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c915, c564] c2000 (by decide) p (sat_cons (step915 p h) (sat_cons (step564 p h) (sat_nil p)))
def c2001 : List Lit := [(80, true), (78, false), (70, true), (20, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c915, c565] c2001 (by decide) p (sat_cons (step915 p h) (sat_cons (step565 p h) (sat_nil p)))
def c2002 : List Lit := [(80, true), (82, true), (83, true), (79, false)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c916, c567] c2002 (by decide) p (sat_cons (step916 p h) (sat_cons (step567 p h) (sat_nil p)))
def c2003 : List Lit := [(82, true), (21, true), (83, true), (79, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c916, c568] c2003 (by decide) p (sat_cons (step916 p h) (sat_cons (step568 p h) (sat_nil p)))
def c2004 : List Lit := [(80, true), (21, true), (79, false), (83, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c916, c569] c2004 (by decide) p (sat_cons (step916 p h) (sat_cons (step569 p h) (sat_nil p)))
def c2005 : List Lit := [(80, true), (82, true), (79, false), (21, true)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c916, c570] c2005 (by decide) p (sat_cons (step916 p h) (sat_cons (step570 p h) (sat_nil p)))
def c2006 : List Lit := [(85, false), (76, true)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c917, c592] c2006 (by decide) p (sat_cons (step917 p h) (sat_cons (step592 p h) (sat_nil p)))
def c2007 : List Lit := [(82, true), (83, true), (30, true), (86, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c918, c593] c2007 (by decide) p (sat_cons (step918 p h) (sat_cons (step593 p h) (sat_nil p)))
def c2008 : List Lit := [(91, true), (88, false), (111, true), (70, true), (100, true), (87, true)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c919, c637] c2008 (by decide) p (sat_cons (step919 p h) (sat_cons (step637 p h) (sat_nil p)))
def c2009 : List Lit := [(45, true), (70, true), (88, false), (91, true), (111, true), (100, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c919, c638] c2009 (by decide) p (sat_cons (step919 p h) (sat_cons (step638 p h) (sat_nil p)))
def c2010 : List Lit := [(70, true), (45, true), (88, false), (87, true), (91, true), (100, true)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c919, c639] c2010 (by decide) p (sat_cons (step919 p h) (sat_cons (step639 p h) (sat_nil p)))
def c2011 : List Lit := [(89, false), (95, true), (92, true)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c920, c640] c2011 (by decide) p (sat_cons (step920 p h) (sat_cons (step640 p h) (sat_nil p)))
def c2012 : List Lit := [(95, true), (89, false), (87, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c920, c641] c2012 (by decide) p (sat_cons (step920 p h) (sat_cons (step641 p h) (sat_nil p)))
def c2013 : List Lit := [(89, false), (92, true), (87, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c920, c642] c2013 (by decide) p (sat_cons (step920 p h) (sat_cons (step642 p h) (sat_nil p)))
def c2014 : List Lit := [(97, true), (102, true), (90, false), (92, true), (87, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c921, c648] c2014 (by decide) p (sat_cons (step921 p h) (sat_cons (step648 p h) (sat_nil p)))
def c2015 : List Lit := [(102, true), (91, true), (87, true), (92, true), (90, false)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c921, c649] c2015 (by decide) p (sat_cons (step921 p h) (sat_cons (step649 p h) (sat_nil p)))
def c2016 : List Lit := [(97, true), (91, true), (87, true), (90, false), (92, true)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c921, c650] c2016 (by decide) p (sat_cons (step921 p h) (sat_cons (step650 p h) (sat_nil p)))
def c2017 : List Lit := [(104, true), (91, true), (93, false), (92, true), (72, true), (99, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c922, c700] c2017 (by decide) p (sat_cons (step922 p h) (sat_cons (step700 p h) (sat_nil p)))
def c2018 : List Lit := [(108, true), (75, true), (116, true), (99, true), (95, true), (96, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c923, c727] c2018 (by decide) p (sat_cons (step923 p h) (sat_cons (step727 p h) (sat_nil p)))
def c2019 : List Lit := [(108, true), (49, true), (116, true), (99, true), (95, true), (96, false)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c923, c728] c2019 (by decide) p (sat_cons (step923 p h) (sat_cons (step728 p h) (sat_nil p)))
def c2020 : List Lit := [(49, true), (75, true), (96, false), (95, true), (99, true), (108, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c923, c729] c2020 (by decide) p (sat_cons (step923 p h) (sat_cons (step729 p h) (sat_nil p)))
def c2021 : List Lit := [(97, true), (98, false), (99, true), (95, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c924, c734] c2021 (by decide) p (sat_cons (step924 p h) (sat_cons (step734 p h) (sat_nil p)))
def c2022 : List Lit := [(98, false), (97, true), (92, true), (99, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c924, c735] c2022 (by decide) p (sat_cons (step924 p h) (sat_cons (step735 p h) (sat_nil p)))
def c2023 : List Lit := [(95, true), (98, false), (99, true), (92, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c924, c736] c2023 (by decide) p (sat_cons (step924 p h) (sat_cons (step736 p h) (sat_nil p)))
def c2024 : List Lit := [(97, true), (95, true), (98, false), (92, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c924, c737] c2024 (by decide) p (sat_cons (step924 p h) (sat_cons (step737 p h) (sat_nil p)))
def c2025 : List Lit := [(102, true), (103, false), (100, true), (104, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c925, c809] c2025 (by decide) p (sat_cons (step925 p h) (sat_cons (step809 p h) (sat_nil p)))
def c2026 : List Lit := [(102, true), (91, true), (104, true), (103, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c925, c810] c2026 (by decide) p (sat_cons (step925 p h) (sat_cons (step810 p h) (sat_nil p)))
def c2027 : List Lit := [(103, false), (104, true), (91, true), (100, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c925, c811] c2027 (by decide) p (sat_cons (step925 p h) (sat_cons (step811 p h) (sat_nil p)))
def c2028 : List Lit := [(102, true), (103, false), (91, true), (100, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c925, c812] c2028 (by decide) p (sat_cons (step925 p h) (sat_cons (step812 p h) (sat_nil p)))
def c2029 : List Lit := [(108, true), (106, false), (105, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c926, c822] c2029 (by decide) p (sat_cons (step926 p h) (sat_cons (step822 p h) (sat_nil p)))
def c2030 : List Lit := [(106, false), (108, true), (100, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c926, c823] c2030 (by decide) p (sat_cons (step926 p h) (sat_cons (step823 p h) (sat_nil p)))
def c2031 : List Lit := [(106, false), (100, true), (105, true)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c926, c824] c2031 (by decide) p (sat_cons (step926 p h) (sat_cons (step824 p h) (sat_nil p)))
def c2032 : List Lit := [(123, true), (108, true), (107, false), (95, true), (105, true)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c927, c828] c2032 (by decide) p (sat_cons (step927 p h) (sat_cons (step828 p h) (sat_nil p)))
def c2033 : List Lit := [(123, true), (108, true), (83, true), (107, false), (95, true)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c927, c829] c2033 (by decide) p (sat_cons (step927 p h) (sat_cons (step829 p h) (sat_nil p)))
def c2034 : List Lit := [(108, true), (83, true), (95, true), (107, false), (105, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c927, c830] c2034 (by decide) p (sat_cons (step927 p h) (sat_cons (step830 p h) (sat_nil p)))
def c2035 : List Lit := [(109, false), (108, true), (104, true), (99, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c928, c841] c2035 (by decide) p (sat_cons (step928 p h) (sat_cons (step841 p h) (sat_nil p)))
def c2036 : List Lit := [(109, false), (61, true), (104, true), (108, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c928, c842] c2036 (by decide) p (sat_cons (step928 p h) (sat_cons (step842 p h) (sat_nil p)))
def c2037 : List Lit := [(109, false), (108, true), (99, true), (61, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c928, c843] c2037 (by decide) p (sat_cons (step928 p h) (sat_cons (step843 p h) (sat_nil p)))
def c2038 : List Lit := [(109, false), (61, true), (99, true), (104, true)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c928, c844] c2038 (by decide) p (sat_cons (step928 p h) (sat_cons (step844 p h) (sat_nil p)))
def c2039 : List Lit := [(114, true), (110, false), (111, true)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c929, c845] c2039 (by decide) p (sat_cons (step929 p h) (sat_cons (step845 p h) (sat_nil p)))
def c2040 : List Lit := [(114, true), (110, false), (87, true)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c929, c846] c2040 (by decide) p (sat_cons (step929 p h) (sat_cons (step846 p h) (sat_nil p)))
def c2041 : List Lit := [(111, true), (110, false), (87, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c929, c847] c2041 (by decide) p (sat_cons (step929 p h) (sat_cons (step847 p h) (sat_nil p)))
def c2042 : List Lit := [(112, false), (113, true), (122, true)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c930, c853] c2042 (by decide) p (sat_cons (step930 p h) (sat_cons (step853 p h) (sat_nil p)))
def c2043 : List Lit := [(112, false), (122, true), (92, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c930, c854] c2043 (by decide) p (sat_cons (step930 p h) (sat_cons (step854 p h) (sat_nil p)))
end B112E121
