import B112E004Part0003
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1990 : List Lit := [(66, true), (50, true), (72, true), (71, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c811, c518] c1990 (by decide) p (sat_cons (step811 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1991 : List Lit := [(29, true), (72, true), (66, true), (71, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c811, c519] c1991 (by decide) p (sat_cons (step811 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1992 : List Lit := [(29, true), (50, true), (71, false), (72, true)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c811, c520] c1992 (by decide) p (sat_cons (step811 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1993 : List Lit := [(66, true), (29, true), (71, false), (50, true)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c811, c521] c1993 (by decide) p (sat_cons (step811 p h) (sat_cons (step521 p h) (sat_nil p)))
def c1994 : List Lit := [(74, true), (65, true), (73, false)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c812, c527] c1994 (by decide) p (sat_cons (step812 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1995 : List Lit := [(74, true), (55, true), (73, false)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c812, c528] c1995 (by decide) p (sat_cons (step812 p h) (sat_cons (step528 p h) (sat_nil p)))
def c1996 : List Lit := [(55, true), (65, true), (73, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c812, c529] c1996 (by decide) p (sat_cons (step812 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1997 : List Lit := [(16, true), (77, true), (78, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c813, c542] c1997 (by decide) p (sat_cons (step813 p h) (sat_cons (step542 p h) (sat_nil p)))
def c1998 : List Lit := [(80, false), (81, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c814, c551] c1998 (by decide) p (sat_cons (step814 p h) (sat_cons (step551 p h) (sat_nil p)))
def c1999 : List Lit := [(80, false), (79, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c814, c552] c1999 (by decide) p (sat_cons (step814 p h) (sat_cons (step552 p h) (sat_nil p)))
def c2000 : List Lit := [(82, false), (79, true)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c815, c557] c2000 (by decide) p (sat_cons (step815 p h) (sat_cons (step557 p h) (sat_nil p)))
def c2001 : List Lit := [(82, false), (29, true)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c815, c558] c2001 (by decide) p (sat_cons (step815 p h) (sat_cons (step558 p h) (sat_nil p)))
def c2002 : List Lit := [(81, true), (118, true), (77, true), (83, false)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c816, c563] c2002 (by decide) p (sat_cons (step816 p h) (sat_cons (step563 p h) (sat_nil p)))
def c2003 : List Lit := [(104, true), (94, true), (84, false), (34, true), (89, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c817, c568] c2003 (by decide) p (sat_cons (step817 p h) (sat_cons (step568 p h) (sat_nil p)))
def c2004 : List Lit := [(96, true), (88, true), (86, false)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c818, c574] c2004 (by decide) p (sat_cons (step818 p h) (sat_cons (step574 p h) (sat_nil p)))
def c2005 : List Lit := [(85, true), (96, true), (86, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c818, c575] c2005 (by decide) p (sat_cons (step818 p h) (sat_cons (step575 p h) (sat_nil p)))
def c2006 : List Lit := [(85, true), (88, true), (86, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c818, c576] c2006 (by decide) p (sat_cons (step818 p h) (sat_cons (step576 p h) (sat_nil p)))
def c2007 : List Lit := [(93, true), (88, true), (87, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c819, c578] c2007 (by decide) p (sat_cons (step819 p h) (sat_cons (step578 p h) (sat_nil p)))
def c2008 : List Lit := [(85, true), (93, true), (87, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c819, c579] c2008 (by decide) p (sat_cons (step819 p h) (sat_cons (step579 p h) (sat_nil p)))
def c2009 : List Lit := [(85, true), (88, true), (87, false)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c819, c580] c2009 (by decide) p (sat_cons (step819 p h) (sat_cons (step580 p h) (sat_nil p)))
def c2010 : List Lit := [(92, true), (99, true), (90, false), (89, true)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c820, c603] c2010 (by decide) p (sat_cons (step820 p h) (sat_cons (step603 p h) (sat_nil p)))
def c2011 : List Lit := [(39, true), (92, true), (99, true), (90, false)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c820, c604] c2011 (by decide) p (sat_cons (step820 p h) (sat_cons (step604 p h) (sat_nil p)))
def c2012 : List Lit := [(39, true), (99, true), (89, true), (90, false)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c820, c605] c2012 (by decide) p (sat_cons (step820 p h) (sat_cons (step605 p h) (sat_nil p)))
def c2013 : List Lit := [(39, true), (92, true), (90, false), (89, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c820, c606] c2013 (by decide) p (sat_cons (step820 p h) (sat_cons (step606 p h) (sat_nil p)))
def c2014 : List Lit := [(93, true), (92, true), (91, false), (100, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c821, c610] c2014 (by decide) p (sat_cons (step821 p h) (sat_cons (step610 p h) (sat_nil p)))
def c2015 : List Lit := [(93, true), (100, true), (91, false), (89, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c821, c611] c2015 (by decide) p (sat_cons (step821 p h) (sat_cons (step611 p h) (sat_nil p)))
def c2016 : List Lit := [(92, true), (100, true), (89, true), (91, false)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c821, c612] c2016 (by decide) p (sat_cons (step821 p h) (sat_cons (step612 p h) (sat_nil p)))
def c2017 : List Lit := [(95, true), (49, true), (96, true), (97, false)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c822, c639] c2017 (by decide) p (sat_cons (step822 p h) (sat_cons (step639 p h) (sat_nil p)))
def c2018 : List Lit := [(96, true), (88, true), (49, true), (97, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c822, c640] c2018 (by decide) p (sat_cons (step822 p h) (sat_cons (step640 p h) (sat_nil p)))
def c2019 : List Lit := [(95, true), (88, true), (97, false), (49, true)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c822, c641] c2019 (by decide) p (sat_cons (step822 p h) (sat_cons (step641 p h) (sat_nil p)))
def c2020 : List Lit := [(94, true), (99, true), (98, false), (89, true), (100, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c823, c642] c2020 (by decide) p (sat_cons (step823 p h) (sat_cons (step642 p h) (sat_nil p)))
def c2021 : List Lit := [(94, true), (99, true), (100, true), (98, false), (50, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c823, c643] c2021 (by decide) p (sat_cons (step823 p h) (sat_cons (step643 p h) (sat_nil p)))
def c2022 : List Lit := [(99, true), (50, true), (98, false), (100, true), (89, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c823, c644] c2022 (by decide) p (sat_cons (step823 p h) (sat_cons (step644 p h) (sat_nil p)))
def c2023 : List Lit := [(94, true), (50, true), (98, false), (89, true), (100, true)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c823, c645] c2023 (by decide) p (sat_cons (step823 p h) (sat_cons (step645 p h) (sat_nil p)))
def c2024 : List Lit := [(94, true), (99, true), (98, false), (50, true), (89, true)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c823, c646] c2024 (by decide) p (sat_cons (step823 p h) (sat_cons (step646 p h) (sat_nil p)))
def c2025 : List Lit := [(95, true), (92, true), (100, true), (101, false), (118, true), (99, true)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c824, c693] c2025 (by decide) p (sat_cons (step824 p h) (sat_cons (step693 p h) (sat_nil p)))
def c2026 : List Lit := [(95, true), (99, true), (77, true), (118, true), (100, true), (101, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c824, c694] c2026 (by decide) p (sat_cons (step824 p h) (sat_cons (step694 p h) (sat_nil p)))
def c2027 : List Lit := [(92, true), (99, true), (101, false), (118, true), (77, true), (100, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c824, c695] c2027 (by decide) p (sat_cons (step824 p h) (sat_cons (step695 p h) (sat_nil p)))
def c2028 : List Lit := [(95, true), (77, true), (101, false), (99, true), (92, true), (100, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c824, c696] c2028 (by decide) p (sat_cons (step824 p h) (sat_cons (step696 p h) (sat_nil p)))
def c2029 : List Lit := [(96, true), (99, true), (102, false), (120, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c825, c699] c2029 (by decide) p (sat_cons (step825 p h) (sat_cons (step699 p h) (sat_nil p)))
def c2030 : List Lit := [(54, true), (99, true), (120, true), (102, false)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c825, c700] c2030 (by decide) p (sat_cons (step825 p h) (sat_cons (step700 p h) (sat_nil p)))
def c2031 : List Lit := [(96, true), (54, true), (120, true), (102, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c825, c701] c2031 (by decide) p (sat_cons (step825 p h) (sat_cons (step701 p h) (sat_nil p)))
def c2032 : List Lit := [(54, true), (96, true), (99, true), (102, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c825, c702] c2032 (by decide) p (sat_cons (step825 p h) (sat_cons (step702 p h) (sat_nil p)))
def c2033 : List Lit := [(93, true), (103, false), (100, true)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c826, c704] c2033 (by decide) p (sat_cons (step826 p h) (sat_cons (step704 p h) (sat_nil p)))
def c2034 : List Lit := [(55, true), (103, false), (100, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c826, c705] c2034 (by decide) p (sat_cons (step826 p h) (sat_cons (step705 p h) (sat_nil p)))
def c2035 : List Lit := [(93, true), (55, true), (103, false)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c826, c706] c2035 (by decide) p (sat_cons (step826 p h) (sat_cons (step706 p h) (sat_nil p)))
def c2036 : List Lit := [(105, false), (107, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c827, c713] c2036 (by decide) p (sat_cons (step827 p h) (sat_cons (step713 p h) (sat_nil p)))
def c2037 : List Lit := [(105, false), (104, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c827, c714] c2037 (by decide) p (sat_cons (step827 p h) (sat_cons (step714 p h) (sat_nil p)))
def c2038 : List Lit := [(113, true), (104, true), (106, false), (107, true)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c828, c716] c2038 (by decide) p (sat_cons (step828 p h) (sat_cons (step716 p h) (sat_nil p)))
def c2039 : List Lit := [(104, true), (57, true), (106, false), (107, true)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c828, c717] c2039 (by decide) p (sat_cons (step828 p h) (sat_cons (step717 p h) (sat_nil p)))
def c2040 : List Lit := [(112, true), (108, false), (88, true)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c829, c725] c2040 (by decide) p (sat_cons (step829 p h) (sat_cons (step725 p h) (sat_nil p)))
def c2041 : List Lit := [(107, true), (108, false), (88, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c829, c726] c2041 (by decide) p (sat_cons (step829 p h) (sat_cons (step726 p h) (sat_nil p)))
def c2042 : List Lit := [(104, true), (89, true), (109, false), (110, true)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c830, c730] c2042 (by decide) p (sat_cons (step830 p h) (sat_cons (step730 p h) (sat_nil p)))
def c2043 : List Lit := [(79, true), (104, true), (109, false), (110, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c830, c731] c2043 (by decide) p (sat_cons (step830 p h) (sat_cons (step731 p h) (sat_nil p)))
def c2044 : List Lit := [(79, true), (89, true), (109, false), (110, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c830, c732] c2044 (by decide) p (sat_cons (step830 p h) (sat_cons (step732 p h) (sat_nil p)))
def c2045 : List Lit := [(120, true), (112, true), (111, false)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c831, c737] c2045 (by decide) p (sat_cons (step831 p h) (sat_cons (step737 p h) (sat_nil p)))
def c2046 : List Lit := [(120, true), (110, true), (111, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c831, c738] c2046 (by decide) p (sat_cons (step831 p h) (sat_cons (step738 p h) (sat_nil p)))
def c2047 : List Lit := [(112, true), (110, true), (111, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c831, c739] c2047 (by decide) p (sat_cons (step831 p h) (sat_cons (step739 p h) (sat_nil p)))
def c2048 : List Lit := [(113, true), (118, true), (114, false), (107, true), (95, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c832, c753] c2048 (by decide) p (sat_cons (step832 p h) (sat_cons (step753 p h) (sat_nil p)))
def c2049 : List Lit := [(116, false), (115, true)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c833, c757] c2049 (by decide) p (sat_cons (step833 p h) (sat_cons (step757 p h) (sat_nil p)))
def c2050 : List Lit := [(116, false), (113, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c833, c758] c2050 (by decide) p (sat_cons (step833 p h) (sat_cons (step758 p h) (sat_nil p)))
def c2051 : List Lit := [(113, true), (118, true), (117, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c834, c760] c2051 (by decide) p (sat_cons (step834 p h) (sat_cons (step760 p h) (sat_nil p)))
def c2052 : List Lit := [(118, true), (117, false), (100, true)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c834, c761] c2052 (by decide) p (sat_cons (step834 p h) (sat_cons (step761 p h) (sat_nil p)))
def c2053 : List Lit := [(113, true), (100, true), (117, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c834, c762] c2053 (by decide) p (sat_cons (step834 p h) (sat_cons (step762 p h) (sat_nil p)))
end B112E004
