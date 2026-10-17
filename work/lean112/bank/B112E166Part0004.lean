import B112E166Part0003
namespace B112E166
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c898 : List Lit := [(305, false), (317, false)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true :=
  Snake9.LocalRup.prove_clause [c653, c269] c898 (by decide) p (sat_cons (step653 p h) (sat_cons (step269 p h) (sat_nil p)))
def c899 : List Lit := [(269, false), (321, false)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true :=
  Snake9.LocalRup.prove_clause [c646, c275] c899 (by decide) p (sat_cons (step646 p h) (sat_cons (step275 p h) (sat_nil p)))
def c900 : List Lit := [(379, false), (383, false)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true :=
  Snake9.LocalRup.prove_clause [c655, c299] c900 (by decide) p (sat_cons (step655 p h) (sat_cons (step299 p h) (sat_nil p)))
def c901 : List Lit := [(385, false), (397, false)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true :=
  Snake9.LocalRup.prove_clause [c651, c303] c901 (by decide) p (sat_cons (step651 p h) (sat_cons (step303 p h) (sat_nil p)))
def c902 : List Lit := [(323, false), (429, false)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true :=
  Snake9.LocalRup.prove_clause [c312, c310] c902 (by decide) p (sat_cons (step312 p h) (sat_cons (step310 p h) (sat_nil p)))
def c903 : List Lit := [(1365, false), (1370, true)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true :=
  Snake9.LocalRup.prove_clause [c836, c402] c903 (by decide) p (sat_cons (step836 p h) (sat_cons (step402 p h) (sat_nil p)))
def c904 : List Lit := [(1366, false), (1371, true)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true :=
  Snake9.LocalRup.prove_clause [c836, c405] c904 (by decide) p (sat_cons (step836 p h) (sat_cons (step405 p h) (sat_nil p)))
def c905 : List Lit := [(1398, true), (1329, false)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true :=
  Snake9.LocalRup.prove_clause [c838, c441] c905 (by decide) p (sat_cons (step838 p h) (sat_cons (step441 p h) (sat_nil p)))
def c906 : List Lit := [(1331, false), (1400, true)]
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true :=
  Snake9.LocalRup.prove_clause [c838, c450] c906 (by decide) p (sat_cons (step838 p h) (sat_cons (step450 p h) (sat_nil p)))
def c907 : List Lit := [(1332, false), (1401, true)]
theorem step907 (p : Nat → Bool) (h : Constraints p) : clause p c907 = true :=
  Snake9.LocalRup.prove_clause [c838, c454] c907 (by decide) p (sat_cons (step838 p h) (sat_cons (step454 p h) (sat_nil p)))
def c908 : List Lit := [(1442, false), (1450, true)]
theorem step908 (p : Nat → Bool) (h : Constraints p) : clause p c908 = true :=
  Snake9.LocalRup.prove_clause [c670, c521] c908 (by decide) p (sat_cons (step670 p h) (sat_cons (step521 p h) (sat_nil p)))
def c909 : List Lit := [(1443, false), (1451, true)]
theorem step909 (p : Nat → Bool) (h : Constraints p) : clause p c909 = true :=
  Snake9.LocalRup.prove_clause [c670, c522] c909 (by decide) p (sat_cons (step670 p h) (sat_cons (step522 p h) (sat_nil p)))
def c910 : List Lit := [(1444, false), (1452, true)]
theorem step910 (p : Nat → Bool) (h : Constraints p) : clause p c910 = true :=
  Snake9.LocalRup.prove_clause [c670, c523] c910 (by decide) p (sat_cons (step670 p h) (sat_cons (step523 p h) (sat_nil p)))
def c911 : List Lit := [(1445, false), (1453, true)]
theorem step911 (p : Nat → Bool) (h : Constraints p) : clause p c911 = true :=
  Snake9.LocalRup.prove_clause [c670, c524] c911 (by decide) p (sat_cons (step670 p h) (sat_cons (step524 p h) (sat_nil p)))
def c912 : List Lit := [(1444, false), (1424, false)]
theorem step912 (p : Nat → Bool) (h : Constraints p) : clause p c912 = true :=
  Snake9.LocalRup.prove_clause [c781, c533] c912 (by decide) p (sat_cons (step781 p h) (sat_cons (step533 p h) (sat_nil p)))
def c913 : List Lit := [(1466, false), (1478, true)]
theorem step913 (p : Nat → Bool) (h : Constraints p) : clause p c913 = true :=
  Snake9.LocalRup.prove_clause [c753, c569] c913 (by decide) p (sat_cons (step753 p h) (sat_cons (step569 p h) (sat_nil p)))
def c914 : List Lit := [(1467, false), (1479, true)]
theorem step914 (p : Nat → Bool) (h : Constraints p) : clause p c914 = true :=
  Snake9.LocalRup.prove_clause [c753, c573] c914 (by decide) p (sat_cons (step753 p h) (sat_cons (step573 p h) (sat_nil p)))
def c915 : List Lit := [(1506, true), (1497, false)]
theorem step915 (p : Nat → Bool) (h : Constraints p) : clause p c915 = true :=
  Snake9.LocalRup.prove_clause [c754, c600] c915 (by decide) p (sat_cons (step754 p h) (sat_cons (step600 p h) (sat_nil p)))
def c916 : List Lit := [(1498, false), (1507, true)]
theorem step916 (p : Nat → Bool) (h : Constraints p) : clause p c916 = true :=
  Snake9.LocalRup.prove_clause [c754, c601] c916 (by decide) p (sat_cons (step754 p h) (sat_cons (step601 p h) (sat_nil p)))
def c917 : List Lit := [(1478, false), (1506, true)]
theorem step917 (p : Nat → Bool) (h : Constraints p) : clause p c917 = true :=
  Snake9.LocalRup.prove_clause [c733, c602] c917 (by decide) p (sat_cons (step733 p h) (sat_cons (step602 p h) (sat_nil p)))
def c918 : List Lit := [(1479, false), (1507, true)]
theorem step918 (p : Nat → Bool) (h : Constraints p) : clause p c918 = true :=
  Snake9.LocalRup.prove_clause [c733, c605] c918 (by decide) p (sat_cons (step733 p h) (sat_cons (step605 p h) (sat_nil p)))
def c919 : List Lit := [(1480, false), (1508, true)]
theorem step919 (p : Nat → Bool) (h : Constraints p) : clause p c919 = true :=
  Snake9.LocalRup.prove_clause [c733, c607] c919 (by decide) p (sat_cons (step733 p h) (sat_cons (step607 p h) (sat_nil p)))
def c920 : List Lit := [(1509, false), (1450, false)]
theorem step920 (p : Nat → Bool) (h : Constraints p) : clause p c920 = true :=
  Snake9.LocalRup.prove_clause [c732, c612] c920 (by decide) p (sat_cons (step732 p h) (sat_cons (step612 p h) (sat_nil p)))
def c921 : List Lit := [(1522, true), (1451, false)]
theorem step921 (p : Nat → Bool) (h : Constraints p) : clause p c921 = true :=
  Snake9.LocalRup.prove_clause [c780, c613] c921 (by decide) p (sat_cons (step780 p h) (sat_cons (step613 p h) (sat_nil p)))
def c922 : List Lit := [(1508, false), (1451, false)]
theorem step922 (p : Nat → Bool) (h : Constraints p) : clause p c922 = true :=
  Snake9.LocalRup.prove_clause [c732, c616] c922 (by decide) p (sat_cons (step732 p h) (sat_cons (step616 p h) (sat_nil p)))
def c923 : List Lit := [(1523, true), (1452, false)]
theorem step923 (p : Nat → Bool) (h : Constraints p) : clause p c923 = true :=
  Snake9.LocalRup.prove_clause [c780, c617] c923 (by decide) p (sat_cons (step780 p h) (sat_cons (step617 p h) (sat_nil p)))
def c924 : List Lit := [(1507, false), (1452, false)]
theorem step924 (p : Nat → Bool) (h : Constraints p) : clause p c924 = true :=
  Snake9.LocalRup.prove_clause [c732, c619] c924 (by decide) p (sat_cons (step732 p h) (sat_cons (step619 p h) (sat_nil p)))
def c925 : List Lit := [(1524, true), (1453, false)]
theorem step925 (p : Nat → Bool) (h : Constraints p) : clause p c925 = true :=
  Snake9.LocalRup.prove_clause [c780, c620] c925 (by decide) p (sat_cons (step780 p h) (sat_cons (step620 p h) (sat_nil p)))
def c926 : List Lit := [(1506, false), (1453, false)]
theorem step926 (p : Nat → Bool) (h : Constraints p) : clause p c926 = true :=
  Snake9.LocalRup.prove_clause [c732, c621] c926 (by decide) p (sat_cons (step732 p h) (sat_cons (step621 p h) (sat_nil p)))
def c927 : List Lit := [(1398, false), (1526, false)]
theorem step927 (p : Nat → Bool) (h : Constraints p) : clause p c927 = true :=
  Snake9.LocalRup.prove_clause [c633, c628] c927 (by decide) p (sat_cons (step633 p h) (sat_cons (step628 p h) (sat_nil p)))
def c928 : List Lit := [(1400, false), (1524, false)]
theorem step928 (p : Nat → Bool) (h : Constraints p) : clause p c928 = true :=
  Snake9.LocalRup.prove_clause [c633, c630] c928 (by decide) p (sat_cons (step633 p h) (sat_cons (step630 p h) (sat_nil p)))
def c929 : List Lit := [(1401, false), (1523, false)]
theorem step929 (p : Nat → Bool) (h : Constraints p) : clause p c929 = true :=
  Snake9.LocalRup.prove_clause [c633, c631] c929 (by decide) p (sat_cons (step633 p h) (sat_cons (step631 p h) (sat_nil p)))
def c930 : List Lit := [(1402, false), (1522, false)]
theorem step930 (p : Nat → Bool) (h : Constraints p) : clause p c930 = true :=
  Snake9.LocalRup.prove_clause [c633, c632] c930 (by decide) p (sat_cons (step633 p h) (sat_cons (step632 p h) (sat_nil p)))
def c931 : List Lit := [(1382, true), (1353, false)]
theorem step931 (p : Nat → Bool) (h : Constraints p) : clause p c931 = true :=
  Snake9.LocalRup.prove_clause [c837, c710] c931 (by decide) p (sat_cons (step837 p h) (sat_cons (step710 p h) (sat_nil p)))
def c932 : List Lit := [(44, true), (1382, true), (1375, true)]
theorem step932 (p : Nat → Bool) (h : Constraints p) : clause p c932 = true :=
  Snake9.LocalRup.prove_clause [c837, c721] c932 (by decide) p (sat_cons (step837 p h) (sat_cons (step721 p h) (sat_nil p)))
def c933 : List Lit := [(1453, false), (1526, true), (1353, true), (1302, false)]
theorem step933 (p : Nat → Bool) (h : Constraints p) : clause p c933 = true :=
  Snake9.LocalRup.prove_clause [c838, c752] c933 (by decide) p (sat_cons (step838 p h) (sat_cons (step752 p h) (sat_nil p)))
def c934 : List Lit := [(1384, true), (1371, false), (1353, false)]
theorem step934 (p : Nat → Bool) (h : Constraints p) : clause p c934 = true :=
  Snake9.LocalRup.prove_clause [c409, c428, c433, c414, c672] c934 (by decide) p (sat_cons (step409 p h) (sat_cons (step428 p h) (sat_cons (step433 p h) (sat_cons (step414 p h) (sat_cons (step672 p h) (sat_nil p))))))
def c935 : List Lit := [(48, false), (58, false), (45, false), (1365, false), (1353, false), (52, true), (1452, false)]
theorem step935 (p : Nat → Bool) (h : Constraints p) : clause p c935 = true :=
  Snake9.LocalRup.prove_clause [c923, c929, c77, c68, c398, c314, c403, c316, c661, c356, c934, c439, c444, c928, c357, c618, c346, c917, c821] c935 (by decide) p (sat_cons (step923 p h) (sat_cons (step929 p h) (sat_cons (step77 p h) (sat_cons (step68 p h) (sat_cons (step398 p h) (sat_cons (step314 p h) (sat_cons (step403 p h) (sat_cons (step316 p h) (sat_cons (step661 p h) (sat_cons (step356 p h) (sat_cons (step934 p h) (sat_cons (step439 p h) (sat_cons (step444 p h) (sat_cons (step928 p h) (sat_cons (step357 p h) (sat_cons (step618 p h) (sat_cons (step346 p h) (sat_cons (step917 p h) (sat_cons (step821 p h) (sat_nil p))))))))))))))))))))
def c936 : List Lit := [(1316, true), (1384, false), (1452, false)]
theorem step936 (p : Nat → Bool) (h : Constraints p) : clause p c936 = true :=
  Snake9.LocalRup.prove_clause [c343, c821, c338, c917, c863, c618, c314, c928, c316, c439, c661, c356] c936 (by decide) p (sat_cons (step343 p h) (sat_cons (step821 p h) (sat_cons (step338 p h) (sat_cons (step917 p h) (sat_cons (step863 p h) (sat_cons (step618 p h) (sat_cons (step314 p h) (sat_cons (step928 p h) (sat_cons (step316 p h) (sat_cons (step439 p h) (sat_cons (step661 p h) (sat_cons (step356 p h) (sat_nil p)))))))))))))
def c937 : List Lit := [(1291, true), (48, true), (45, false)]
theorem step937 (p : Nat → Bool) (h : Constraints p) : clause p c937 = true :=
  Snake9.LocalRup.prove_clause [c314, c685, c857] c937 (by decide) p (sat_cons (step314 p h) (sat_cons (step685 p h) (sat_cons (step857 p h) (sat_nil p))))
def c938 : List Lit := [(1329, true), (70, false), (1409, true), (152, true), (45, false), (1365, false), (1353, false), (52, true), (1452, false), (1443, false)]
theorem step938 (p : Nat → Bool) (h : Constraints p) : clause p c938 = true :=
  Snake9.LocalRup.prove_clause [c456, c935, c937, c316, c661, c457, c881, c110, c465, c360, c662, c319, c856, c357, c346, c821, c936, c917, c934, c926, c403, c532, c398, c479, c690, c62, c60, c474, c853, c469, c126] c938 (by decide) p (sat_cons (step456 p h) (sat_cons (step935 p h) (sat_cons (step937 p h) (sat_cons (step316 p h) (sat_cons (step661 p h) (sat_cons (step457 p h) (sat_cons (step881 p h) (sat_cons (step110 p h) (sat_cons (step465 p h) (sat_cons (step360 p h) (sat_cons (step662 p h) (sat_cons (step319 p h) (sat_cons (step856 p h) (sat_cons (step357 p h) (sat_cons (step346 p h) (sat_cons (step821 p h) (sat_cons (step936 p h) (sat_cons (step917 p h) (sat_cons (step934 p h) (sat_cons (step926 p h) (sat_cons (step403 p h) (sat_cons (step532 p h) (sat_cons (step398 p h) (sat_cons (step479 p h) (sat_cons (step690 p h) (sat_cons (step62 p h) (sat_cons (step60 p h) (sat_cons (step474 p h) (sat_cons (step853 p h) (sat_cons (step469 p h) (sat_cons (step126 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c939 : List Lit := [(1329, false), (73, false), (1409, true), (152, true), (45, false), (1365, false), (1353, false), (52, true), (1438, false), (1431, false), (1423, false)]
theorem step939 (p : Nat → Bool) (h : Constraints p) : clause p c939 = true :=
  Snake9.LocalRup.prove_clause [c513, c527, c456, c935, c937, c457, c881, c110, c465, c923, c929, c903, c808, c447, c444, c443, c934, c928, c403, c925, c618, c398, c528, c532, c917, c514, c517, c479, c821, c841, c506, c474, c346, c499, c361, c828, c662, c469, c319, c679, c856, c690, c62, c853] c939 (by decide) p (sat_cons (step513 p h) (sat_cons (step527 p h) (sat_cons (step456 p h) (sat_cons (step935 p h) (sat_cons (step937 p h) (sat_cons (step457 p h) (sat_cons (step881 p h) (sat_cons (step110 p h) (sat_cons (step465 p h) (sat_cons (step923 p h) (sat_cons (step929 p h) (sat_cons (step903 p h) (sat_cons (step808 p h) (sat_cons (step447 p h) (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step934 p h) (sat_cons (step928 p h) (sat_cons (step403 p h) (sat_cons (step925 p h) (sat_cons (step618 p h) (sat_cons (step398 p h) (sat_cons (step528 p h) (sat_cons (step532 p h) (sat_cons (step917 p h) (sat_cons (step514 p h) (sat_cons (step517 p h) (sat_cons (step479 p h) (sat_cons (step821 p h) (sat_cons (step841 p h) (sat_cons (step506 p h) (sat_cons (step474 p h) (sat_cons (step346 p h) (sat_cons (step499 p h) (sat_cons (step361 p h) (sat_cons (step828 p h) (sat_cons (step662 p h) (sat_cons (step469 p h) (sat_cons (step319 p h) (sat_cons (step679 p h) (sat_cons (step856 p h) (sat_cons (step690 p h) (sat_cons (step62 p h) (sat_cons (step853 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c940 : List Lit := [(1329, true), (1409, true), (152, true), (45, false), (1365, false), (1353, false), (52, true), (1443, false), (1438, false), (1423, false)]
theorem step940 (p : Nat → Bool) (h : Constraints p) : clause p c940 = true :=
  Snake9.LocalRup.prove_clause [c527, c456, c935, c937, c316, c661, c924, c357, c938, c346, c492, c821, c917, c603, c926, c813, c528, c497, c517] c940 (by decide) p (sat_cons (step527 p h) (sat_cons (step456 p h) (sat_cons (step935 p h) (sat_cons (step937 p h) (sat_cons (step316 p h) (sat_cons (step661 p h) (sat_cons (step924 p h) (sat_cons (step357 p h) (sat_cons (step938 p h) (sat_cons (step346 p h) (sat_cons (step492 p h) (sat_cons (step821 p h) (sat_cons (step917 p h) (sat_cons (step603 p h) (sat_cons (step926 p h) (sat_cons (step813 p h) (sat_cons (step528 p h) (sat_cons (step497 p h) (sat_cons (step517 p h) (sat_nil p))))))))))))))))))))
def c941 : List Lit := [(1409, true), (152, true), (45, false), (1365, false), (1353, false), (52, true), (1438, false), (1431, false), (1423, false)]
theorem step941 (p : Nat → Bool) (h : Constraints p) : clause p c941 = true :=
  Snake9.LocalRup.prove_clause [c903, c808, c513, c527, c940, c443, c939, c928, c500, c925, c618, c528, c917, c514, c841, c506] c941 (by decide) p (sat_cons (step903 p h) (sat_cons (step808 p h) (sat_cons (step513 p h) (sat_cons (step527 p h) (sat_cons (step940 p h) (sat_cons (step443 p h) (sat_cons (step939 p h) (sat_cons (step928 p h) (sat_cons (step500 p h) (sat_cons (step925 p h) (sat_cons (step618 p h) (sat_cons (step528 p h) (sat_cons (step917 p h) (sat_cons (step514 p h) (sat_cons (step841 p h) (sat_cons (step506 p h) (sat_nil p)))))))))))))))))
def c942 : List Lit := [(1453, false), (47, true), (1353, false)]
theorem step942 (p : Nat → Bool) (h : Constraints p) : clause p c942 = true :=
  Snake9.LocalRup.prove_clause [c926, c925, c917, c928, c821, c843, c346] c942 (by decide) p (sat_cons (step926 p h) (sat_cons (step925 p h) (sat_cons (step917 p h) (sat_cons (step928 p h) (sat_cons (step821 p h) (sat_cons (step843 p h) (sat_cons (step346 p h) (sat_nil p))))))))
def c943 : List Lit := [(1478, true), (176, true), (45, false), (1417, true), (1432, true), (1439, true), (47, true), (1353, false), (1452, false)]
theorem step943 (p : Nat → Bool) (h : Constraints p) : clause p c943 = true :=
  Snake9.LocalRup.prove_clause [c821, c841, c346, c506, c843, c499, c500, c928, c828, c618, c469, c915, c679, c883, c813, c134] c943 (by decide) p (sat_cons (step821 p h) (sat_cons (step841 p h) (sat_cons (step346 p h) (sat_cons (step506 p h) (sat_cons (step843 p h) (sat_cons (step499 p h) (sat_cons (step500 p h) (sat_cons (step928 p h) (sat_cons (step828 p h) (sat_cons (step618 p h) (sat_cons (step469 p h) (sat_cons (step915 p h) (sat_cons (step679 p h) (sat_cons (step883 p h) (sat_cons (step813 p h) (sat_cons (step134 p h) (sat_nil p)))))))))))))))))
def c944 : List Lit := [(45, false), (1409, true), (47, true), (1353, false), (52, true), (1438, false), (1431, false), (1423, false)]
theorem step944 (p : Nat → Bool) (h : Constraints p) : clause p c944 = true :=
  Snake9.TreeRup.prove_clause [c513, c942, c532, c479, c456, c457, c881, c110, c465, c474, c528, c517, c514, c393, c903, c808, c527, c924, c512, c526, c922, c941, c47, c256, c257, c262, c268, c270, c272, c899, c902, c254, c307, c252, c293, c245, c284, c243, c283, c242, c282, c11, c281, c943, c917, c603, c618, c813, c928, c134, c843, c443, c845, c678, c506, c859, c499, c500, c55, c828, c883, c469] c944 (by decide) p (sat_cons (step513 p h) (sat_cons (step942 p h) (sat_cons (step532 p h) (sat_cons (step479 p h) (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step881 p h) (sat_cons (step110 p h) (sat_cons (step465 p h) (sat_cons (step474 p h) (sat_cons (step528 p h) (sat_cons (step517 p h) (sat_cons (step514 p h) (sat_cons (step393 p h) (sat_cons (step903 p h) (sat_cons (step808 p h) (sat_cons (step527 p h) (sat_cons (step924 p h) (sat_cons (step512 p h) (sat_cons (step526 p h) (sat_cons (step922 p h) (sat_cons (step941 p h) (sat_cons (step47 p h) (sat_cons (step256 p h) (sat_cons (step257 p h) (sat_cons (step262 p h) (sat_cons (step268 p h) (sat_cons (step270 p h) (sat_cons (step272 p h) (sat_cons (step899 p h) (sat_cons (step902 p h) (sat_cons (step254 p h) (sat_cons (step307 p h) (sat_cons (step252 p h) (sat_cons (step293 p h) (sat_cons (step245 p h) (sat_cons (step284 p h) (sat_cons (step243 p h) (sat_cons (step283 p h) (sat_cons (step242 p h) (sat_cons (step282 p h) (sat_cons (step11 p h) (sat_cons (step281 p h) (sat_cons (step943 p h) (sat_cons (step917 p h) (sat_cons (step603 p h) (sat_cons (step618 p h) (sat_cons (step813 p h) (sat_cons (step928 p h) (sat_cons (step134 p h) (sat_cons (step843 p h) (sat_cons (step443 p h) (sat_cons (step845 p h) (sat_cons (step678 p h) (sat_cons (step506 p h) (sat_cons (step859 p h) (sat_cons (step499 p h) (sat_cons (step500 p h) (sat_cons (step55 p h) (sat_cons (step828 p h) (sat_cons (step883 p h) (sat_cons (step469 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c945 : List Lit := [(1366, false), (1353, false), (52, true), (1452, false)]
theorem step945 (p : Nat → Bool) (h : Constraints p) : clause p c945 = true :=
  Snake9.LocalRup.prove_clause [c923, c929, c904, c409, c934, c444, c936, c700, c346, c334, c336, c665, c357, c331, c864, c440, c661, c24, c429, c436, c318, c370, c711, c415, c419, c414, c406, c390, c434, c398, c382, c690, c377, c386, c388, c373, c392, c872, c44] c945 (by decide) p (sat_cons (step923 p h) (sat_cons (step929 p h) (sat_cons (step904 p h) (sat_cons (step409 p h) (sat_cons (step934 p h) (sat_cons (step444 p h) (sat_cons (step936 p h) (sat_cons (step700 p h) (sat_cons (step346 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step665 p h) (sat_cons (step357 p h) (sat_cons (step331 p h) (sat_cons (step864 p h) (sat_cons (step440 p h) (sat_cons (step661 p h) (sat_cons (step24 p h) (sat_cons (step429 p h) (sat_cons (step436 p h) (sat_cons (step318 p h) (sat_cons (step370 p h) (sat_cons (step711 p h) (sat_cons (step415 p h) (sat_cons (step419 p h) (sat_cons (step414 p h) (sat_cons (step406 p h) (sat_cons (step390 p h) (sat_cons (step434 p h) (sat_cons (step398 p h) (sat_cons (step382 p h) (sat_cons (step690 p h) (sat_cons (step377 p h) (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step373 p h) (sat_cons (step392 p h) (sat_cons (step872 p h) (sat_cons (step44 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c946 : List Lit := [(47, true), (1353, false), (52, true), (1431, false), (1419, false)]
theorem step946 (p : Nat → Bool) (h : Constraints p) : clause p c946 = true :=
  Snake9.LocalRup.prove_clause [c478, c512, c855, c513, c527, c945, c942, c395, c532, c944, c482, c459] c946 (by decide) p (sat_cons (step478 p h) (sat_cons (step512 p h) (sat_cons (step855 p h) (sat_cons (step513 p h) (sat_cons (step527 p h) (sat_cons (step945 p h) (sat_cons (step942 p h) (sat_cons (step395 p h) (sat_cons (step532 p h) (sat_cons (step944 p h) (sat_cons (step482 p h) (sat_cons (step459 p h) (sat_nil p)))))))))))))
def c947 : List Lit := [(1291, true), (45, false), (47, false)]
theorem step947 (p : Nat → Bool) (h : Constraints p) : clause p c947 = true :=
  Snake9.LocalRup.prove_clause [c314, c937, c66] c947 (by decide) p (sat_cons (step314 p h) (sat_cons (step937 p h) (sat_cons (step66 p h) (sat_nil p))))
def c948 : List Lit := [(1453, false), (1302, false), (1353, false), (52, true)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true :=
  Snake9.LocalRup.prove_clause [c926, c925, c917, c928, c821, c839, c346, c443, c357] c948 (by decide) p (sat_cons (step926 p h) (sat_cons (step925 p h) (sat_cons (step917 p h) (sat_cons (step928 p h) (sat_cons (step821 p h) (sat_cons (step839 p h) (sat_cons (step346 p h) (sat_cons (step443 p h) (sat_cons (step357 p h) (sat_nil p))))))))))
def c949 : List Lit := [(45, false), (47, false), (1353, false), (52, true), (1443, false), (1419, false)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true :=
  Snake9.LocalRup.prove_clause [c947, c316, c661, c948, c532, c482, c459, c456, c736, c75] c949 (by decide) p (sat_cons (step947 p h) (sat_cons (step316 p h) (sat_cons (step661 p h) (sat_cons (step948 p h) (sat_cons (step532 p h) (sat_cons (step482 p h) (sat_cons (step459 p h) (sat_cons (step456 p h) (sat_cons (step736 p h) (sat_cons (step75 p h) (sat_nil p)))))))))))
def c950 : List Lit := [(1409, true), (47, false)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true :=
  Snake9.LocalRup.prove_clause [c456, c457, c881, c107] c950 (by decide) p (sat_cons (step456 p h) (sat_cons (step457 p h) (sat_cons (step881 p h) (sat_cons (step107 p h) (sat_nil p)))))
def c951 : List Lit := [(47, false), (1353, false), (1419, false), (52, true), (1443, false)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true :=
  Snake9.LocalRup.prove_clause [c949, c394, c903, c808, c950, c459, c482, c532, c926, c925, c948, c917, c928, c661, c821, c443, c318, c346, c700, c665, c699, c334, c336, c439, c413, c331, c864, c428, c934, c433, c24, c418, c403, c384, c370, c390, c398, c371, c382, c690, c368, c377, c388, c871, c373, c37] c951 (by decide) p (sat_cons (step949 p h) (sat_cons (step394 p h) (sat_cons (step903 p h) (sat_cons (step808 p h) (sat_cons (step950 p h) (sat_cons (step459 p h) (sat_cons (step482 p h) (sat_cons (step532 p h) (sat_cons (step926 p h) (sat_cons (step925 p h) (sat_cons (step948 p h) (sat_cons (step917 p h) (sat_cons (step928 p h) (sat_cons (step661 p h) (sat_cons (step821 p h) (sat_cons (step443 p h) (sat_cons (step318 p h) (sat_cons (step346 p h) (sat_cons (step700 p h) (sat_cons (step665 p h) (sat_cons (step699 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step439 p h) (sat_cons (step413 p h) (sat_cons (step331 p h) (sat_cons (step864 p h) (sat_cons (step428 p h) (sat_cons (step934 p h) (sat_cons (step433 p h) (sat_cons (step24 p h) (sat_cons (step418 p h) (sat_cons (step403 p h) (sat_cons (step384 p h) (sat_cons (step370 p h) (sat_cons (step390 p h) (sat_cons (step398 p h) (sat_cons (step371 p h) (sat_cons (step382 p h) (sat_cons (step690 p h) (sat_cons (step368 p h) (sat_cons (step377 p h) (sat_cons (step388 p h) (sat_cons (step871 p h) (sat_cons (step373 p h) (sat_cons (step37 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c952 : List Lit := [(1353, false), (52, true), (1431, false), (1419, false)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true :=
  Snake9.LocalRup.prove_clause [c512, c855, c513, c946, c951] c952 (by decide) p (sat_cons (step512 p h) (sat_cons (step855 p h) (sat_cons (step513 p h) (sat_cons (step946 p h) (sat_cons (step951 p h) (sat_nil p))))))
def c953 : List Lit := [(1353, true), (1452, false), (1419, false)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true :=
  Snake9.LocalRup.prove_clause [c924, c916, c478, c381, c749, c801, c746, c370, c915, c603, c869, c870, c634, c618, c821, c841, c331, c928, c346, c506, c334, c500, c700, c850, c443] c953 (by decide) p (sat_cons (step924 p h) (sat_cons (step916 p h) (sat_cons (step478 p h) (sat_cons (step381 p h) (sat_cons (step749 p h) (sat_cons (step801 p h) (sat_cons (step746 p h) (sat_cons (step370 p h) (sat_cons (step915 p h) (sat_cons (step603 p h) (sat_cons (step869 p h) (sat_cons (step870 p h) (sat_cons (step634 p h) (sat_cons (step618 p h) (sat_cons (step821 p h) (sat_cons (step841 p h) (sat_cons (step331 p h) (sat_cons (step928 p h) (sat_cons (step346 p h) (sat_cons (step506 p h) (sat_cons (step334 p h) (sat_cons (step500 p h) (sat_cons (step700 p h) (sat_cons (step850 p h) (sat_cons (step443 p h) (sat_nil p))))))))))))))))))))))))))
def c954 : List Lit := [(1431, false), (1419, false)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true :=
  Snake9.LocalRup.prove_clause [c478, c512, c855, c513, c527, c953, c952, c772, c786, c482, c912, c532, c514, c926, c925, c917, c915, c928, c821, c841, c813, c346, c506, c357, c500, c443, c850] c954 (by decide) p (sat_cons (step478 p h) (sat_cons (step512 p h) (sat_cons (step855 p h) (sat_cons (step513 p h) (sat_cons (step527 p h) (sat_cons (step953 p h) (sat_cons (step952 p h) (sat_cons (step772 p h) (sat_cons (step786 p h) (sat_cons (step482 p h) (sat_cons (step912 p h) (sat_cons (step532 p h) (sat_cons (step514 p h) (sat_cons (step926 p h) (sat_cons (step925 p h) (sat_cons (step917 p h) (sat_cons (step915 p h) (sat_cons (step928 p h) (sat_cons (step821 p h) (sat_cons (step841 p h) (sat_cons (step813 p h) (sat_cons (step346 p h) (sat_cons (step506 p h) (sat_cons (step357 p h) (sat_cons (step500 p h) (sat_cons (step443 p h) (sat_cons (step850 p h) (sat_nil p))))))))))))))))))))))))))))
def c955 : List Lit := [(52, false), (1419, false)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true :=
  Snake9.LocalRup.prove_clause [c954, c496, c813, c915, c926, c771, c772, c844, c482, c768, c532] c955 (by decide) p (sat_cons (step954 p h) (sat_cons (step496 p h) (sat_cons (step813 p h) (sat_cons (step915 p h) (sat_cons (step926 p h) (sat_cons (step771 p h) (sat_cons (step772 p h) (sat_cons (step844 p h) (sat_cons (step482 p h) (sat_cons (step768 p h) (sat_cons (step532 p h) (sat_nil p))))))))))))
def c956 : List Lit := [(1400, true), (1316, false), (1353, false), (52, true)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true :=
  Snake9.LocalRup.prove_clause [c346, c665, c839, c439, c443, c428, c934, c700, c357, c334, c336, c661, c331, c864, c316, c318, c24, c704, c370, c903, c699, c403, c418, c413, c398, c390, c433, c690, c382, c386, c388, c377, c392, c373, c876, c44] c956 (by decide) p (sat_cons (step346 p h) (sat_cons (step665 p h) (sat_cons (step839 p h) (sat_cons (step439 p h) (sat_cons (step443 p h) (sat_cons (step428 p h) (sat_cons (step934 p h) (sat_cons (step700 p h) (sat_cons (step357 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step661 p h) (sat_cons (step331 p h) (sat_cons (step864 p h) (sat_cons (step316 p h) (sat_cons (step318 p h) (sat_cons (step24 p h) (sat_cons (step704 p h) (sat_cons (step370 p h) (sat_cons (step903 p h) (sat_cons (step699 p h) (sat_cons (step403 p h) (sat_cons (step418 p h) (sat_cons (step413 p h) (sat_cons (step398 p h) (sat_cons (step390 p h) (sat_cons (step433 p h) (sat_cons (step690 p h) (sat_cons (step382 p h) (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step377 p h) (sat_cons (step392 p h) (sat_cons (step373 p h) (sat_cons (step876 p h) (sat_cons (step44 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c957 : List Lit := [(1424, false), (1524, true), (1497, false)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true :=
  Snake9.LocalRup.prove_clause [c915, c618, c530, c531, c615, c509, c603, c504, c841] c957 (by decide) p (sat_cons (step915 p h) (sat_cons (step618 p h) (sat_cons (step530 p h) (sat_cons (step531 p h) (sat_cons (step615 p h) (sat_cons (step509 p h) (sat_cons (step603 p h) (sat_cons (step504 p h) (sat_cons (step841 p h) (sat_nil p))))))))))
def c958 : List Lit := [(1478, true), (86, true)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true :=
  Snake9.LocalRup.prove_clause [c540, c543, c913, c566, c840] c958 (by decide) p (sat_cons (step540 p h) (sat_cons (step543 p h) (sat_cons (step913 p h) (sat_cons (step566 p h) (sat_cons (step840 p h) (sat_nil p))))))
def c959 : List Lit := [(1329, true), (1316, false), (1353, false), (1419, false)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true :=
  Snake9.TreeRup.prove_clause [c954, c496, c813, c955, c956, c928, c957, c482, c459, c950, c456, c346, c665, c478, c525, c666, c700, c357, c347, c334, c336, c661, c345, c331, c864, c316, c318, c24, c314, c370, c863, c338, c339, c344, c340, c868, c29, c73, c937, c395, c904, c409, c958, c603, c610, c929, c440, c429, c436, c419, c711, c390, c414, c415, c434, c406, c384, c382, c398, c371, c377, c690, c368, c373, c388, c871, c37] c959 (by decide) p (sat_cons (step954 p h) (sat_cons (step496 p h) (sat_cons (step813 p h) (sat_cons (step955 p h) (sat_cons (step956 p h) (sat_cons (step928 p h) (sat_cons (step957 p h) (sat_cons (step482 p h) (sat_cons (step459 p h) (sat_cons (step950 p h) (sat_cons (step456 p h) (sat_cons (step346 p h) (sat_cons (step665 p h) (sat_cons (step478 p h) (sat_cons (step525 p h) (sat_cons (step666 p h) (sat_cons (step700 p h) (sat_cons (step357 p h) (sat_cons (step347 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step661 p h) (sat_cons (step345 p h) (sat_cons (step331 p h) (sat_cons (step864 p h) (sat_cons (step316 p h) (sat_cons (step318 p h) (sat_cons (step24 p h) (sat_cons (step314 p h) (sat_cons (step370 p h) (sat_cons (step863 p h) (sat_cons (step338 p h) (sat_cons (step339 p h) (sat_cons (step344 p h) (sat_cons (step340 p h) (sat_cons (step868 p h) (sat_cons (step29 p h) (sat_cons (step73 p h) (sat_cons (step937 p h) (sat_cons (step395 p h) (sat_cons (step904 p h) (sat_cons (step409 p h) (sat_cons (step958 p h) (sat_cons (step603 p h) (sat_cons (step610 p h) (sat_cons (step929 p h) (sat_cons (step440 p h) (sat_cons (step429 p h) (sat_cons (step436 p h) (sat_cons (step419 p h) (sat_cons (step711 p h) (sat_cons (step390 p h) (sat_cons (step414 p h) (sat_cons (step415 p h) (sat_cons (step434 p h) (sat_cons (step406 p h) (sat_cons (step384 p h) (sat_cons (step382 p h) (sat_cons (step398 p h) (sat_cons (step371 p h) (sat_cons (step377 p h) (sat_cons (step690 p h) (sat_cons (step368 p h) (sat_cons (step373 p h) (sat_cons (step388 p h) (sat_cons (step871 p h) (sat_cons (step37 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c960 : List Lit := [(1401, true), (1316, false), (1353, false), (1419, false)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true :=
  Snake9.LocalRup.prove_clause [c954, c496, c813, c955, c956, c928, c957, c482, c459, c950, c393, c903, c808, c959, c456, c346, c447, c444, c361, c428, c934, c662, c418, c904, c403, c390, c395, c398, c79, c937, c316, c319, c661, c690, c358, c386, c388, c349, c389, c392, c334, c336, c413, c876, c44, c331, c864, c433, c373, c24, c377, c370, c382] c960 (by decide) p (sat_cons (step954 p h) (sat_cons (step496 p h) (sat_cons (step813 p h) (sat_cons (step955 p h) (sat_cons (step956 p h) (sat_cons (step928 p h) (sat_cons (step957 p h) (sat_cons (step482 p h) (sat_cons (step459 p h) (sat_cons (step950 p h) (sat_cons (step393 p h) (sat_cons (step903 p h) (sat_cons (step808 p h) (sat_cons (step959 p h) (sat_cons (step456 p h) (sat_cons (step346 p h) (sat_cons (step447 p h) (sat_cons (step444 p h) (sat_cons (step361 p h) (sat_cons (step428 p h) (sat_cons (step934 p h) (sat_cons (step662 p h) (sat_cons (step418 p h) (sat_cons (step904 p h) (sat_cons (step403 p h) (sat_cons (step390 p h) (sat_cons (step395 p h) (sat_cons (step398 p h) (sat_cons (step79 p h) (sat_cons (step937 p h) (sat_cons (step316 p h) (sat_cons (step319 p h) (sat_cons (step661 p h) (sat_cons (step690 p h) (sat_cons (step358 p h) (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step349 p h) (sat_cons (step389 p h) (sat_cons (step392 p h) (sat_cons (step334 p h) (sat_cons (step336 p h) (sat_cons (step413 p h) (sat_cons (step876 p h) (sat_cons (step44 p h) (sat_cons (step331 p h) (sat_cons (step864 p h) (sat_cons (step433 p h) (sat_cons (step373 p h) (sat_cons (step24 p h) (sat_cons (step377 p h) (sat_cons (step370 p h) (sat_cons (step382 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c961 : List Lit := [(1523, true), (1419, false)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true :=
  Snake9.LocalRup.prove_clause [c954, c496, c813, c915, c478, c525, c610, c614, c603, c526, c841, c509, c504] c961 (by decide) p (sat_cons (step954 p h) (sat_cons (step496 p h) (sat_cons (step813 p h) (sat_cons (step915 p h) (sat_cons (step478 p h) (sat_cons (step525 p h) (sat_cons (step610 p h) (sat_cons (step614 p h) (sat_cons (step603 p h) (sat_cons (step526 p h) (sat_cons (step841 p h) (sat_cons (step509 p h) (sat_cons (step504 p h) (sat_nil p))))))))))))))
end B112E166
