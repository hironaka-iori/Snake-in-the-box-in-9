import B112E145Part0002
namespace B112E145
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c891 : List Lit := [(7, true), (217, true), (1236, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.LocalRup.prove_clause [c178, c177, c232, c228, c227, c231, c230, c229, c16, c20, c14, c463, c9, c468] c891 (by decide) p (sat_cons (step178 p h) (sat_cons (step177 p h) (sat_cons (step232 p h) (sat_cons (step228 p h) (sat_cons (step227 p h) (sat_cons (step231 p h) (sat_cons (step230 p h) (sat_cons (step229 p h) (sat_cons (step16 p h) (sat_cons (step20 p h) (sat_cons (step14 p h) (sat_cons (step463 p h) (sat_cons (step9 p h) (sat_cons (step468 p h) (sat_nil p)))))))))))))))
def c892 : List Lit := [(1363, false), (1313, false)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true :=
  Snake9.LocalRup.prove_clause [c744, c888, c782, c695, c879, c184, c827, c714, c825, c650, c654, c683, c846, c691, c853, c597, c496, c70, c522, c499, c505, c509, c504, c507, c795, c492, c526, c491, c493, c272, c478, c489, c255, c475, c806, c470, c36] c892 (by decide) p (sat_cons (step744 p h) (sat_cons (step888 p h) (sat_cons (step782 p h) (sat_cons (step695 p h) (sat_cons (step879 p h) (sat_cons (step184 p h) (sat_cons (step827 p h) (sat_cons (step714 p h) (sat_cons (step825 p h) (sat_cons (step650 p h) (sat_cons (step654 p h) (sat_cons (step683 p h) (sat_cons (step846 p h) (sat_cons (step691 p h) (sat_cons (step853 p h) (sat_cons (step597 p h) (sat_cons (step496 p h) (sat_cons (step70 p h) (sat_cons (step522 p h) (sat_cons (step499 p h) (sat_cons (step505 p h) (sat_cons (step509 p h) (sat_cons (step504 p h) (sat_cons (step507 p h) (sat_cons (step795 p h) (sat_cons (step492 p h) (sat_cons (step526 p h) (sat_cons (step491 p h) (sat_cons (step493 p h) (sat_cons (step272 p h) (sat_cons (step478 p h) (sat_cons (step489 p h) (sat_cons (step255 p h) (sat_cons (step475 p h) (sat_cons (step806 p h) (sat_cons (step470 p h) (sat_cons (step36 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c893 : List Lit := [(24, false), (1432, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true :=
  Snake9.LocalRup.prove_clause [c879, c830, c779, c781, c844, c853, c665, c846, c666, c653, c675, c684, c677] c893 (by decide) p (sat_cons (step879 p h) (sat_cons (step830 p h) (sat_cons (step779 p h) (sat_cons (step781 p h) (sat_cons (step844 p h) (sat_cons (step853 p h) (sat_cons (step665 p h) (sat_cons (step846 p h) (sat_cons (step666 p h) (sat_cons (step653 p h) (sat_cons (step675 p h) (sat_cons (step684 p h) (sat_cons (step677 p h) (sat_nil p))))))))))))))
def c894 : List Lit := [(24, true), (1259, true), (1344, false)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true :=
  Snake9.LocalRup.prove_clause [c888, c782, c695, c830, c879, c184, c707, c714, c825, c748, c801, c856, c509, c492, c505, c653, c845, c486, c683, c691, c654, c838, c496, c70, c747, c499, c795, c277, c504, c507, c272, c243, c245, c491, c493, c255, c241, c891, c489, c806, c236, c36, c24, c470, c13, c475, c478, c526, c597, c588, c586, c553, c880, c551, c545] c894 (by decide) p (sat_cons (step888 p h) (sat_cons (step782 p h) (sat_cons (step695 p h) (sat_cons (step830 p h) (sat_cons (step879 p h) (sat_cons (step184 p h) (sat_cons (step707 p h) (sat_cons (step714 p h) (sat_cons (step825 p h) (sat_cons (step748 p h) (sat_cons (step801 p h) (sat_cons (step856 p h) (sat_cons (step509 p h) (sat_cons (step492 p h) (sat_cons (step505 p h) (sat_cons (step653 p h) (sat_cons (step845 p h) (sat_cons (step486 p h) (sat_cons (step683 p h) (sat_cons (step691 p h) (sat_cons (step654 p h) (sat_cons (step838 p h) (sat_cons (step496 p h) (sat_cons (step70 p h) (sat_cons (step747 p h) (sat_cons (step499 p h) (sat_cons (step795 p h) (sat_cons (step277 p h) (sat_cons (step504 p h) (sat_cons (step507 p h) (sat_cons (step272 p h) (sat_cons (step243 p h) (sat_cons (step245 p h) (sat_cons (step491 p h) (sat_cons (step493 p h) (sat_cons (step255 p h) (sat_cons (step241 p h) (sat_cons (step891 p h) (sat_cons (step489 p h) (sat_cons (step806 p h) (sat_cons (step236 p h) (sat_cons (step36 p h) (sat_cons (step24 p h) (sat_cons (step470 p h) (sat_cons (step13 p h) (sat_cons (step475 p h) (sat_cons (step478 p h) (sat_cons (step526 p h) (sat_cons (step597 p h) (sat_cons (step588 p h) (sat_cons (step586 p h) (sat_cons (step553 p h) (sat_cons (step880 p h) (sat_cons (step551 p h) (sat_cons (step545 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c895 : List Lit := [(1313, true)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true :=
  Snake9.LocalRup.prove_clause [c748, c801, c856, c588, c586, c553, c890, c551, c545] c895 (by decide) p (sat_cons (step748 p h) (sat_cons (step801 p h) (sat_cons (step856 p h) (sat_cons (step588 p h) (sat_cons (step586 p h) (sat_cons (step553 p h) (sat_cons (step890 p h) (sat_cons (step551 p h) (sat_cons (step545 p h) (sat_nil p))))))))))
def c896 : List Lit := [(1326, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true :=
  Snake9.LocalRup.prove_clause [c895, c876, c594] c896 (by decide) p (sat_cons (step895 p h) (sat_cons (step876 p h) (sat_cons (step594 p h) (sat_nil p))))
def c897 : List Lit := [(1432, false)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true :=
  Snake9.LocalRup.prove_clause [c896, c695, c690] c897 (by decide) p (sat_cons (step896 p h) (sat_cons (step695 p h) (sat_cons (step690 p h) (sat_nil p))))
def c898 : List Lit := [(24, false)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true :=
  Snake9.LocalRup.prove_clause [c897, c893] c898 (by decide) p (sat_cons (step897 p h) (sat_cons (step893 p h) (sat_nil p)))
def c899 : List Lit := [(1344, false)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true :=
  Snake9.LocalRup.prove_clause [c830, c782, c695, c895, c827, c898, c653, c683, c691, c597, c522, c894] c899 (by decide) p (sat_cons (step830 p h) (sat_cons (step782 p h) (sat_cons (step695 p h) (sat_cons (step895 p h) (sat_cons (step827 p h) (sat_cons (step898 p h) (sat_cons (step653 p h) (sat_cons (step683 p h) (sat_cons (step691 p h) (sat_cons (step597 p h) (sat_cons (step522 p h) (sat_cons (step894 p h) (sat_nil p)))))))))))))
def c900 : List Lit := [(1267, false)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true :=
  Snake9.LocalRup.prove_clause [c895, c833, c600] c900 (by decide) p (sat_cons (step895 p h) (sat_cons (step833 p h) (sat_cons (step600 p h) (sat_nil p))))
def c901 : List Lit := [(1363, false)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true :=
  Snake9.LocalRup.prove_clause [c895, c892] c901 (by decide) p (sat_cons (step895 p h) (sat_cons (step892 p h) (sat_nil p)))
def c902 : List Lit := [(1253, true)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true :=
  Snake9.LocalRup.prove_clause [c898, c496] c902 (by decide) p (sat_cons (step898 p h) (sat_cons (step496 p h) (sat_nil p)))
def c903 : List Lit := [(20, false)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true :=
  Snake9.LocalRup.prove_clause [c898, c184, c825, c70] c903 (by decide) p (sat_cons (step898 p h) (sat_cons (step184 p h) (sat_cons (step825 p h) (sat_cons (step70 p h) (sat_nil p)))))
def c904 : List Lit := [(53, true)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true :=
  Snake9.LocalRup.prove_clause [c899, c846] c904 (by decide) p (sat_cons (step899 p h) (sat_cons (step846 p h) (sat_nil p)))
def c905 : List Lit := [(1260, false)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true :=
  Snake9.LocalRup.prove_clause [c900, c827, c523] c905 (by decide) p (sat_cons (step900 p h) (sat_cons (step827 p h) (sat_cons (step523 p h) (sat_nil p))))
def c906 : List Lit := [(69, true)]
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true :=
  Snake9.LocalRup.prove_clause [c901, c838] c906 (by decide) p (sat_cons (step901 p h) (sat_cons (step838 p h) (sat_nil p)))
def c907 : List Lit := [(1255, true)]
theorem step907 (p : Nat → Bool) (h : Constraints p) : clause p c907 = true :=
  Snake9.LocalRup.prove_clause [c902, c499] c907 (by decide) p (sat_cons (step902 p h) (sat_cons (step499 p h) (sat_nil p)))
def c908 : List Lit := [(1258, true)]
theorem step908 (p : Nat → Bool) (h : Constraints p) : clause p c908 = true :=
  Snake9.LocalRup.prove_clause [c907, c504] c908 (by decide) p (sat_cons (step907 p h) (sat_cons (step504 p h) (sat_nil p)))
def c909 : List Lit := [(1251, false)]
theorem step909 (p : Nat → Bool) (h : Constraints p) : clause p c909 = true :=
  Snake9.LocalRup.prove_clause [c907, c905, c510] c909 (by decide) p (sat_cons (step907 p h) (sat_cons (step905 p h) (sat_cons (step510 p h) (sat_nil p))))
def c910 : List Lit := [(1249, false)]
theorem step910 (p : Nat → Bool) (h : Constraints p) : clause p c910 = true :=
  Snake9.LocalRup.prove_clause [c909, c492] c910 (by decide) p (sat_cons (step909 p h) (sat_cons (step492 p h) (sat_nil p)))
def c911 : List Lit := [(1259, true)]
theorem step911 (p : Nat → Bool) (h : Constraints p) : clause p c911 = true :=
  Snake9.LocalRup.prove_clause [c898, c907, c903, c714, c424, c910, c825, c908, c895, c695, c904, c879, c831, c781, c779, c505, c747, c507, c795, c274, c491, c493, c272, c327, c489, c255, c422, c806, c419, c36, c373, c470, c348, c475, c346, c478, c344, c526, c343, c597, c140, c691, c139, c681, c665, c677, c666, c675] c911 (by decide) p (sat_cons (step898 p h) (sat_cons (step907 p h) (sat_cons (step903 p h) (sat_cons (step714 p h) (sat_cons (step424 p h) (sat_cons (step910 p h) (sat_cons (step825 p h) (sat_cons (step908 p h) (sat_cons (step895 p h) (sat_cons (step695 p h) (sat_cons (step904 p h) (sat_cons (step879 p h) (sat_cons (step831 p h) (sat_cons (step781 p h) (sat_cons (step779 p h) (sat_cons (step505 p h) (sat_cons (step747 p h) (sat_cons (step507 p h) (sat_cons (step795 p h) (sat_cons (step274 p h) (sat_cons (step491 p h) (sat_cons (step493 p h) (sat_cons (step272 p h) (sat_cons (step327 p h) (sat_cons (step489 p h) (sat_cons (step255 p h) (sat_cons (step422 p h) (sat_cons (step806 p h) (sat_cons (step419 p h) (sat_cons (step36 p h) (sat_cons (step373 p h) (sat_cons (step470 p h) (sat_cons (step348 p h) (sat_cons (step475 p h) (sat_cons (step346 p h) (sat_cons (step478 p h) (sat_cons (step344 p h) (sat_cons (step526 p h) (sat_cons (step343 p h) (sat_cons (step597 p h) (sat_cons (step140 p h) (sat_cons (step691 p h) (sat_cons (step139 p h) (sat_cons (step681 p h) (sat_cons (step665 p h) (sat_cons (step677 p h) (sat_cons (step666 p h) (sat_cons (step675 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c912 : List Lit := [(1266, true)]
theorem step912 (p : Nat → Bool) (h : Constraints p) : clause p c912 = true :=
  Snake9.LocalRup.prove_clause [c911, c827, c522] c912 (by decide) p (sat_cons (step911 p h) (sat_cons (step827 p h) (sat_cons (step522 p h) (sat_nil p))))
def c913 : List Lit := [(1243, false)]
theorem step913 (p : Nat → Bool) (h : Constraints p) : clause p c913 = true :=
  Snake9.LocalRup.prove_clause [c911, c900, c527] c913 (by decide) p (sat_cons (step911 p h) (sat_cons (step900 p h) (sat_cons (step527 p h) (sat_nil p))))
def c914 : List Lit := [(1327, true)]
theorem step914 (p : Nat → Bool) (h : Constraints p) : clause p c914 = true :=
  Snake9.LocalRup.prove_clause [c912, c895, c597] c914 (by decide) p (sat_cons (step912 p h) (sat_cons (step895 p h) (sat_cons (step597 p h) (sat_nil p))))
def c915 : List Lit := [(1240, false)]
theorem step915 (p : Nat → Bool) (h : Constraints p) : clause p c915 = true :=
  Snake9.LocalRup.prove_clause [c913, c478] c915 (by decide) p (sat_cons (step913 p h) (sat_cons (step478 p h) (sat_nil p)))
def c916 : List Lit := [(1234, false)]
theorem step916 (p : Nat → Bool) (h : Constraints p) : clause p c916 = true :=
  Snake9.LocalRup.prove_clause [c913, c826, c481] c916 (by decide) p (sat_cons (step913 p h) (sat_cons (step826 p h) (sat_cons (step481 p h) (sat_nil p))))
def c917 : List Lit := [(1431, false)]
theorem step917 (p : Nat → Bool) (h : Constraints p) : clause p c917 = true :=
  Snake9.LocalRup.prove_clause [c914, c695, c691] c917 (by decide) p (sat_cons (step914 p h) (sat_cons (step695 p h) (sat_cons (step691 p h) (sat_nil p))))
def c918 : List Lit := [(1237, false)]
theorem step918 (p : Nat → Bool) (h : Constraints p) : clause p c918 = true :=
  Snake9.LocalRup.prove_clause [c915, c825, c475] c918 (by decide) p (sat_cons (step915 p h) (sat_cons (step825 p h) (sat_cons (step475 p h) (sat_nil p))))
def c919 : List Lit := [(1232, false)]
theorem step919 (p : Nat → Bool) (h : Constraints p) : clause p c919 = true :=
  Snake9.LocalRup.prove_clause [c916, c464] c919 (by decide) p (sat_cons (step916 p h) (sat_cons (step464 p h) (sat_nil p)))
def c920 : List Lit := [(1418, false)]
theorem step920 (p : Nat → Bool) (h : Constraints p) : clause p c920 = true :=
  Snake9.LocalRup.prove_clause [c917, c831, c681] c920 (by decide) p (sat_cons (step917 p h) (sat_cons (step831 p h) (sat_cons (step681 p h) (sat_nil p))))
def c921 : List Lit := [(11, true)]
theorem step921 (p : Nat → Bool) (h : Constraints p) : clause p c921 = true :=
  Snake9.LocalRup.prove_clause [c918, c470] c921 (by decide) p (sat_cons (step918 p h) (sat_cons (step470 p h) (sat_nil p)))
def c922 : List Lit := [(7, true)]
theorem step922 (p : Nat → Bool) (h : Constraints p) : clause p c922 = true :=
  Snake9.LocalRup.prove_clause [c919, c461] c922 (by decide) p (sat_cons (step919 p h) (sat_cons (step461 p h) (sat_nil p)))
def c923 : List Lit := [(1410, false)]
theorem step923 (p : Nat → Bool) (h : Constraints p) : clause p c923 = true :=
  Snake9.LocalRup.prove_clause [c920, c781, c677] c923 (by decide) p (sat_cons (step920 p h) (sat_cons (step781 p h) (sat_cons (step677 p h) (sat_nil p))))
def c924 : List Lit := [(3, false)]
theorem step924 (p : Nat → Bool) (h : Constraints p) : clause p c924 = true :=
  Snake9.LocalRup.prove_clause [c921, c906, c922, c12] c924 (by decide) p (sat_cons (step921 p h) (sat_cons (step906 p h) (sat_cons (step922 p h) (sat_cons (step12 p h) (sat_nil p)))))
def c925 : List Lit := [(1398, false)]
theorem step925 (p : Nat → Bool) (h : Constraints p) : clause p c925 = true :=
  Snake9.LocalRup.prove_clause [c923, c779, c675] c925 (by decide) p (sat_cons (step923 p h) (sat_cons (step779 p h) (sat_cons (step675 p h) (sat_nil p))))
def c926 : List Lit := [(111, true)]
theorem step926 (p : Nat → Bool) (h : Constraints p) : clause p c926 = true :=
  Snake9.LocalRup.prove_clause [c924, c922, c24] c926 (by decide) p (sat_cons (step924 p h) (sat_cons (step922 p h) (sat_cons (step24 p h) (sat_nil p))))
def c927 : List Lit := [(1396, false)]
theorem step927 (p : Nat → Bool) (h : Constraints p) : clause p c927 = true :=
  Snake9.LocalRup.prove_clause [c925, c666] c927 (by decide) p (sat_cons (step925 p h) (sat_cons (step666 p h) (sat_nil p)))
def c928 : List Lit := [(221, true)]
theorem step928 (p : Nat → Bool) (h : Constraints p) : clause p c928 = true :=
  Snake9.LocalRup.prove_clause [c926, c236] c928 (by decide) p (sat_cons (step926 p h) (sat_cons (step236 p h) (sat_nil p)))
def c929 : List Lit := [(93, true)]
theorem step929 (p : Nat → Bool) (h : Constraints p) : clause p c929 = true :=
  Snake9.LocalRup.prove_clause [c927, c665] c929 (by decide) p (sat_cons (step927 p h) (sat_cons (step665 p h) (sat_nil p)))
def c930 : List Lit := [(227, true)]
theorem step930 (p : Nat → Bool) (h : Constraints p) : clause p c930 = true :=
  Snake9.LocalRup.prove_clause [c928, c241] c930 (by decide) p (sat_cons (step928 p h) (sat_cons (step241 p h) (sat_nil p)))
def c931 : List Lit := [(64, false)]
theorem step931 (p : Nat → Bool) (h : Constraints p) : clause p c931 = true :=
  Snake9.LocalRup.prove_clause [c929, c879, c904, c139] c931 (by decide) p (sat_cons (step929 p h) (sat_cons (step879 p h) (sat_cons (step904 p h) (sat_cons (step139 p h) (sat_nil p)))))
def c932 : List Lit := [(229, true)]
theorem step932 (p : Nat → Bool) (h : Constraints p) : clause p c932 = true :=
  Snake9.LocalRup.prove_clause [c930, c243] c932 (by decide) p (sat_cons (step930 p h) (sat_cons (step243 p h) (sat_nil p)))
def c933 : List Lit := [(169, true)]
theorem step933 (p : Nat → Bool) (h : Constraints p) : clause p c933 = true :=
  Snake9.LocalRup.prove_clause [c931, c879, c140] c933 (by decide) p (sat_cons (step931 p h) (sat_cons (step879 p h) (sat_cons (step140 p h) (sat_nil p))))
def c934 : List Lit := [(255, true)]
theorem step934 (p : Nat → Bool) (h : Constraints p) : clause p c934 = true :=
  Snake9.LocalRup.prove_clause [c932, c276] c934 (by decide) p (sat_cons (step932 p h) (sat_cons (step276 p h) (sat_nil p)))
def c935 : List Lit := [(325, true)]
theorem step935 (p : Nat → Bool) (h : Constraints p) : clause p c935 = true :=
  Snake9.LocalRup.prove_clause [c933, c343] c935 (by decide) p (sat_cons (step933 p h) (sat_cons (step343 p h) (sat_nil p)))
def c936 : List Lit := [(307, true)]
theorem step936 (p : Nat → Bool) (h : Constraints p) : clause p c936 = true :=
  Snake9.LocalRup.prove_clause [c934, c327] c936 (by decide) p (sat_cons (step934 p h) (sat_cons (step327 p h) (sat_nil p)))
def c937 : List Lit := [(327, true)]
theorem step937 (p : Nat → Bool) (h : Constraints p) : clause p c937 = true :=
  Snake9.LocalRup.prove_clause [c935, c344] c937 (by decide) p (sat_cons (step935 p h) (sat_cons (step344 p h) (sat_nil p)))
def c938 : List Lit := [(409, false)]
theorem step938 (p : Nat → Bool) (h : Constraints p) : clause p c938 = true :=
  Snake9.LocalRup.prove_clause [c936, c424, c422] c938 (by decide) p (sat_cons (step936 p h) (sat_cons (step424 p h) (sat_cons (step422 p h) (sat_nil p))))
def c939 : List Lit := [(329, true)]
theorem step939 (p : Nat → Bool) (h : Constraints p) : clause p c939 = true :=
  Snake9.LocalRup.prove_clause [c937, c346] c939 (by decide) p (sat_cons (step937 p h) (sat_cons (step346 p h) (sat_nil p)))
def c940 : List Lit := [(357, false)]
theorem step940 (p : Nat → Bool) (h : Constraints p) : clause p c940 = true :=
  Snake9.LocalRup.prove_clause [c938, c419] c940 (by decide) p (sat_cons (step938 p h) (sat_cons (step419 p h) (sat_nil p)))
def c941 : List Lit := [(331, true)]
theorem step941 (p : Nat → Bool) (h : Constraints p) : clause p c941 = true :=
  Snake9.LocalRup.prove_clause [c939, c348] c941 (by decide) p (sat_cons (step939 p h) (sat_cons (step348 p h) (sat_nil p)))
def c942 : List Lit := []
theorem step942 (p : Nat → Bool) (h : Constraints p) : clause p c942 = true :=
  Snake9.LocalRup.prove_clause [c941, c940, c373] c942 (by decide) p (sat_cons (step941 p h) (sat_cons (step940 p h) (sat_cons (step373 p h) (sat_nil p))))
end B112E145
