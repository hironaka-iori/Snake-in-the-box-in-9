import B112E121Part0080
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6908 : List Lit := [(1023, false)]
theorem step6908 (p : Nat → Bool) (h : Constraints p) : clause p c6908 = true :=
  Snake9.LocalRup.prove_clause [c6906, c1404] c6908 (by decide) p (sat_cons (step6906 p h) (sat_cons (step1404 p h) (sat_nil p)))
def c6909 : List Lit := [(85, false)]
theorem step6909 (p : Nat → Bool) (h : Constraints p) : clause p c6909 = true :=
  Snake9.LocalRup.prove_clause [c6906, c2212] c6909 (by decide) p (sat_cons (step6906 p h) (sat_cons (step2212 p h) (sat_nil p)))
def c6910 : List Lit := [(78, true)]
theorem step6910 (p : Nat → Bool) (h : Constraints p) : clause p c6910 = true :=
  Snake9.LocalRup.prove_clause [c6907, c1399] c6910 (by decide) p (sat_cons (step6907 p h) (sat_cons (step1399 p h) (sat_nil p)))
def c6911 : List Lit := [(77, true)]
theorem step6911 (p : Nat → Bool) (h : Constraints p) : clause p c6911 = true :=
  Snake9.LocalRup.prove_clause [c6907, c1400] c6911 (by decide) p (sat_cons (step6907 p h) (sat_cons (step1400 p h) (sat_nil p)))
def c6912 : List Lit := [(74, true)]
theorem step6912 (p : Nat → Bool) (h : Constraints p) : clause p c6912 = true :=
  Snake9.LocalRup.prove_clause [c6908, c1396] c6912 (by decide) p (sat_cons (step6908 p h) (sat_cons (step1396 p h) (sat_nil p)))
def c6913 : List Lit := [(71, true)]
theorem step6913 (p : Nat → Bool) (h : Constraints p) : clause p c6913 = true :=
  Snake9.LocalRup.prove_clause [c6908, c1397] c6913 (by decide) p (sat_cons (step6908 p h) (sat_cons (step1397 p h) (sat_nil p)))
def c6914 : List Lit := [(1041, true)]
theorem step6914 (p : Nat → Bool) (h : Constraints p) : clause p c6914 = true :=
  Snake9.LocalRup.prove_clause [c6909, c1428] c6914 (by decide) p (sat_cons (step6909 p h) (sat_cons (step1428 p h) (sat_nil p)))
def c6915 : List Lit := [(1084, true)]
theorem step6915 (p : Nat → Bool) (h : Constraints p) : clause p c6915 = true :=
  Snake9.LocalRup.prove_clause [c6911, c6875, c6344, c4858] c6915 (by decide) p (sat_cons (step6911 p h) (sat_cons (step6875 p h) (sat_cons (step6344 p h) (sat_cons (step4858 p h) (sat_nil p)))))
def c6916 : List Lit := [(980, true)]
theorem step6916 (p : Nat → Bool) (h : Constraints p) : clause p c6916 = true :=
  Snake9.LocalRup.prove_clause [c6913, c6875, c6684, c5950, c4891] c6916 (by decide) p (sat_cons (step6913 p h) (sat_cons (step6875 p h) (sat_cons (step6684 p h) (sat_cons (step5950 p h) (sat_cons (step4891 p h) (sat_nil p))))))
def c6917 : List Lit := [(88, false), (100, false)]
theorem step6917 (p : Nat → Bool) (h : Constraints p) : clause p c6917 = true :=
  Snake9.LocalRup.prove_clause [c6344, c6875, c6915, c6912, c6910, c6711, c6911, c6913, c2233, c783, c4681, c1515, c2285, c1472, c5463, c5438, c3288, c1530, c1534, c1516, c5457] c6917 (by decide) p (sat_cons (step6344 p h) (sat_cons (step6875 p h) (sat_cons (step6915 p h) (sat_cons (step6912 p h) (sat_cons (step6910 p h) (sat_cons (step6711 p h) (sat_cons (step6911 p h) (sat_cons (step6913 p h) (sat_cons (step2233 p h) (sat_cons (step783 p h) (sat_cons (step4681 p h) (sat_cons (step1515 p h) (sat_cons (step2285 p h) (sat_cons (step1472 p h) (sat_cons (step5463 p h) (sat_cons (step5438 p h) (sat_cons (step3288 p h) (sat_cons (step1530 p h) (sat_cons (step1534 p h) (sat_cons (step1516 p h) (sat_cons (step5457 p h) (sat_nil p))))))))))))))))))))))
def c6918 : List Lit := [(88, false)]
theorem step6918 (p : Nat → Bool) (h : Constraints p) : clause p c6918 = true :=
  Snake9.LocalRup.prove_clause [c6886, c6917] c6918 (by decide) p (sat_cons (step6886 p h) (sat_cons (step6917 p h) (sat_nil p)))
def c6919 : List Lit := [(1047, true)]
theorem step6919 (p : Nat → Bool) (h : Constraints p) : clause p c6919 = true :=
  Snake9.LocalRup.prove_clause [c6918, c1438] c6919 (by decide) p (sat_cons (step6918 p h) (sat_cons (step1438 p h) (sat_nil p)))
def c6920 : List Lit := [(1057, true)]
theorem step6920 (p : Nat → Bool) (h : Constraints p) : clause p c6920 = true :=
  Snake9.LocalRup.prove_clause [c6919, c6875, c6913, c6911, c2278] c6920 (by decide) p (sat_cons (step6919 p h) (sat_cons (step6875 p h) (sat_cons (step6913 p h) (sat_cons (step6911 p h) (sat_cons (step2278 p h) (sat_nil p))))))
def c6921 : List Lit := [(1066, true)]
theorem step6921 (p : Nat → Bool) (h : Constraints p) : clause p c6921 = true :=
  Snake9.LocalRup.prove_clause [c6920, c6711, c1472] c6921 (by decide) p (sat_cons (step6920 p h) (sat_cons (step6711 p h) (sat_cons (step1472 p h) (sat_nil p))))
def c6922 : List Lit := [(1132, false)]
theorem step6922 (p : Nat → Bool) (h : Constraints p) : clause p c6922 = true :=
  Snake9.LocalRup.prove_clause [c6921, c6916, c6918, c6913, c6911, c6875, c6711, c6684, c1613, c2107, c5436, c6360, c6392, c1364, c1963, c5857, c1217, c1268, c1473, c1868, c1620, c1330, c2106, c6716] c6922 (by decide) p (sat_cons (step6921 p h) (sat_cons (step6916 p h) (sat_cons (step6918 p h) (sat_cons (step6913 p h) (sat_cons (step6911 p h) (sat_cons (step6875 p h) (sat_cons (step6711 p h) (sat_cons (step6684 p h) (sat_cons (step1613 p h) (sat_cons (step2107 p h) (sat_cons (step5436 p h) (sat_cons (step6360 p h) (sat_cons (step6392 p h) (sat_cons (step1364 p h) (sat_cons (step1963 p h) (sat_cons (step5857 p h) (sat_cons (step1217 p h) (sat_cons (step1268 p h) (sat_cons (step1473 p h) (sat_cons (step1868 p h) (sat_cons (step1620 p h) (sat_cons (step1330 p h) (sat_cons (step2106 p h) (sat_cons (step6716 p h) (sat_nil p)))))))))))))))))))))))))
def c6923 : List Lit := [(1099, false)]
theorem step6923 (p : Nat → Bool) (h : Constraints p) : clause p c6923 = true :=
  Snake9.LocalRup.prove_clause [c6922, c2093] c6923 (by decide) p (sat_cons (step6922 p h) (sat_cons (step2093 p h) (sat_nil p)))
def c6924 : List Lit := [(1098, false)]
theorem step6924 (p : Nat → Bool) (h : Constraints p) : clause p c6924 = true :=
  Snake9.LocalRup.prove_clause [c6922, c6876, c1587] c6924 (by decide) p (sat_cons (step6922 p h) (sat_cons (step6876 p h) (sat_cons (step1587 p h) (sat_nil p))))
def c6925 : List Lit := [(100, false)]
theorem step6925 (p : Nat → Bool) (h : Constraints p) : clause p c6925 = true :=
  Snake9.LocalRup.prove_clause [c6922, c6913, c6899] c6925 (by decide) p (sat_cons (step6922 p h) (sat_cons (step6913 p h) (sat_cons (step6899 p h) (sat_nil p))))
def c6926 : List Lit := [(93, false)]
theorem step6926 (p : Nat → Bool) (h : Constraints p) : clause p c6926 = true :=
  Snake9.LocalRup.prove_clause [c6925, c6918, c6910, c6924, c6901] c6926 (by decide) p (sat_cons (step6925 p h) (sat_cons (step6918 p h) (sat_cons (step6910 p h) (sat_cons (step6924 p h) (sat_cons (step6901 p h) (sat_nil p))))))
def c6927 : List Lit := [(106, false)]
theorem step6927 (p : Nat → Bool) (h : Constraints p) : clause p c6927 = true :=
  Snake9.LocalRup.prove_clause [c6925, c6924, c6911, c6875, c6344, c4903] c6927 (by decide) p (sat_cons (step6925 p h) (sat_cons (step6924 p h) (sat_cons (step6911 p h) (sat_cons (step6875 p h) (sat_cons (step6344 p h) (sat_cons (step4903 p h) (sat_nil p)))))))
def c6928 : List Lit := [(1049, true)]
theorem step6928 (p : Nat → Bool) (h : Constraints p) : clause p c6928 = true :=
  Snake9.LocalRup.prove_clause [c6926, c1440] c6928 (by decide) p (sat_cons (step6926 p h) (sat_cons (step1440 p h) (sat_nil p)))
def c6929 : List Lit := [(1087, true)]
theorem step6929 (p : Nat → Bool) (h : Constraints p) : clause p c6929 = true :=
  Snake9.LocalRup.prove_clause [c6927, c1504] c6929 (by decide) p (sat_cons (step6927 p h) (sat_cons (step1504 p h) (sat_nil p)))
def c6930 : List Lit := [(89, false)]
theorem step6930 (p : Nat → Bool) (h : Constraints p) : clause p c6930 = true :=
  Snake9.LocalRup.prove_clause [c6929, c6875, c6344, c6923, c4041] c6930 (by decide) p (sat_cons (step6929 p h) (sat_cons (step6875 p h) (sat_cons (step6344 p h) (sat_cons (step6923 p h) (sat_cons (step4041 p h) (sat_nil p))))))
def c6931 : List Lit := [(1048, true)]
theorem step6931 (p : Nat → Bool) (h : Constraints p) : clause p c6931 = true :=
  Snake9.LocalRup.prove_clause [c6930, c6918, c1439] c6931 (by decide) p (sat_cons (step6930 p h) (sat_cons (step6918 p h) (sat_cons (step1439 p h) (sat_nil p))))
def c6932 : List Lit := [(1053, true)]
theorem step6932 (p : Nat → Bool) (h : Constraints p) : clause p c6932 = true :=
  Snake9.LocalRup.prove_clause [c6931, c6928, c1449] c6932 (by decide) p (sat_cons (step6931 p h) (sat_cons (step6928 p h) (sat_cons (step1449 p h) (sat_nil p))))
def c6933 : List Lit := [(1058, true)]
theorem step6933 (p : Nat → Bool) (h : Constraints p) : clause p c6933 = true :=
  Snake9.LocalRup.prove_clause [c6932, c2078] c6933 (by decide) p (sat_cons (step6932 p h) (sat_cons (step2078 p h) (sat_nil p)))
def c6934 : List Lit := [(1045, false)]
theorem step6934 (p : Nat → Bool) (h : Constraints p) : clause p c6934 = true :=
  Snake9.LocalRup.prove_clause [c6932, c6879, c1464] c6934 (by decide) p (sat_cons (step6932 p h) (sat_cons (step6879 p h) (sat_cons (step1464 p h) (sat_nil p))))
def c6935 : List Lit := [(1067, true)]
theorem step6935 (p : Nat → Bool) (h : Constraints p) : clause p c6935 = true :=
  Snake9.LocalRup.prove_clause [c6933, c6711, c1473] c6935 (by decide) p (sat_cons (step6933 p h) (sat_cons (step6711 p h) (sat_cons (step1473 p h) (sat_nil p))))
def c6936 : List Lit := [(1040, false)]
theorem step6936 (p : Nat → Bool) (h : Constraints p) : clause p c6936 = true :=
  Snake9.LocalRup.prove_clause [c6934, c6914, c1436] c6936 (by decide) p (sat_cons (step6934 p h) (sat_cons (step6914 p h) (sat_cons (step1436 p h) (sat_nil p))))
def c6937 : List Lit := [(1152, true)]
theorem step6937 (p : Nat → Bool) (h : Constraints p) : clause p c6937 = true :=
  Snake9.LocalRup.prove_clause [c6935, c6877, c1619] c6937 (by decide) p (sat_cons (step6935 p h) (sat_cons (step6877 p h) (sat_cons (step1619 p h) (sat_nil p))))
def c6938 : List Lit := [(1004, false)]
theorem step6938 (p : Nat → Bool) (h : Constraints p) : clause p c6938 = true :=
  Snake9.LocalRup.prove_clause [c6937, c2107] c6938 (by decide) p (sat_cons (step6937 p h) (sat_cons (step2107 p h) (sat_nil p)))
def c6939 : List Lit := [(13, false)]
theorem step6939 (p : Nat → Bool) (h : Constraints p) : clause p c6939 = true :=
  Snake9.LocalRup.prove_clause [c6938, c6392] c6939 (by decide) p (sat_cons (step6938 p h) (sat_cons (step6392 p h) (sat_nil p)))
def c6940 : List Lit := [(82, true)]
theorem step6940 (p : Nat → Bool) (h : Constraints p) : clause p c6940 = true :=
  Snake9.LocalRup.prove_clause [c6939, c6913, c6875, c1992] c6940 (by decide) p (sat_cons (step6939 p h) (sat_cons (step6913 p h) (sat_cons (step6875 p h) (sat_cons (step1992 p h) (sat_nil p)))))
def c6941 : List Lit := [(79, false)]
theorem step6941 (p : Nat → Bool) (h : Constraints p) : clause p c6941 = true :=
  Snake9.LocalRup.prove_clause [c6940, c6909, c6934, c6913, c4612] c6941 (by decide) p (sat_cons (step6940 p h) (sat_cons (step6909 p h) (sat_cons (step6934 p h) (sat_cons (step6913 p h) (sat_cons (step4612 p h) (sat_nil p))))))
def c6942 : List Lit := [(1039, true)]
theorem step6942 (p : Nat → Bool) (h : Constraints p) : clause p c6942 = true :=
  Snake9.LocalRup.prove_clause [c6941, c1425] c6942 (by decide) p (sat_cons (step6941 p h) (sat_cons (step1425 p h) (sat_nil p)))
def c6943 : List Lit := [(81, true)]
theorem step6943 (p : Nat → Bool) (h : Constraints p) : clause p c6943 = true :=
  Snake9.LocalRup.prove_clause [c6941, c6936, c1426] c6943 (by decide) p (sat_cons (step6941 p h) (sat_cons (step6936 p h) (sat_cons (step1426 p h) (sat_nil p))))
def c6944 : List Lit := [(1042, false)]
theorem step6944 (p : Nat → Bool) (h : Constraints p) : clause p c6944 = true :=
  Snake9.LocalRup.prove_clause [c6942, c6934, c1434] c6944 (by decide) p (sat_cons (step6942 p h) (sat_cons (step6934 p h) (sat_cons (step1434 p h) (sat_nil p))))
def c6945 : List Lit := [(86, false)]
theorem step6945 (p : Nat → Bool) (h : Constraints p) : clause p c6945 = true :=
  Snake9.LocalRup.prove_clause [c6943, c6940, c6913, c585] c6945 (by decide) p (sat_cons (step6943 p h) (sat_cons (step6940 p h) (sat_cons (step6913 p h) (sat_cons (step585 p h) (sat_nil p)))))
def c6946 : List Lit := []
theorem step6946 (p : Nat → Bool) (h : Constraints p) : clause p c6946 = true :=
  Snake9.LocalRup.prove_clause [c6945, c6944, c6909, c1429] c6946 (by decide) p (sat_cons (step6945 p h) (sat_cons (step6944 p h) (sat_cons (step6909 p h) (sat_cons (step1429 p h) (sat_nil p)))))
end B112E121
