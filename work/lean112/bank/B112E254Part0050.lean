import B112E254Part0049
namespace B112E254
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4615 : List Lit := [(1526, false), (1516, false), (1562, false)]
theorem step4615 (p : Nat → Bool) (h : Constraints p) : clause p c4615 = true :=
  Snake9.LocalRup.prove_clause [c4609, c4594, c4595, c4608, c4593, c4334, c978, c1008, c938, c939, c949, c958, c933, c976, c1093, c1855, c4614, c954, c977, c1097, c1854, c2166, c1016, c929, c1011, c4153] c4615 (by decide) p (sat_cons (step4609 p h) (sat_cons (step4594 p h) (sat_cons (step4595 p h) (sat_cons (step4608 p h) (sat_cons (step4593 p h) (sat_cons (step4334 p h) (sat_cons (step978 p h) (sat_cons (step1008 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step949 p h) (sat_cons (step958 p h) (sat_cons (step933 p h) (sat_cons (step976 p h) (sat_cons (step1093 p h) (sat_cons (step1855 p h) (sat_cons (step4614 p h) (sat_cons (step954 p h) (sat_cons (step977 p h) (sat_cons (step1097 p h) (sat_cons (step1854 p h) (sat_cons (step2166 p h) (sat_cons (step1016 p h) (sat_cons (step929 p h) (sat_cons (step1011 p h) (sat_cons (step4153 p h) (sat_nil p)))))))))))))))))))))))))))
def c4616 : List Lit := [(1601, true), (1510, false), (1562, false)]
theorem step4616 (p : Nat → Bool) (h : Constraints p) : clause p c4616 = true :=
  Snake9.LocalRup.prove_clause [c4593, c1854, c4364, c1016, c4312, c1011, c1002] c4616 (by decide) p (sat_cons (step4593 p h) (sat_cons (step1854 p h) (sat_cons (step4364 p h) (sat_cons (step1016 p h) (sat_cons (step4312 p h) (sat_cons (step1011 p h) (sat_cons (step1002 p h) (sat_nil p))))))))
def c4617 : List Lit := [(1560, true), (1601, false), (10, true)]
theorem step4617 (p : Nat → Bool) (h : Constraints p) : clause p c4617 = true :=
  Snake9.LocalRup.prove_clause [c4608, c4593, c4294, c900, c4317, c1097, c977, c1002, c4325, c4267, c926, c954, c936, c933, c4226, c4256, c4299] c4617 (by decide) p (sat_cons (step4608 p h) (sat_cons (step4593 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step4317 p h) (sat_cons (step1097 p h) (sat_cons (step977 p h) (sat_cons (step1002 p h) (sat_cons (step4325 p h) (sat_cons (step4267 p h) (sat_cons (step926 p h) (sat_cons (step954 p h) (sat_cons (step936 p h) (sat_cons (step933 p h) (sat_cons (step4226 p h) (sat_cons (step4256 p h) (sat_cons (step4299 p h) (sat_nil p))))))))))))))))))
def c4618 : List Lit := [(1522, false), (10, true), (1562, false)]
theorem step4618 (p : Nat → Bool) (h : Constraints p) : clause p c4618 = true :=
  Snake9.LocalRup.prove_clause [c4608, c4294, c900, c4616, c4617, c4317, c1097, c977, c957, c926, c929, c953, c954, c976, c936, c1093, c933, c1855, c2595] c4618 (by decide) p (sat_cons (step4608 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step4616 p h) (sat_cons (step4617 p h) (sat_cons (step4317 p h) (sat_cons (step1097 p h) (sat_cons (step977 p h) (sat_cons (step957 p h) (sat_cons (step926 p h) (sat_cons (step929 p h) (sat_cons (step953 p h) (sat_cons (step954 p h) (sat_cons (step976 p h) (sat_cons (step936 p h) (sat_cons (step1093 p h) (sat_cons (step933 p h) (sat_cons (step1855 p h) (sat_cons (step2595 p h) (sat_nil p))))))))))))))))))))
def c4619 : List Lit := [(1524, false), (1530, true), (31, false), (81, true), (1601, false), (10, true)]
theorem step4619 (p : Nat → Bool) (h : Constraints p) : clause p c4619 = true :=
  Snake9.LocalRup.prove_clause [c4608, c4593, c4617, c4294, c900, c4226, c4252, c4299] c4619 (by decide) p (sat_cons (step4608 p h) (sat_cons (step4593 p h) (sat_cons (step4617 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step4226 p h) (sat_cons (step4252 p h) (sat_cons (step4299 p h) (sat_nil p)))))))))
def c4620 : List Lit := [(1524, true), (1528, true), (41, true), (27, false), (10, true)]
theorem step4620 (p : Nat → Bool) (h : Constraints p) : clause p c4620 = true :=
  Snake9.LocalRup.prove_clause [c4593, c4608, c934, c933, c4294, c900, c4298, c4184] c4620 (by decide) p (sat_cons (step4593 p h) (sat_cons (step4608 p h) (sat_cons (step934 p h) (sat_cons (step933 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step4298 p h) (sat_cons (step4184 p h) (sat_nil p)))))))))
def c4621 : List Lit := [(1528, true), (81, true), (41, true), (1601, false), (27, false), (10, true)]
theorem step4621 (p : Nat → Bool) (h : Constraints p) : clause p c4621 = true :=
  Snake9.LocalRup.prove_clause [c4608, c4294, c900, c4317, c1097, c977, c933, c4620, c954, c4619] c4621 (by decide) p (sat_cons (step4608 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step4317 p h) (sat_cons (step1097 p h) (sat_cons (step977 p h) (sat_cons (step933 p h) (sat_cons (step4620 p h) (sat_cons (step954 p h) (sat_cons (step4619 p h) (sat_nil p)))))))))))
def c4622 : List Lit := [(10, true), (1562, false)]
theorem step4622 (p : Nat → Bool) (h : Constraints p) : clause p c4622 = true :=
  Snake9.LocalRup.prove_clause [c4593, c4595, c4594, c4608, c4294, c900, c4317, c4615, c930, c4616, c1097, c977, c4617, c1011, c1016, c4618, c4267, c4271, c4621, c936, c949, c954, c976, c928, c1093, c1855, c1065, c1020, c1852, c2022, c1033, c1027] c4622 (by decide) p (sat_cons (step4593 p h) (sat_cons (step4595 p h) (sat_cons (step4594 p h) (sat_cons (step4608 p h) (sat_cons (step4294 p h) (sat_cons (step900 p h) (sat_cons (step4317 p h) (sat_cons (step4615 p h) (sat_cons (step930 p h) (sat_cons (step4616 p h) (sat_cons (step1097 p h) (sat_cons (step977 p h) (sat_cons (step4617 p h) (sat_cons (step1011 p h) (sat_cons (step1016 p h) (sat_cons (step4618 p h) (sat_cons (step4267 p h) (sat_cons (step4271 p h) (sat_cons (step4621 p h) (sat_cons (step936 p h) (sat_cons (step949 p h) (sat_cons (step954 p h) (sat_cons (step976 p h) (sat_cons (step928 p h) (sat_cons (step1093 p h) (sat_cons (step1855 p h) (sat_cons (step1065 p h) (sat_cons (step1020 p h) (sat_cons (step1852 p h) (sat_cons (step2022 p h) (sat_cons (step1033 p h) (sat_cons (step1027 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c4623 : List Lit := [(10, false), (1562, false)]
theorem step4623 (p : Nat → Bool) (h : Constraints p) : clause p c4623 = true :=
  Snake9.LocalRup.prove_clause [c4608, c4596, c4612, c4613, c894, c987, c902, c1097, c4616] c4623 (by decide) p (sat_cons (step4608 p h) (sat_cons (step4596 p h) (sat_cons (step4612 p h) (sat_cons (step4613 p h) (sat_cons (step894 p h) (sat_cons (step987 p h) (sat_cons (step902 p h) (sat_cons (step1097 p h) (sat_cons (step4616 p h) (sat_nil p))))))))))
def c4624 : List Lit := [(1562, false)]
theorem step4624 (p : Nat → Bool) (h : Constraints p) : clause p c4624 = true :=
  Snake9.LocalRup.prove_clause [c4622, c4623] c4624 (by decide) p (sat_cons (step4622 p h) (sat_cons (step4623 p h) (sat_nil p)))
def c4625 : List Lit := [(45, true)]
theorem step4625 (p : Nat → Bool) (h : Constraints p) : clause p c4625 = true :=
  Snake9.LocalRup.prove_clause [c4624, c1005] c4625 (by decide) p (sat_cons (step4624 p h) (sat_cons (step1005 p h) (sat_nil p)))
def c4626 : List Lit := [(10, false)]
theorem step4626 (p : Nat → Bool) (h : Constraints p) : clause p c4626 = true :=
  Snake9.LocalRup.prove_clause [c4625, c4593, c4595, c4609, c4608, c4594, c4324, c55, c34, c44, c930, c1450, c895, c938, c4332, c902, c949, c919, c983, c982, c4366, c954, c1097, c1010, c928, c2166] c4626 (by decide) p (sat_cons (step4625 p h) (sat_cons (step4593 p h) (sat_cons (step4595 p h) (sat_cons (step4609 p h) (sat_cons (step4608 p h) (sat_cons (step4594 p h) (sat_cons (step4324 p h) (sat_cons (step55 p h) (sat_cons (step34 p h) (sat_cons (step44 p h) (sat_cons (step930 p h) (sat_cons (step1450 p h) (sat_cons (step895 p h) (sat_cons (step938 p h) (sat_cons (step4332 p h) (sat_cons (step902 p h) (sat_cons (step949 p h) (sat_cons (step919 p h) (sat_cons (step983 p h) (sat_cons (step982 p h) (sat_cons (step4366 p h) (sat_cons (step954 p h) (sat_cons (step1097 p h) (sat_cons (step1010 p h) (sat_cons (step928 p h) (sat_cons (step2166 p h) (sat_nil p)))))))))))))))))))))))))))
def c4627 : List Lit := [(1508, true)]
theorem step4627 (p : Nat → Bool) (h : Constraints p) : clause p c4627 = true :=
  Snake9.LocalRup.prove_clause [c4626, c4294] c4627 (by decide) p (sat_cons (step4626 p h) (sat_cons (step4294 p h) (sat_nil p)))
def c4628 : List Lit := [(104, true)]
theorem step4628 (p : Nat → Bool) (h : Constraints p) : clause p c4628 = true :=
  Snake9.LocalRup.prove_clause [c4626, c4625, c1737] c4628 (by decide) p (sat_cons (step4626 p h) (sat_cons (step4625 p h) (sat_cons (step1737 p h) (sat_nil p))))
def c4629 : List Lit := [(1510, true)]
theorem step4629 (p : Nat → Bool) (h : Constraints p) : clause p c4629 = true :=
  Snake9.LocalRup.prove_clause [c4627, c900] c4629 (by decide) p (sat_cons (step4627 p h) (sat_cons (step900 p h) (sat_nil p)))
def c4630 : List Lit := [(1516, true)]
theorem step4630 (p : Nat → Bool) (h : Constraints p) : clause p c4630 = true :=
  Snake9.LocalRup.prove_clause [c4629, c4317] c4630 (by decide) p (sat_cons (step4629 p h) (sat_cons (step4317 p h) (sat_nil p)))
def c4631 : List Lit := [(1544, true)]
theorem step4631 (p : Nat → Bool) (h : Constraints p) : clause p c4631 = true :=
  Snake9.LocalRup.prove_clause [c4630, c4596, c975] c4631 (by decide) p (sat_cons (step4630 p h) (sat_cons (step4596 p h) (sat_cons (step975 p h) (sat_nil p))))
def c4632 : List Lit := [(1537, false)]
theorem step4632 (p : Nat → Bool) (h : Constraints p) : clause p c4632 = true :=
  Snake9.LocalRup.prove_clause [c4630, c4609, c978] c4632 (by decide) p (sat_cons (step4630 p h) (sat_cons (step4609 p h) (sat_cons (step978 p h) (sat_nil p))))
def c4633 : List Lit := [(1531, false)]
theorem step4633 (p : Nat → Bool) (h : Constraints p) : clause p c4633 = true :=
  Snake9.LocalRup.prove_clause [c4630, c4594, c4593, c4608, c4334] c4633 (by decide) p (sat_cons (step4630 p h) (sat_cons (step4594 p h) (sat_cons (step4593 p h) (sat_cons (step4608 p h) (sat_cons (step4334 p h) (sat_nil p))))))
def c4634 : List Lit := [(1529, false)]
theorem step4634 (p : Nat → Bool) (h : Constraints p) : clause p c4634 = true :=
  Snake9.LocalRup.prove_clause [c4633, c937] c4634 (by decide) p (sat_cons (step4633 p h) (sat_cons (step937 p h) (sat_nil p)))
def c4635 : List Lit := [(31, false), (12, true)]
theorem step4635 (p : Nat → Bool) (h : Constraints p) : clause p c4635 = true :=
  Snake9.LocalRup.prove_clause [c4626, c4593, c4608, c4169, c4226] c4635 (by decide) p (sat_cons (step4626 p h) (sat_cons (step4593 p h) (sat_cons (step4608 p h) (sat_cons (step4169 p h) (sat_cons (step4226 p h) (sat_nil p))))))
def c4636 : List Lit := [(1524, true), (1601, true)]
theorem step4636 (p : Nat → Bool) (h : Constraints p) : clause p c4636 = true :=
  Snake9.LocalRup.prove_clause [c4594, c4593, c926, c928, c4267, c2166, c1002, c1010] c4636 (by decide) p (sat_cons (step4594 p h) (sat_cons (step4593 p h) (sat_cons (step926 p h) (sat_cons (step928 p h) (sat_cons (step4267 p h) (sat_cons (step2166 p h) (sat_cons (step1002 p h) (sat_cons (step1010 p h) (sat_nil p)))))))))
def c4637 : List Lit := [(1530, false), (1546, false), (1601, true)]
theorem step4637 (p : Nat → Bool) (h : Constraints p) : clause p c4637 = true :=
  Snake9.LocalRup.prove_clause [c4632, c4609, c4627, c4633, c4628, c4634, c4626, c4608, c4629, c4593, c1865, c1889, c4636, c958, c954, c983, c4330, c919, c903, c4332, c894, c895, c1450, c3719, c1691, c4464, c4250, c1106, c4270, c1111, c935, c4395, c4208, c4153, c929] c4637 (by decide) p (sat_cons (step4632 p h) (sat_cons (step4609 p h) (sat_cons (step4627 p h) (sat_cons (step4633 p h) (sat_cons (step4628 p h) (sat_cons (step4634 p h) (sat_cons (step4626 p h) (sat_cons (step4608 p h) (sat_cons (step4629 p h) (sat_cons (step4593 p h) (sat_cons (step1865 p h) (sat_cons (step1889 p h) (sat_cons (step4636 p h) (sat_cons (step958 p h) (sat_cons (step954 p h) (sat_cons (step983 p h) (sat_cons (step4330 p h) (sat_cons (step919 p h) (sat_cons (step903 p h) (sat_cons (step4332 p h) (sat_cons (step894 p h) (sat_cons (step895 p h) (sat_cons (step1450 p h) (sat_cons (step3719 p h) (sat_cons (step1691 p h) (sat_cons (step4464 p h) (sat_cons (step4250 p h) (sat_cons (step1106 p h) (sat_cons (step4270 p h) (sat_cons (step1111 p h) (sat_cons (step935 p h) (sat_cons (step4395 p h) (sat_cons (step4208 p h) (sat_cons (step4153 p h) (sat_cons (step929 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c4638 : List Lit := [(1546, false), (1601, true)]
theorem step4638 (p : Nat → Bool) (h : Constraints p) : clause p c4638 = true :=
  Snake9.LocalRup.prove_clause [c4628, c4593, c4631, c4626, c2214, c1235, c1864, c1888, c4637, c936, c938, c933, c934, c930, c4635, c83, c1529, c1524, c1714, c1698, c4318, c344, c1146, c4305, c4304, c1148, c1223, c4443, c449, c3806, c1690, c4462, c4496, c1117] c4638 (by decide) p (sat_cons (step4628 p h) (sat_cons (step4593 p h) (sat_cons (step4631 p h) (sat_cons (step4626 p h) (sat_cons (step2214 p h) (sat_cons (step1235 p h) (sat_cons (step1864 p h) (sat_cons (step1888 p h) (sat_cons (step4637 p h) (sat_cons (step936 p h) (sat_cons (step938 p h) (sat_cons (step933 p h) (sat_cons (step934 p h) (sat_cons (step930 p h) (sat_cons (step4635 p h) (sat_cons (step83 p h) (sat_cons (step1529 p h) (sat_cons (step1524 p h) (sat_cons (step1714 p h) (sat_cons (step1698 p h) (sat_cons (step4318 p h) (sat_cons (step344 p h) (sat_cons (step1146 p h) (sat_cons (step4305 p h) (sat_cons (step4304 p h) (sat_cons (step1148 p h) (sat_cons (step1223 p h) (sat_cons (step4443 p h) (sat_cons (step449 p h) (sat_cons (step3806 p h) (sat_cons (step1690 p h) (sat_cons (step4462 p h) (sat_cons (step4496 p h) (sat_cons (step1117 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c4639 : List Lit := [(1601, true)]
theorem step4639 (p : Nat → Bool) (h : Constraints p) : clause p c4639 = true :=
  Snake9.LocalRup.prove_clause [c4630, c4627, c4633, c4628, c4626, c4593, c4636, c953, c4638, c977, c982, c954, c4330, c936, c903, c933, c934, c894, c895, c1691, c4250, c4305, c4270, c4301, c1889] c4639 (by decide) p (sat_cons (step4630 p h) (sat_cons (step4627 p h) (sat_cons (step4633 p h) (sat_cons (step4628 p h) (sat_cons (step4626 p h) (sat_cons (step4593 p h) (sat_cons (step4636 p h) (sat_cons (step953 p h) (sat_cons (step4638 p h) (sat_cons (step977 p h) (sat_cons (step982 p h) (sat_cons (step954 p h) (sat_cons (step4330 p h) (sat_cons (step936 p h) (sat_cons (step903 p h) (sat_cons (step933 p h) (sat_cons (step934 p h) (sat_cons (step894 p h) (sat_cons (step895 p h) (sat_cons (step1691 p h) (sat_cons (step4250 p h) (sat_cons (step4305 p h) (sat_cons (step4270 p h) (sat_cons (step4301 p h) (sat_cons (step1889 p h) (sat_nil p))))))))))))))))))))))))))
def c4640 : List Lit := [(1546, false)]
theorem step4640 (p : Nat → Bool) (h : Constraints p) : clause p c4640 = true :=
  Snake9.LocalRup.prove_clause [c4639, c4608, c1097] c4640 (by decide) p (sat_cons (step4639 p h) (sat_cons (step4608 p h) (sat_cons (step1097 p h) (sat_nil p))))
def c4641 : List Lit := [(1536, false)]
theorem step4641 (p : Nat → Bool) (h : Constraints p) : clause p c4641 = true :=
  Snake9.LocalRup.prove_clause [c4640, c4630, c977] c4641 (by decide) p (sat_cons (step4640 p h) (sat_cons (step4630 p h) (sat_cons (step977 p h) (sat_nil p))))
def c4642 : List Lit := [(1530, true)]
theorem step4642 (p : Nat → Bool) (h : Constraints p) : clause p c4642 = true :=
  Snake9.LocalRup.prove_clause [c4628, c4639, c4593, c4626, c936, c938, c933, c934, c930, c4635, c83, c1714, c1698, c4318, c344, c4619, c4298] c4642 (by decide) p (sat_cons (step4628 p h) (sat_cons (step4639 p h) (sat_cons (step4593 p h) (sat_cons (step4626 p h) (sat_cons (step936 p h) (sat_cons (step938 p h) (sat_cons (step933 p h) (sat_cons (step934 p h) (sat_cons (step930 p h) (sat_cons (step4635 p h) (sat_cons (step83 p h) (sat_cons (step1714 p h) (sat_cons (step1698 p h) (sat_cons (step4318 p h) (sat_cons (step344 p h) (sat_cons (step4619 p h) (sat_cons (step4298 p h) (sat_nil p))))))))))))))))))
def c4643 : List Lit := [(1535, true)]
theorem step4643 (p : Nat → Bool) (h : Constraints p) : clause p c4643 = true :=
  Snake9.LocalRup.prove_clause [c4642, c4595, c949] c4643 (by decide) p (sat_cons (step4642 p h) (sat_cons (step4595 p h) (sat_cons (step949 p h) (sat_nil p))))
def c4644 : List Lit := [(1524, false)]
theorem step4644 (p : Nat → Bool) (h : Constraints p) : clause p c4644 = true :=
  Snake9.LocalRup.prove_clause [c4642, c4641, c954] c4644 (by decide) p (sat_cons (step4642 p h) (sat_cons (step4641 p h) (sat_cons (step954 p h) (sat_nil p))))
def c4645 : List Lit := [(1545, true)]
theorem step4645 (p : Nat → Bool) (h : Constraints p) : clause p c4645 = true :=
  Snake9.LocalRup.prove_clause [c4643, c4630, c976] c4645 (by decide) p (sat_cons (step4643 p h) (sat_cons (step4630 p h) (sat_cons (step976 p h) (sat_nil p))))
def c4646 : List Lit := [(1517, false)]
theorem step4646 (p : Nat → Bool) (h : Constraints p) : clause p c4646 = true :=
  Snake9.LocalRup.prove_clause [c4643, c4640, c982] c4646 (by decide) p (sat_cons (step4643 p h) (sat_cons (step4640 p h) (sat_cons (step982 p h) (sat_nil p))))
def c4647 : List Lit := [(1522, false)]
theorem step4647 (p : Nat → Bool) (h : Constraints p) : clause p c4647 = true :=
  Snake9.LocalRup.prove_clause [c4644, c926] c4647 (by decide) p (sat_cons (step4644 p h) (sat_cons (step926 p h) (sat_nil p)))
def c4648 : List Lit := [(18, true)]
theorem step4648 (p : Nat → Bool) (h : Constraints p) : clause p c4648 = true :=
  Snake9.LocalRup.prove_clause [c4644, c4594, c928] c4648 (by decide) p (sat_cons (step4644 p h) (sat_cons (step4594 p h) (sat_cons (step928 p h) (sat_nil p))))
def c4649 : List Lit := [(1621, true)]
theorem step4649 (p : Nat → Bool) (h : Constraints p) : clause p c4649 = true :=
  Snake9.LocalRup.prove_clause [c4645, c4639, c1092] c4649 (by decide) p (sat_cons (step4645 p h) (sat_cons (step4639 p h) (sat_cons (step1092 p h) (sat_nil p))))
def c4650 : List Lit := [(1511, false)]
theorem step4650 (p : Nat → Bool) (h : Constraints p) : clause p c4650 = true :=
  Snake9.LocalRup.prove_clause [c4646, c4330] c4650 (by decide) p (sat_cons (step4646 p h) (sat_cons (step4330 p h) (sat_nil p)))
def c4651 : List Lit := [(1754, false)]
theorem step4651 (p : Nat → Bool) (h : Constraints p) : clause p c4651 = true :=
  Snake9.LocalRup.prove_clause [c4649, c1889] c4651 (by decide) p (sat_cons (step4649 p h) (sat_cons (step1889 p h) (sat_nil p)))
def c4652 : List Lit := [(1506, false)]
theorem step4652 (p : Nat → Bool) (h : Constraints p) : clause p c4652 = true :=
  Snake9.LocalRup.prove_clause [c4650, c4627, c903] c4652 (by decide) p (sat_cons (step4650 p h) (sat_cons (step4627 p h) (sat_cons (step903 p h) (sat_nil p))))
def c4653 : List Lit := [(12, true)]
theorem step4653 (p : Nat → Bool) (h : Constraints p) : clause p c4653 = true :=
  Snake9.LocalRup.prove_clause [c4652, c894] c4653 (by decide) p (sat_cons (step4652 p h) (sat_cons (step894 p h) (sat_nil p)))
def c4654 : List Lit := [(9, true)]
theorem step4654 (p : Nat → Bool) (h : Constraints p) : clause p c4654 = true :=
  Snake9.LocalRup.prove_clause [c4652, c895] c4654 (by decide) p (sat_cons (step4652 p h) (sat_cons (step895 p h) (sat_nil p)))
def c4655 : List Lit := [(68, true)]
theorem step4655 (p : Nat → Bool) (h : Constraints p) : clause p c4655 = true :=
  Snake9.LocalRup.prove_clause [c4654, c4626, c1691] c4655 (by decide) p (sat_cons (step4654 p h) (sat_cons (step4626 p h) (sat_cons (step1691 p h) (sat_nil p))))
def c4656 : List Lit := [(69, false)]
theorem step4656 (p : Nat → Bool) (h : Constraints p) : clause p c4656 = true :=
  Snake9.LocalRup.prove_clause [c4655, c4626, c4628, c4653, c4593, c4633, c4250] c4656 (by decide) p (sat_cons (step4655 p h) (sat_cons (step4626 p h) (sat_cons (step4628 p h) (sat_cons (step4653 p h) (sat_cons (step4593 p h) (sat_cons (step4633 p h) (sat_cons (step4250 p h) (sat_nil p))))))))
def c4657 : List Lit := [(31, false)]
theorem step4657 (p : Nat → Bool) (h : Constraints p) : clause p c4657 = true :=
  Snake9.LocalRup.prove_clause [c4656, c4626, c4593, c4644, c4298] c4657 (by decide) p (sat_cons (step4656 p h) (sat_cons (step4626 p h) (sat_cons (step4593 p h) (sat_cons (step4644 p h) (sat_cons (step4298 p h) (sat_nil p))))))
def c4658 : List Lit := []
theorem step4658 (p : Nat → Bool) (h : Constraints p) : clause p c4658 = true :=
  Snake9.LocalRup.prove_clause [c4657, c4656, c4608, c4626, c4651, c4647, c4648, c4653, c4593, c4654, c4272] c4658 (by decide) p (sat_cons (step4657 p h) (sat_cons (step4656 p h) (sat_cons (step4608 p h) (sat_cons (step4626 p h) (sat_cons (step4651 p h) (sat_cons (step4647 p h) (sat_cons (step4648 p h) (sat_cons (step4653 p h) (sat_cons (step4593 p h) (sat_cons (step4654 p h) (sat_cons (step4272 p h) (sat_nil p))))))))))))
end B112E254
