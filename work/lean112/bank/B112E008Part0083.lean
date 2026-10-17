import B112E008Part0082
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6919 : List Lit := [(1577, false), (1567, false), (1606, false)]
theorem step6919 (p : Nat → Bool) (h : Constraints p) : clause p c6919 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3269] c6919 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3269 p h) (sat_nil p)))
def c6920 : List Lit := [(1569, true), (1607, false), (40, true), (33, true)]
theorem step6920 (p : Nat → Bool) (h : Constraints p) : clause p c6920 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3636] c6920 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3636 p h) (sat_nil p)))
def c6921 : List Lit := [(1578, false), (1607, false)]
theorem step6921 (p : Nat → Bool) (h : Constraints p) : clause p c6921 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3789] c6921 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3789 p h) (sat_nil p)))
def c6922 : List Lit := [(1607, false), (1567, false), (1576, false)]
theorem step6922 (p : Nat → Bool) (h : Constraints p) : clause p c6922 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3506] c6922 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3506 p h) (sat_nil p)))
def c6923 : List Lit := [(1607, false), (38, true), (36, false), (1593, false), (60, false), (40, true), (90, false), (1606, false)]
theorem step6923 (p : Nat → Bool) (h : Constraints p) : clause p c6923 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3655] c6923 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3655 p h) (sat_nil p)))
def c6924 : List Lit := [(1607, false), (1577, false), (1566, false)]
theorem step6924 (p : Nat → Bool) (h : Constraints p) : clause p c6924 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3734] c6924 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3734 p h) (sat_nil p)))
def c6925 : List Lit := [(1578, false), (1567, false), (1605, false)]
theorem step6925 (p : Nat → Bool) (h : Constraints p) : clause p c6925 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3943] c6925 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3943 p h) (sat_nil p)))
def c6926 : List Lit := [(1608, false), (1577, false)]
theorem step6926 (p : Nat → Bool) (h : Constraints p) : clause p c6926 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3733] c6926 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3733 p h) (sat_nil p)))
def c6927 : List Lit := [(1608, false), (33, true)]
theorem step6927 (p : Nat → Bool) (h : Constraints p) : clause p c6927 = true :=
  Snake9.LocalRup.prove_clause [c6789, c3766] c6927 (by decide) p (sat_cons (step6789 p h) (sat_cons (step3766 p h) (sat_nil p)))
def c6928 : List Lit := [(43, true), (98, true), (34, false), (104, true), (60, false), (96, true), (112, false), (92, true), (1566, false), (51, true), (1608, true), (103, false)]
theorem step6928 (p : Nat → Bool) (h : Constraints p) : clause p c6928 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5460] c6928 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5460 p h) (sat_nil p)))
def c6929 : List Lit := [(43, true), (19, true), (73, false), (96, true), (97, false), (1512, false), (83, false), (91, true), (108, false), (57, false), (1601, false), (60, false), (90, false), (1590, false), (33, true)]
theorem step6929 (p : Nat → Bool) (h : Constraints p) : clause p c6929 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4535] c6929 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4535 p h) (sat_nil p)))
def c6930 : List Lit := [(57, true), (43, true), (92, true), (34, false), (51, true), (19, true), (1601, false), (73, false), (83, false), (60, false), (1751, true), (112, false), (1512, false), (1576, false), (90, false), (33, true)]
theorem step6930 (p : Nat → Bool) (h : Constraints p) : clause p c6930 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4538] c6930 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4538 p h) (sat_nil p)))
def c6931 : List Lit := [(43, false), (15, false), (1751, true), (1590, false), (112, false), (1601, false), (33, true), (83, false), (60, false), (73, false), (34, false), (100, false), (1512, false)]
theorem step6931 (p : Nat → Bool) (h : Constraints p) : clause p c6931 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4516] c6931 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4516 p h) (sat_nil p)))
def c6932 : List Lit := [(1577, false), (100, false), (1601, false), (33, true), (38, true), (1590, false)]
theorem step6932 (p : Nat → Bool) (h : Constraints p) : clause p c6932 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4592] c6932 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4592 p h) (sat_nil p)))
def c6933 : List Lit := [(1577, false), (1601, true), (38, false), (1605, false), (33, true), (1590, false), (60, false), (112, false)]
theorem step6933 (p : Nat → Bool) (h : Constraints p) : clause p c6933 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4590] c6933 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4590 p h) (sat_nil p)))
def c6934 : List Lit := [(1577, false), (1567, false), (83, false), (55, true), (60, false), (15, false), (112, false)]
theorem step6934 (p : Nat → Bool) (h : Constraints p) : clause p c6934 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4575] c6934 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4575 p h) (sat_nil p)))
def c6935 : List Lit := [(1577, false), (38, false), (33, true), (100, false), (97, false), (90, false), (112, false), (103, false), (60, false), (108, false), (51, true)]
theorem step6935 (p : Nat → Bool) (h : Constraints p) : clause p c6935 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4591] c6935 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4591 p h) (sat_nil p)))
def c6936 : List Lit := [(1593, false), (1607, true), (1751, true), (60, false), (34, false), (1566, false)]
theorem step6936 (p : Nat → Bool) (h : Constraints p) : clause p c6936 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5247] c6936 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5247 p h) (sat_nil p)))
def c6937 : List Lit := [(57, false), (1567, false), (90, false), (96, true), (97, false), (1556, true), (108, false), (1590, false), (60, false), (91, true), (1601, false)]
theorem step6937 (p : Nat → Bool) (h : Constraints p) : clause p c6937 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4531] c6937 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4531 p h) (sat_nil p)))
def c6938 : List Lit := [(1567, false), (56, true), (90, false), (112, false), (96, true), (108, false), (1590, false), (60, false), (1601, false), (91, true), (1556, true), (97, false)]
theorem step6938 (p : Nat → Bool) (h : Constraints p) : clause p c6938 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4632] c6938 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4632 p h) (sat_nil p)))
def c6939 : List Lit := [(19, true), (45, true), (1576, false), (33, true), (83, false), (1514, false), (40, false), (1519, false), (34, false), (90, false), (1589, true), (60, false), (1601, false), (57, true)]
theorem step6939 (p : Nat → Bool) (h : Constraints p) : clause p c6939 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4536] c6939 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4536 p h) (sat_nil p)))
def c6940 : List Lit := [(1601, true), (104, true), (97, false), (105, true), (108, false), (90, false), (117, false), (92, true), (51, true), (33, true), (96, true), (103, false), (100, false), (112, false), (1577, true), (86, true), (42, false), (60, false)]
theorem step6940 (p : Nat → Bool) (h : Constraints p) : clause p c6940 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4588] c6940 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4588 p h) (sat_nil p)))
def c6941 : List Lit := [(43, false), (100, false), (94, true), (83, false), (92, true), (60, false), (1590, false), (117, false), (114, true), (82, false), (124, false), (104, true), (69, false), (96, true), (1674, true), (91, true), (33, true), (119, false), (112, false), (102, false), (1751, true)]
theorem step6941 (p : Nat → Bool) (h : Constraints p) : clause p c6941 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4518] c6941 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4518 p h) (sat_nil p)))
def c6942 : List Lit := [(19, false), (57, true), (1567, false), (114, true), (1601, false), (60, false), (1514, false), (1590, false), (83, false), (96, true), (90, false)]
theorem step6942 (p : Nat → Bool) (h : Constraints p) : clause p c6942 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4544] c6942 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4544 p h) (sat_nil p)))
def c6943 : List Lit := [(19, false), (57, true), (112, false), (1751, true), (60, false), (1601, false), (1512, false), (73, false), (96, true), (90, false), (69, false), (43, true), (33, true), (1590, false), (83, false), (114, true)]
theorem step6943 (p : Nat → Bool) (h : Constraints p) : clause p c6943 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4551] c6943 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4551 p h) (sat_nil p)))
def c6944 : List Lit := [(1564, false), (15, false), (80, false), (60, false), (112, false), (1556, true), (1567, false), (83, false), (73, false), (1576, false), (91, true)]
theorem step6944 (p : Nat → Bool) (h : Constraints p) : clause p c6944 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5456] c6944 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5456 p h) (sat_nil p)))
def c6945 : List Lit := [(1698, false), (1715, false), (105, false), (1760, false), (97, true), (1714, false), (90, false), (1719, true)]
theorem step6945 (p : Nat → Bool) (h : Constraints p) : clause p c6945 = true :=
  Snake9.LocalRup.prove_clause [c6628, c5281] c6945 (by decide) p (sat_cons (step6628 p h) (sat_cons (step5281 p h) (sat_nil p)))
def c6946 : List Lit := [(57, true), (22, false), (1567, false), (1576, false), (19, false), (1555, true), (1596, false), (1514, false), (83, false), (29, false)]
theorem step6946 (p : Nat → Bool) (h : Constraints p) : clause p c6946 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4543] c6946 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4543 p h) (sat_nil p)))
def c6947 : List Lit := [(1567, false), (1601, true), (38, true), (83, false), (60, false), (112, false), (96, true), (90, false)]
theorem step6947 (p : Nat → Bool) (h : Constraints p) : clause p c6947 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4637] c6947 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4637 p h) (sat_nil p)))
def c6948 : List Lit := [(1588, false), (44, true), (40, true), (1600, false), (1594, true), (96, true), (1567, false), (1590, false)]
theorem step6948 (p : Nat → Bool) (h : Constraints p) : clause p c6948 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5270] c6948 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5270 p h) (sat_nil p)))
def c6949 : List Lit := [(57, false), (43, true), (1606, false), (60, false), (34, false), (83, false), (1556, true), (1519, false), (45, false), (1566, false)]
theorem step6949 (p : Nat → Bool) (h : Constraints p) : clause p c6949 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4533] c6949 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4533 p h) (sat_nil p)))
def c6950 : List Lit := [(1601, true), (1567, false), (55, true), (43, true), (1577, true), (112, false), (1525, false), (103, false), (47, false), (96, true), (60, false), (51, true)]
theorem step6950 (p : Nat → Bool) (h : Constraints p) : clause p c6950 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4578] c6950 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4578 p h) (sat_nil p)))
def c6951 : List Lit := [(43, true), (47, false), (51, true), (1566, false), (103, false), (96, true), (112, false), (34, false), (60, false), (1608, true)]
theorem step6951 (p : Nat → Bool) (h : Constraints p) : clause p c6951 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4574] c6951 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4574 p h) (sat_nil p)))
def c6952 : List Lit := [(1521, false), (19, true), (57, false), (1567, false), (1556, true), (1600, false)]
theorem step6952 (p : Nat → Bool) (h : Constraints p) : clause p c6952 = true :=
  Snake9.LocalRup.prove_clause [c6789, c4529] c6952 (by decide) p (sat_cons (step6789 p h) (sat_cons (step4529 p h) (sat_nil p)))
def c6953 : List Lit := [(1761, true), (1665, false), (1682, false), (87, true)]
theorem step6953 (p : Nat → Bool) (h : Constraints p) : clause p c6953 = true :=
  Snake9.LocalRup.prove_clause [c6628, c5547] c6953 (by decide) p (sat_cons (step6628 p h) (sat_cons (step5547 p h) (sat_nil p)))
def c6954 : List Lit := [(43, true), (1593, false), (55, true), (1607, true), (1567, false), (90, false), (112, false), (47, false), (51, true), (83, false), (60, false), (103, false), (96, true)]
theorem step6954 (p : Nat → Bool) (h : Constraints p) : clause p c6954 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5905] c6954 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5905 p h) (sat_nil p)))
def c6955 : List Lit := [(34, false), (90, false), (1601, false), (1566, false), (1607, true), (40, true), (100, false), (103, false), (36, false)]
theorem step6955 (p : Nat → Bool) (h : Constraints p) : clause p c6955 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5946] c6955 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5946 p h) (sat_nil p)))
def c6956 : List Lit := [(1598, false), (100, false), (33, true), (1618, true), (36, false), (96, true), (40, true), (103, false), (90, false)]
theorem step6956 (p : Nat → Bool) (h : Constraints p) : clause p c6956 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5948] c6956 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5948 p h) (sat_nil p)))
def c6957 : List Lit := [(1598, true), (47, false), (90, false), (1582, false), (40, true), (77, false), (100, false), (1618, true), (103, false), (1520, false), (36, false), (97, false), (1590, false), (34, false), (1566, false)]
theorem step6957 (p : Nat → Bool) (h : Constraints p) : clause p c6957 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5951] c6957 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5951 p h) (sat_nil p)))
def c6958 : List Lit := [(1520, false), (40, true), (97, false), (47, false), (34, false), (1653, false), (103, false), (1698, true), (1618, true), (90, false), (36, false), (1582, false), (77, false), (100, false), (1598, true), (1566, false)]
theorem step6958 (p : Nat → Bool) (h : Constraints p) : clause p c6958 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5952] c6958 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5952 p h) (sat_nil p)))
def c6959 : List Lit := [(57, false), (38, true), (60, false), (40, true), (90, false), (1567, false), (36, false)]
theorem step6959 (p : Nat → Bool) (h : Constraints p) : clause p c6959 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5956] c6959 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5956 p h) (sat_nil p)))
def c6960 : List Lit := [(1598, true), (1722, true), (1567, false), (40, true), (90, false), (1698, true), (36, false), (60, false), (33, true)]
theorem step6960 (p : Nat → Bool) (h : Constraints p) : clause p c6960 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5957] c6960 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5957 p h) (sat_nil p)))
def c6961 : List Lit := [(1577, false), (57, false), (1567, false), (36, false), (90, false), (40, false), (60, false)]
theorem step6961 (p : Nat → Bool) (h : Constraints p) : clause p c6961 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5959] c6961 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5959 p h) (sat_nil p)))
def c6962 : List Lit := [(57, false), (39, true), (38, false), (1567, false), (58, true), (90, false), (1600, false), (1582, false), (36, false), (1590, false), (1618, true), (1606, false)]
theorem step6962 (p : Nat → Bool) (h : Constraints p) : clause p c6962 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5961] c6962 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5961 p h) (sat_nil p)))
def c6963 : List Lit := [(57, false), (39, true), (1600, false), (1590, false), (103, false), (1618, true), (38, false), (58, true), (1567, false), (35, false), (90, false), (36, false)]
theorem step6963 (p : Nat → Bool) (h : Constraints p) : clause p c6963 = true :=
  Snake9.LocalRup.prove_clause [c6789, c5962] c6963 (by decide) p (sat_cons (step6789 p h) (sat_cons (step5962 p h) (sat_nil p)))
def c6964 : List Lit := [(1567, false), (1593, false), (1576, false), (83, false), (112, false), (60, false), (15, false)]
theorem step6964 (p : Nat → Bool) (h : Constraints p) : clause p c6964 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6040] c6964 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6040 p h) (sat_nil p)))
def c6965 : List Lit := [(43, true), (19, false), (60, false), (33, true), (1556, true), (1607, true), (1751, true), (112, false), (1590, false), (73, false), (80, false), (83, false), (34, false), (100, false), (91, true)]
theorem step6965 (p : Nat → Bool) (h : Constraints p) : clause p c6965 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6062] c6965 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6062 p h) (sat_nil p)))
def c6966 : List Lit := [(43, true), (15, false), (112, false), (1641, true), (100, false), (1590, false), (91, true), (1576, false), (33, true), (80, false), (83, false), (1617, false), (96, true), (73, false), (1751, true), (60, false)]
theorem step6966 (p : Nat → Bool) (h : Constraints p) : clause p c6966 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6065] c6966 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6065 p h) (sat_nil p)))
def c6967 : List Lit := [(1617, true), (43, true), (60, false), (112, false), (33, true), (1751, true), (34, false), (100, false), (1590, false), (96, true)]
theorem step6967 (p : Nat → Bool) (h : Constraints p) : clause p c6967 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6067] c6967 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6067 p h) (sat_nil p)))
def c6968 : List Lit := [(1723, false), (1710, false), (1750, false), (1680, false), (87, true)]
theorem step6968 (p : Nat → Bool) (h : Constraints p) : clause p c6968 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6176] c6968 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6176 p h) (sat_nil p)))
def c6969 : List Lit := [(1607, false), (1593, false), (33, true), (89, false), (97, false), (34, false), (60, false)]
theorem step6969 (p : Nat → Bool) (h : Constraints p) : clause p c6969 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6309] c6969 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6309 p h) (sat_nil p)))
def c6970 : List Lit := [(19, true), (33, false), (1653, false), (1564, false), (1682, false), (1616, false), (87, true)]
theorem step6970 (p : Nat → Bool) (h : Constraints p) : clause p c6970 = true :=
  Snake9.LocalRup.prove_clause [c6628, c6311] c6970 (by decide) p (sat_cons (step6628 p h) (sat_cons (step6311 p h) (sat_nil p)))
def c6971 : List Lit := [(1745, false), (110, true), (1715, false), (77, false), (105, true), (1710, false), (1737, false), (99, true)]
theorem step6971 (p : Nat → Bool) (h : Constraints p) : clause p c6971 = true :=
  Snake9.LocalRup.prove_clause [c6630, c6393] c6971 (by decide) p (sat_cons (step6630 p h) (sat_cons (step6393 p h) (sat_nil p)))
def c6972 : List Lit := [(19, true), (6, true), (1566, false), (1606, false), (1577, false), (1616, false)]
theorem step6972 (p : Nat → Bool) (h : Constraints p) : clause p c6972 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6699] c6972 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6699 p h) (sat_nil p)))
def c6973 : List Lit := [(1593, false), (1596, false), (57, true), (1, false), (33, false), (1556, true), (71, false), (87, true), (74, false)]
theorem step6973 (p : Nat → Bool) (h : Constraints p) : clause p c6973 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6728] c6973 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6728 p h) (sat_nil p)))
def c6974 : List Lit := [(29, false), (54, true), (1576, false), (97, false), (1, false), (60, false), (1601, false), (89, false), (33, true), (1641, true), (1593, false), (1556, true)]
theorem step6974 (p : Nat → Bool) (h : Constraints p) : clause p c6974 = true :=
  Snake9.LocalRup.prove_clause [c6790, c6738] c6974 (by decide) p (sat_cons (step6790 p h) (sat_cons (step6738 p h) (sat_nil p)))
def c6975 : List Lit := [(1577, false), (34, true), (36, false), (90, false), (1680, false), (1697, true), (1582, false), (40, true), (87, true)]
theorem step6975 (p : Nat → Bool) (h : Constraints p) : clause p c6975 = true :=
  Snake9.LocalRup.prove_clause [c6789, c6756] c6975 (by decide) p (sat_cons (step6789 p h) (sat_cons (step6756 p h) (sat_nil p)))
def c6976 : List Lit := [(1601, false), (97, false), (89, false), (1514, false), (1569, false), (1564, false), (33, true), (1618, true), (1, false), (91, true), (87, true)]
theorem step6976 (p : Nat → Bool) (h : Constraints p) : clause p c6976 = true :=
  Snake9.LocalRup.prove_clause [c1793, c1232, c2004, c2003, c1205, c1237, c1180, c2496, c1161, c1157, c6896, c1128, c554, c1697, c1123, c5939, c2079, c4823, c1395, c1195, c1869, c1868, c6863, c6834, c1178, c1170, c4794, c1185, c2966, c363] c6976 (by decide) p (sat_cons (step1793 p h) (sat_cons (step1232 p h) (sat_cons (step2004 p h) (sat_cons (step2003 p h) (sat_cons (step1205 p h) (sat_cons (step1237 p h) (sat_cons (step1180 p h) (sat_cons (step2496 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step6896 p h) (sat_cons (step1128 p h) (sat_cons (step554 p h) (sat_cons (step1697 p h) (sat_cons (step1123 p h) (sat_cons (step5939 p h) (sat_cons (step2079 p h) (sat_cons (step4823 p h) (sat_cons (step1395 p h) (sat_cons (step1195 p h) (sat_cons (step1869 p h) (sat_cons (step1868 p h) (sat_cons (step6863 p h) (sat_cons (step6834 p h) (sat_cons (step1178 p h) (sat_cons (step1170 p h) (sat_cons (step4794 p h) (sat_cons (step1185 p h) (sat_cons (step2966 p h) (sat_cons (step363 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c6977 : List Lit := [(1583, true), (1576, false), (1601, true), (97, false), (89, false), (1569, false), (1564, false), (33, true)]
theorem step6977 (p : Nat → Bool) (h : Constraints p) : clause p c6977 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1157, c1128, c6221, c1123] c6977 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1128 p h) (sat_cons (step6221 p h) (sat_cons (step1123 p h) (sat_nil p))))))
def c6978 : List Lit := [(60, true), (110, true), (34, true), (1722, false), (97, false), (33, true), (71, false), (87, true)]
theorem step6978 (p : Nat → Bool) (h : Constraints p) : clause p c6978 = true :=
  Snake9.LocalRup.prove_clause [c6875, c5927] c6978 (by decide) p (sat_cons (step6875 p h) (sat_cons (step5927 p h) (sat_nil p)))
def c6979 : List Lit := [(34, true), (39, false), (88, false), (100, true), (1601, true), (97, false), (86, true), (1564, false), (33, true), (1618, true), (71, false), (87, true)]
theorem step6979 (p : Nat → Bool) (h : Constraints p) : clause p c6979 = true :=
  Snake9.LocalRup.prove_clause [c5423, c1397, c1395, c1403, c1123, c511, c1128, c939, c940, c944, c945, c948, c2000, c1003, c1000, c983, c978, c975, c2302, c6978, c1662, c2161, c2002, c4638, c1241, c1162] c6979 (by decide) p (sat_cons (step5423 p h) (sat_cons (step1397 p h) (sat_cons (step1395 p h) (sat_cons (step1403 p h) (sat_cons (step1123 p h) (sat_cons (step511 p h) (sat_cons (step1128 p h) (sat_cons (step939 p h) (sat_cons (step940 p h) (sat_cons (step944 p h) (sat_cons (step945 p h) (sat_cons (step948 p h) (sat_cons (step2000 p h) (sat_cons (step1003 p h) (sat_cons (step1000 p h) (sat_cons (step983 p h) (sat_cons (step978 p h) (sat_cons (step975 p h) (sat_cons (step2302 p h) (sat_cons (step6978 p h) (sat_cons (step1662 p h) (sat_cons (step2161 p h) (sat_cons (step2002 p h) (sat_cons (step4638 p h) (sat_cons (step1241 p h) (sat_cons (step1162 p h) (sat_nil p)))))))))))))))))))))))))))
def c6980 : List Lit := [(39, false), (88, false), (100, true), (1601, true), (97, false), (89, false), (1564, false), (33, true), (1618, true), (71, false), (1566, false), (87, true)]
theorem step6980 (p : Nat → Bool) (h : Constraints p) : clause p c6980 = true :=
  Snake9.LocalRup.prove_clause [c6838, c6979, c6221, c178, c6714] c6980 (by decide) p (sat_cons (step6838 p h) (sat_cons (step6979 p h) (sat_cons (step6221 p h) (sat_cons (step178 p h) (sat_cons (step6714 p h) (sat_nil p))))))
def c6981 : List Lit := [(40, false), (39, true), (93, true), (1601, true)]
theorem step6981 (p : Nat → Bool) (h : Constraints p) : clause p c6981 = true :=
  Snake9.LocalRup.prove_clause [c4363, c1868] c6981 (by decide) p (sat_cons (step4363 p h) (sat_cons (step1868 p h) (sat_nil p)))
def c6982 : List Lit := [(60, true), (40, true), (54, false), (96, true), (1722, false), (1593, true), (89, false), (1578, true), (105, true), (91, true), (34, false), (97, false), (87, true)]
theorem step6982 (p : Nat → Bool) (h : Constraints p) : clause p c6982 = true :=
  Snake9.LocalRup.prove_clause [c6837, c1332, c2162, c1458, c5984, c6898, c2022, c1348, c6115, c1340, c1369, c2018, c1674, c1397, c1400, c2171, c2014, c1292, c2017, c6635, c6722, c6897, c1341, c1344, c1494, c1485, c6841, c1335, c1424, c4451, c1326, c6727, c1490, c6122, c6746, c2168, c1420] c6982 (by decide) p (sat_cons (step6837 p h) (sat_cons (step1332 p h) (sat_cons (step2162 p h) (sat_cons (step1458 p h) (sat_cons (step5984 p h) (sat_cons (step6898 p h) (sat_cons (step2022 p h) (sat_cons (step1348 p h) (sat_cons (step6115 p h) (sat_cons (step1340 p h) (sat_cons (step1369 p h) (sat_cons (step2018 p h) (sat_cons (step1674 p h) (sat_cons (step1397 p h) (sat_cons (step1400 p h) (sat_cons (step2171 p h) (sat_cons (step2014 p h) (sat_cons (step1292 p h) (sat_cons (step2017 p h) (sat_cons (step6635 p h) (sat_cons (step6722 p h) (sat_cons (step6897 p h) (sat_cons (step1341 p h) (sat_cons (step1344 p h) (sat_cons (step1494 p h) (sat_cons (step1485 p h) (sat_cons (step6841 p h) (sat_cons (step1335 p h) (sat_cons (step1424 p h) (sat_cons (step4451 p h) (sat_cons (step1326 p h) (sat_cons (step6727 p h) (sat_cons (step1490 p h) (sat_cons (step6122 p h) (sat_cons (step6746 p h) (sat_cons (step2168 p h) (sat_cons (step1420 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
end B112E008
