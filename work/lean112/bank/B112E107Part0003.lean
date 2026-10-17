import B112E107Part0002
namespace B112E107
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c948 : List Lit := [(1459, false), (1466, true)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true :=
  Snake9.LocalRup.prove_clause [c767, c620, c611, c852, c624, c614, c364, c600, c606, c365, c881, c368, c354, c360, c358] c948 (by decide) p (sat_cons (step767 p h) (sat_cons (step620 p h) (sat_cons (step611 p h) (sat_cons (step852 p h) (sat_cons (step624 p h) (sat_cons (step614 p h) (sat_cons (step364 p h) (sat_cons (step600 p h) (sat_cons (step606 p h) (sat_cons (step365 p h) (sat_cons (step881 p h) (sat_cons (step368 p h) (sat_cons (step354 p h) (sat_cons (step360 p h) (sat_cons (step358 p h) (sat_nil p))))))))))))))))
def c949 : List Lit := [(1465, false), (1337, false), (1438, false)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true :=
  Snake9.LocalRup.prove_clause [c824, c826, c743, c591, c638, c946, c697, c702, c719, c740, c947, c639, c643, c948, c940] c949 (by decide) p (sat_cons (step824 p h) (sat_cons (step826 p h) (sat_cons (step743 p h) (sat_cons (step591 p h) (sat_cons (step638 p h) (sat_cons (step946 p h) (sat_cons (step697 p h) (sat_cons (step702 p h) (sat_cons (step719 p h) (sat_cons (step740 p h) (sat_cons (step947 p h) (sat_cons (step639 p h) (sat_cons (step643 p h) (sat_cons (step948 p h) (sat_cons (step940 p h) (sat_nil p))))))))))))))))
def c950 : List Lit := [(1465, true)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true :=
  Snake9.LocalRup.prove_clause [c767, c619, c623, c807, c613, c600, c364, c606, c881, c365, c354, c368, c358, c360] c950 (by decide) p (sat_cons (step767 p h) (sat_cons (step619 p h) (sat_cons (step623 p h) (sat_cons (step807 p h) (sat_cons (step613 p h) (sat_cons (step600 p h) (sat_cons (step364 p h) (sat_cons (step606 p h) (sat_cons (step881 p h) (sat_cons (step365 p h) (sat_cons (step354 p h) (sat_cons (step368 p h) (sat_cons (step358 p h) (sat_cons (step360 p h) (sat_nil p)))))))))))))))
def c951 : List Lit := [(75, false), (1452, true), (76, false)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true :=
  Snake9.LocalRup.prove_clause [c785, c598, c597, c881, c155, c174, c354, c165, c359, c355] c951 (by decide) p (sat_cons (step785 p h) (sat_cons (step598 p h) (sat_cons (step597 p h) (sat_cons (step881 p h) (sat_cons (step155 p h) (sat_cons (step174 p h) (sat_cons (step354 p h) (sat_cons (step165 p h) (sat_cons (step359 p h) (sat_cons (step355 p h) (sat_nil p)))))))))))
def c952 : List Lit := [(1472, true)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true :=
  Snake9.LocalRup.prove_clause [c950, c633] c952 (by decide) p (sat_cons (step950 p h) (sat_cons (step633 p h) (sat_nil p)))
def c953 : List Lit := [(1367, false)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true :=
  Snake9.LocalRup.prove_clause [c952, c943] c953 (by decide) p (sat_cons (step952 p h) (sat_cons (step943 p h) (sat_nil p)))
def c954 : List Lit := [(1, false), (43, true)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true :=
  Snake9.LocalRup.prove_clause [c223, c1] c954 (by decide) p (sat_cons (step223 p h) (sat_cons (step1 p h) (sat_nil p)))
def c955 : List Lit := [(3, false), (49, true)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true :=
  Snake9.LocalRup.prove_clause [c225, c3] c955 (by decide) p (sat_cons (step225 p h) (sat_cons (step3 p h) (sat_nil p)))
def c956 : List Lit := [(4, false), (3, true), (114, true)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true :=
  Snake9.LocalRup.prove_clause [c756, c757, c6] c956 (by decide) p (sat_cons (step756 p h) (sat_cons (step757 p h) (sat_cons (step6 p h) (sat_nil p))))
def c957 : List Lit := [(53, true), (1, true), (6, false), (116, true)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true :=
  Snake9.LocalRup.prove_clause [c758, c9] c957 (by decide) p (sat_cons (step758 p h) (sat_cons (step9 p h) (sat_nil p)))
def c958 : List Lit := [(12, false), (11, true), (60, true)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true :=
  Snake9.LocalRup.prove_clause [c229, c25] c958 (by decide) p (sat_cons (step229 p h) (sat_cons (step25 p h) (sat_nil p)))
def c959 : List Lit := [(4, true), (12, false), (60, true)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true :=
  Snake9.LocalRup.prove_clause [c229, c26] c959 (by decide) p (sat_cons (step229 p h) (sat_cons (step26 p h) (sat_nil p)))
def c960 : List Lit := [(15, false), (79, false)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true :=
  Snake9.LocalRup.prove_clause [c31, c30] c960 (by decide) p (sat_cons (step31 p h) (sat_cons (step30 p h) (sat_nil p)))
def c961 : List Lit := [(19, false), (15, true)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true :=
  Snake9.LocalRup.prove_clause [c232, c38] c961 (by decide) p (sat_cons (step232 p h) (sat_cons (step38 p h) (sat_nil p)))
def c962 : List Lit := [(27, false), (31, true)]
theorem step962 (p : Nat → Bool) (h : Constraints p) : clause p c962 = true :=
  Snake9.LocalRup.prove_clause [c235, c54] c962 (by decide) p (sat_cons (step235 p h) (sat_cons (step54 p h) (sat_nil p)))
def c963 : List Lit := [(27, false), (28, true)]
theorem step963 (p : Nat → Bool) (h : Constraints p) : clause p c963 = true :=
  Snake9.LocalRup.prove_clause [c235, c55] c963 (by decide) p (sat_cons (step235 p h) (sat_cons (step55 p h) (sat_nil p)))
def c964 : List Lit := [(53, false), (54, true), (43, true)]
theorem step964 (p : Nat → Bool) (h : Constraints p) : clause p c964 = true :=
  Snake9.LocalRup.prove_clause [c237, c91] c964 (by decide) p (sat_cons (step237 p h) (sat_cons (step91 p h) (sat_nil p)))
def c965 : List Lit := [(55, false), (54, true), (60, true)]
theorem step965 (p : Nat → Bool) (h : Constraints p) : clause p c965 = true :=
  Snake9.LocalRup.prove_clause [c238, c97] c965 (by decide) p (sat_cons (step238 p h) (sat_cons (step97 p h) (sat_nil p)))
def c966 : List Lit := [(57, false), (49, true), (60, true)]
theorem step966 (p : Nat → Bool) (h : Constraints p) : clause p c966 = true :=
  Snake9.LocalRup.prove_clause [c239, c103] c966 (by decide) p (sat_cons (step239 p h) (sat_cons (step103 p h) (sat_nil p)))
def c967 : List Lit := [(57, false), (49, true), (59, true)]
theorem step967 (p : Nat → Bool) (h : Constraints p) : clause p c967 = true :=
  Snake9.LocalRup.prove_clause [c239, c104] c967 (by decide) p (sat_cons (step239 p h) (sat_cons (step104 p h) (sat_nil p)))
def c968 : List Lit := [(61, false), (59, true), (60, true)]
theorem step968 (p : Nat → Bool) (h : Constraints p) : clause p c968 = true :=
  Snake9.LocalRup.prove_clause [c240, c117] c968 (by decide) p (sat_cons (step240 p h) (sat_cons (step117 p h) (sat_nil p)))
def c969 : List Lit := [(62, false), (43, true), (67, true)]
theorem step969 (p : Nat → Bool) (h : Constraints p) : clause p c969 = true :=
  Snake9.LocalRup.prove_clause [c241, c119] c969 (by decide) p (sat_cons (step241 p h) (sat_cons (step119 p h) (sat_nil p)))
def c970 : List Lit := [(68, false), (49, true), (63, true), (67, true)]
theorem step970 (p : Nat → Bool) (h : Constraints p) : clause p c970 = true :=
  Snake9.LocalRup.prove_clause [c242, c143] c970 (by decide) p (sat_cons (step242 p h) (sat_cons (step143 p h) (sat_nil p)))
def c971 : List Lit := [(70, false), (66, true)]
theorem step971 (p : Nat → Bool) (h : Constraints p) : clause p c971 = true :=
  Snake9.LocalRup.prove_clause [c243, c152] c971 (by decide) p (sat_cons (step243 p h) (sat_cons (step152 p h) (sat_nil p)))
def c972 : List Lit := [(71, false), (73, true)]
theorem step972 (p : Nat → Bool) (h : Constraints p) : clause p c972 = true :=
  Snake9.LocalRup.prove_clause [c244, c153] c972 (by decide) p (sat_cons (step244 p h) (sat_cons (step153 p h) (sat_nil p)))
def c973 : List Lit := [(71, false), (63, true)]
theorem step973 (p : Nat → Bool) (h : Constraints p) : clause p c973 = true :=
  Snake9.LocalRup.prove_clause [c244, c154] c973 (by decide) p (sat_cons (step244 p h) (sat_cons (step154 p h) (sat_nil p)))
def c974 : List Lit := [(60, true), (76, true), (77, false)]
theorem step974 (p : Nat → Bool) (h : Constraints p) : clause p c974 = true :=
  Snake9.LocalRup.prove_clause [c245, c172] c974 (by decide) p (sat_cons (step245 p h) (sat_cons (step172 p h) (sat_nil p)))
def c975 : List Lit := [(60, true), (69, true), (77, false)]
theorem step975 (p : Nat → Bool) (h : Constraints p) : clause p c975 = true :=
  Snake9.LocalRup.prove_clause [c245, c173] c975 (by decide) p (sat_cons (step245 p h) (sat_cons (step173 p h) (sat_nil p)))
def c976 : List Lit := [(78, false), (75, true), (76, true)]
theorem step976 (p : Nat → Bool) (h : Constraints p) : clause p c976 = true :=
  Snake9.LocalRup.prove_clause [c246, c175] c976 (by decide) p (sat_cons (step246 p h) (sat_cons (step175 p h) (sat_nil p)))
def c977 : List Lit := [(80, false), (82, true), (79, true)]
theorem step977 (p : Nat → Bool) (h : Constraints p) : clause p c977 = true :=
  Snake9.LocalRup.prove_clause [c247, c176] c977 (by decide) p (sat_cons (step247 p h) (sat_cons (step176 p h) (sat_nil p)))
def c978 : List Lit := [(89, false), (90, true), (94, true)]
theorem step978 (p : Nat → Bool) (h : Constraints p) : clause p c978 = true :=
  Snake9.LocalRup.prove_clause [c248, c196] c978 (by decide) p (sat_cons (step248 p h) (sat_cons (step196 p h) (sat_nil p)))
def c979 : List Lit := [(89, false), (88, true), (94, true)]
theorem step979 (p : Nat → Bool) (h : Constraints p) : clause p c979 = true :=
  Snake9.LocalRup.prove_clause [c248, c197] c979 (by decide) p (sat_cons (step248 p h) (sat_cons (step197 p h) (sat_nil p)))
def c980 : List Lit := [(95, false), (93, true), (94, true)]
theorem step980 (p : Nat → Bool) (h : Constraints p) : clause p c980 = true :=
  Snake9.LocalRup.prove_clause [c249, c203] c980 (by decide) p (sat_cons (step249 p h) (sat_cons (step203 p h) (sat_nil p)))
def c981 : List Lit := [(100, false), (97, true)]
theorem step981 (p : Nat → Bool) (h : Constraints p) : clause p c981 = true :=
  Snake9.LocalRup.prove_clause [c250, c212] c981 (by decide) p (sat_cons (step250 p h) (sat_cons (step212 p h) (sat_nil p)))
def c982 : List Lit := [(243, false), (269, false)]
theorem step982 (p : Nat → Bool) (h : Constraints p) : clause p c982 = true :=
  Snake9.LocalRup.prove_clause [c764, c292] c982 (by decide) p (sat_cons (step764 p h) (sat_cons (step292 p h) (sat_nil p)))
def c983 : List Lit := [(311, false), (317, false)]
theorem step983 (p : Nat → Bool) (h : Constraints p) : clause p c983 = true :=
  Snake9.LocalRup.prove_clause [c779, c318] c983 (by decide) p (sat_cons (step779 p h) (sat_cons (step318 p h) (sat_nil p)))
def c984 : List Lit := [(295, false), (321, false)]
theorem step984 (p : Nat → Bool) (h : Constraints p) : clause p c984 = true :=
  Snake9.LocalRup.prove_clause [c763, c325] c984 (by decide) p (sat_cons (step763 p h) (sat_cons (step325 p h) (sat_nil p)))
def c985 : List Lit := [(271, false), (323, false)]
theorem step985 (p : Nat → Bool) (h : Constraints p) : clause p c985 = true :=
  Snake9.LocalRup.prove_clause [c760, c330] c985 (by decide) p (sat_cons (step760 p h) (sat_cons (step330 p h) (sat_nil p)))
def c986 : List Lit := [(341, false), (343, false)]
theorem step986 (p : Nat → Bool) (h : Constraints p) : clause p c986 = true :=
  Snake9.LocalRup.prove_clause [c786, c343] c986 (by decide) p (sat_cons (step786 p h) (sat_cons (step343 p h) (sat_nil p)))
def c987 : List Lit := [(339, false), (345, false)]
theorem step987 (p : Nat → Bool) (h : Constraints p) : clause p c987 = true :=
  Snake9.LocalRup.prove_clause [c777, c347] c987 (by decide) p (sat_cons (step777 p h) (sat_cons (step347 p h) (sat_nil p)))
def c988 : List Lit := [(335, false), (347, false)]
theorem step988 (p : Nat → Bool) (h : Constraints p) : clause p c988 = true :=
  Snake9.LocalRup.prove_clause [c768, c351] c988 (by decide) p (sat_cons (step768 p h) (sat_cons (step351 p h) (sat_nil p)))
def c989 : List Lit := [(355, false), (357, false)]
theorem step989 (p : Nat → Bool) (h : Constraints p) : clause p c989 = true :=
  Snake9.LocalRup.prove_clause [c785, c359] c989 (by decide) p (sat_cons (step785 p h) (sat_cons (step359 p h) (sat_nil p)))
def c990 : List Lit := [(353, false), (359, false)]
theorem step990 (p : Nat → Bool) (h : Constraints p) : clause p c990 = true :=
  Snake9.LocalRup.prove_clause [c776, c363] c990 (by decide) p (sat_cons (step776 p h) (sat_cons (step363 p h) (sat_nil p)))
def c991 : List Lit := [(361, false), (373, false)]
theorem step991 (p : Nat → Bool) (h : Constraints p) : clause p c991 = true :=
  Snake9.LocalRup.prove_clause [c767, c368] c991 (by decide) p (sat_cons (step767 p h) (sat_cons (step368 p h) (sat_nil p)))
def c992 : List Lit := [(349, false), (375, false)]
theorem step992 (p : Nat → Bool) (h : Constraints p) : clause p c992 = true :=
  Snake9.LocalRup.prove_clause [c762, c373] c992 (by decide) p (sat_cons (step762 p h) (sat_cons (step373 p h) (sat_nil p)))
def c993 : List Lit := [(389, false), (401, false)]
theorem step993 (p : Nat → Bool) (h : Constraints p) : clause p c993 = true :=
  Snake9.LocalRup.prove_clause [c766, c391] c993 (by decide) p (sat_cons (step766 p h) (sat_cons (step391 p h) (sat_nil p)))
def c994 : List Lit := [(377, false), (431, false)]
theorem step994 (p : Nat → Bool) (h : Constraints p) : clause p c994 = true :=
  Snake9.LocalRup.prove_clause [c759, c420] c994 (by decide) p (sat_cons (step759 p h) (sat_cons (step420 p h) (sat_nil p)))
def c995 : List Lit := [(325, false), (433, false)]
theorem step995 (p : Nat → Bool) (h : Constraints p) : clause p c995 = true :=
  Snake9.LocalRup.prove_clause [c425, c423] c995 (by decide) p (sat_cons (step425 p h) (sat_cons (step423 p h) (sat_nil p)))
def c996 : List Lit := [(1355, false), (1363, true)]
theorem step996 (p : Nat → Bool) (h : Constraints p) : clause p c996 = true :=
  Snake9.LocalRup.prove_clause [c790, c486] c996 (by decide) p (sat_cons (step790 p h) (sat_cons (step486 p h) (sat_nil p)))
def c997 : List Lit := [(1357, false), (1365, true)]
theorem step997 (p : Nat → Bool) (h : Constraints p) : clause p c997 = true :=
  Snake9.LocalRup.prove_clause [c790, c487] c997 (by decide) p (sat_cons (step790 p h) (sat_cons (step487 p h) (sat_nil p)))
def c998 : List Lit := [(1363, true), (1336, false)]
theorem step998 (p : Nat → Bool) (h : Constraints p) : clause p c998 = true :=
  Snake9.LocalRup.prove_clause [c792, c488] c998 (by decide) p (sat_cons (step792 p h) (sat_cons (step488 p h) (sat_nil p)))
def c999 : List Lit := [(1364, true), (1337, false)]
theorem step999 (p : Nat → Bool) (h : Constraints p) : clause p c999 = true :=
  Snake9.LocalRup.prove_clause [c792, c492] c999 (by decide) p (sat_cons (step792 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1000 : List Lit := [(1357, false), (1337, false)]
theorem step1000 (p : Nat → Bool) (h : Constraints p) : clause p c1000 = true :=
  Snake9.LocalRup.prove_clause [c953, c495] c1000 (by decide) p (sat_cons (step953 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1001 : List Lit := [(1365, true), (1338, false)]
theorem step1001 (p : Nat → Bool) (h : Constraints p) : clause p c1001 = true :=
  Snake9.LocalRup.prove_clause [c792, c496] c1001 (by decide) p (sat_cons (step792 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1002 : List Lit := [(1376, false), (1385, true)]
theorem step1002 (p : Nat → Bool) (h : Constraints p) : clause p c1002 = true :=
  Snake9.LocalRup.prove_clause [c797, c509] c1002 (by decide) p (sat_cons (step797 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1003 : List Lit := [(1377, false), (1386, true)]
theorem step1003 (p : Nat → Bool) (h : Constraints p) : clause p c1003 = true :=
  Snake9.LocalRup.prove_clause [c797, c510] c1003 (by decide) p (sat_cons (step797 p h) (sat_cons (step510 p h) (sat_nil p)))
def c1004 : List Lit := [(1404, false), (1412, true)]
theorem step1004 (p : Nat → Bool) (h : Constraints p) : clause p c1004 = true :=
  Snake9.LocalRup.prove_clause [c798, c547] c1004 (by decide) p (sat_cons (step798 p h) (sat_cons (step547 p h) (sat_nil p)))
def c1005 : List Lit := [(1405, false), (1413, true)]
theorem step1005 (p : Nat → Bool) (h : Constraints p) : clause p c1005 = true :=
  Snake9.LocalRup.prove_clause [c798, c548] c1005 (by decide) p (sat_cons (step798 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1006 : List Lit := [(1406, false), (1414, true)]
theorem step1006 (p : Nat → Bool) (h : Constraints p) : clause p c1006 = true :=
  Snake9.LocalRup.prove_clause [c798, c549] c1006 (by decide) p (sat_cons (step798 p h) (sat_cons (step549 p h) (sat_nil p)))
def c1007 : List Lit := [(1385, false), (1412, true)]
theorem step1007 (p : Nat → Bool) (h : Constraints p) : clause p c1007 = true :=
  Snake9.LocalRup.prove_clause [c794, c550] c1007 (by decide) p (sat_cons (step794 p h) (sat_cons (step550 p h) (sat_nil p)))
def c1008 : List Lit := [(1386, false), (1413, true)]
theorem step1008 (p : Nat → Bool) (h : Constraints p) : clause p c1008 = true :=
  Snake9.LocalRup.prove_clause [c794, c553] c1008 (by decide) p (sat_cons (step794 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1009 : List Lit := [(1413, false), (1427, true)]
theorem step1009 (p : Nat → Bool) (h : Constraints p) : clause p c1009 = true :=
  Snake9.LocalRup.prove_clause [c791, c555] c1009 (by decide) p (sat_cons (step791 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1010 : List Lit := [(1412, false), (1427, true)]
theorem step1010 (p : Nat → Bool) (h : Constraints p) : clause p c1010 = true :=
  Snake9.LocalRup.prove_clause [c793, c557] c1010 (by decide) p (sat_cons (step793 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1011 : List Lit := [(1413, false), (1428, true)]
theorem step1011 (p : Nat → Bool) (h : Constraints p) : clause p c1011 = true :=
  Snake9.LocalRup.prove_clause [c793, c558] c1011 (by decide) p (sat_cons (step793 p h) (sat_cons (step558 p h) (sat_nil p)))
end B112E107
