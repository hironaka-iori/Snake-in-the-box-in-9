import B112E058Part0003
namespace B112E058
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c939 : List Lit := [(77, false), (78, true)]
theorem step939 (p : Nat → Bool) (h : Constraints p) : clause p c939 = true :=
  Snake9.LocalRup.prove_clause [c285, c202] c939 (by decide) p (sat_cons (step285 p h) (sat_cons (step202 p h) (sat_nil p)))
def c940 : List Lit := [(77, false), (65, true)]
theorem step940 (p : Nat → Bool) (h : Constraints p) : clause p c940 = true :=
  Snake9.LocalRup.prove_clause [c285, c203] c940 (by decide) p (sat_cons (step285 p h) (sat_cons (step203 p h) (sat_nil p)))
def c941 : List Lit := [(78, true), (83, true), (79, false), (68, true)]
theorem step941 (p : Nat → Bool) (h : Constraints p) : clause p c941 = true :=
  Snake9.LocalRup.prove_clause [c286, c210] c941 (by decide) p (sat_cons (step286 p h) (sat_cons (step210 p h) (sat_nil p)))
def c942 : List Lit := [(83, true), (68, true), (79, false), (76, true)]
theorem step942 (p : Nat → Bool) (h : Constraints p) : clause p c942 = true :=
  Snake9.LocalRup.prove_clause [c286, c211] c942 (by decide) p (sat_cons (step286 p h) (sat_cons (step211 p h) (sat_nil p)))
def c943 : List Lit := [(78, true), (68, true), (79, false), (76, true)]
theorem step943 (p : Nat → Bool) (h : Constraints p) : clause p c943 = true :=
  Snake9.LocalRup.prove_clause [c286, c212] c943 (by decide) p (sat_cons (step286 p h) (sat_cons (step212 p h) (sat_nil p)))
def c944 : List Lit := [(80, true), (83, true), (82, false), (76, true), (81, true)]
theorem step944 (p : Nat → Bool) (h : Constraints p) : clause p c944 = true :=
  Snake9.LocalRup.prove_clause [c287, c215] c944 (by decide) p (sat_cons (step287 p h) (sat_cons (step215 p h) (sat_nil p)))
def c945 : List Lit := [(81, true), (71, true), (82, false), (83, true), (76, true)]
theorem step945 (p : Nat → Bool) (h : Constraints p) : clause p c945 = true :=
  Snake9.LocalRup.prove_clause [c287, c216] c945 (by decide) p (sat_cons (step287 p h) (sat_cons (step216 p h) (sat_nil p)))
def c946 : List Lit := [(71, true), (80, true), (82, false), (76, true), (81, true)]
theorem step946 (p : Nat → Bool) (h : Constraints p) : clause p c946 = true :=
  Snake9.LocalRup.prove_clause [c287, c217] c946 (by decide) p (sat_cons (step287 p h) (sat_cons (step217 p h) (sat_nil p)))
def c947 : List Lit := [(87, false), (86, true)]
theorem step947 (p : Nat → Bool) (h : Constraints p) : clause p c947 = true :=
  Snake9.LocalRup.prove_clause [c288, c219] c947 (by decide) p (sat_cons (step288 p h) (sat_cons (step219 p h) (sat_nil p)))
def c948 : List Lit := [(63, true), (100, true), (101, false), (105, true)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true :=
  Snake9.LocalRup.prove_clause [c290, c228] c948 (by decide) p (sat_cons (step290 p h) (sat_cons (step228 p h) (sat_nil p)))
def c949 : List Lit := [(100, true), (69, true), (104, false), (105, true)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true :=
  Snake9.LocalRup.prove_clause [c292, c231] c949 (by decide) p (sat_cons (step292 p h) (sat_cons (step231 p h) (sat_nil p)))
def c950 : List Lit := [(100, true), (104, false), (105, true), (32, true)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true :=
  Snake9.LocalRup.prove_clause [c292, c232] c950 (by decide) p (sat_cons (step292 p h) (sat_cons (step232 p h) (sat_nil p)))
def c951 : List Lit := [(69, true), (104, false), (105, true), (32, true)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true :=
  Snake9.LocalRup.prove_clause [c292, c233] c951 (by decide) p (sat_cons (step292 p h) (sat_cons (step233 p h) (sat_nil p)))
def c952 : List Lit := [(108, true), (106, false), (71, true)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true :=
  Snake9.LocalRup.prove_clause [c293, c245] c952 (by decide) p (sat_cons (step293 p h) (sat_cons (step245 p h) (sat_nil p)))
def c953 : List Lit := [(115, true), (107, false), (105, true)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true :=
  Snake9.LocalRup.prove_clause [c294, c247] c953 (by decide) p (sat_cons (step294 p h) (sat_cons (step247 p h) (sat_nil p)))
def c954 : List Lit := [(109, true), (76, true), (111, false)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true :=
  Snake9.LocalRup.prove_clause [c295, c254] c954 (by decide) p (sat_cons (step295 p h) (sat_cons (step254 p h) (sat_nil p)))
def c955 : List Lit := [(114, false), (115, true)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true :=
  Snake9.LocalRup.prove_clause [c296, c256] c955 (by decide) p (sat_cons (step296 p h) (sat_cons (step256 p h) (sat_nil p)))
def c956 : List Lit := [(343, false), (457, false)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true :=
  Snake9.LocalRup.prove_clause [c315, c314] c956 (by decide) p (sat_cons (step315 p h) (sat_cons (step314 p h) (sat_nil p)))
def c957 : List Lit := [(1414, false), (1442, true)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true :=
  Snake9.LocalRup.prove_clause [c692, c380] c957 (by decide) p (sat_cons (step692 p h) (sat_cons (step380 p h) (sat_nil p)))
def c958 : List Lit := [(1415, false), (1443, true)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true :=
  Snake9.LocalRup.prove_clause [c692, c385] c958 (by decide) p (sat_cons (step692 p h) (sat_cons (step385 p h) (sat_nil p)))
def c959 : List Lit := [(1416, false), (1444, true)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true :=
  Snake9.LocalRup.prove_clause [c692, c389] c959 (by decide) p (sat_cons (step692 p h) (sat_cons (step389 p h) (sat_nil p)))
def c960 : List Lit := [(1457, false), (1469, true)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true :=
  Snake9.LocalRup.prove_clause [c683, c414] c960 (by decide) p (sat_cons (step683 p h) (sat_cons (step414 p h) (sat_nil p)))
def c961 : List Lit := [(1458, false), (1470, true)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true :=
  Snake9.LocalRup.prove_clause [c683, c417] c961 (by decide) p (sat_cons (step683 p h) (sat_cons (step417 p h) (sat_nil p)))
def c962 : List Lit := [(1459, false), (1471, true)]
theorem step962 (p : Nat → Bool) (h : Constraints p) : clause p c962 = true :=
  Snake9.LocalRup.prove_clause [c683, c420] c962 (by decide) p (sat_cons (step683 p h) (sat_cons (step420 p h) (sat_nil p)))
def c963 : List Lit := [(1489, false), (1497, true)]
theorem step963 (p : Nat → Bool) (h : Constraints p) : clause p c963 = true :=
  Snake9.LocalRup.prove_clause [c684, c454] c963 (by decide) p (sat_cons (step684 p h) (sat_cons (step454 p h) (sat_nil p)))
def c964 : List Lit := [(1490, false), (1498, true)]
theorem step964 (p : Nat → Bool) (h : Constraints p) : clause p c964 = true :=
  Snake9.LocalRup.prove_clause [c684, c455] c964 (by decide) p (sat_cons (step684 p h) (sat_cons (step455 p h) (sat_nil p)))
def c965 : List Lit := [(1491, false), (1499, true)]
theorem step965 (p : Nat → Bool) (h : Constraints p) : clause p c965 = true :=
  Snake9.LocalRup.prove_clause [c684, c456] c965 (by decide) p (sat_cons (step684 p h) (sat_cons (step456 p h) (sat_nil p)))
def c966 : List Lit := [(1469, false), (1497, true)]
theorem step966 (p : Nat → Bool) (h : Constraints p) : clause p c966 = true :=
  Snake9.LocalRup.prove_clause [c694, c457] c966 (by decide) p (sat_cons (step694 p h) (sat_cons (step457 p h) (sat_nil p)))
def c967 : List Lit := [(1498, true), (1470, false)]
theorem step967 (p : Nat → Bool) (h : Constraints p) : clause p c967 = true :=
  Snake9.LocalRup.prove_clause [c694, c460] c967 (by decide) p (sat_cons (step694 p h) (sat_cons (step460 p h) (sat_nil p)))
def c968 : List Lit := [(1471, false), (1499, true)]
theorem step968 (p : Nat → Bool) (h : Constraints p) : clause p c968 = true :=
  Snake9.LocalRup.prove_clause [c694, c463] c968 (by decide) p (sat_cons (step694 p h) (sat_cons (step463 p h) (sat_nil p)))
def c969 : List Lit := [(1472, false), (1500, true)]
theorem step969 (p : Nat → Bool) (h : Constraints p) : clause p c969 = true :=
  Snake9.LocalRup.prove_clause [c694, c466] c969 (by decide) p (sat_cons (step694 p h) (sat_cons (step466 p h) (sat_nil p)))
def c970 : List Lit := [(1499, false), (1514, true)]
theorem step970 (p : Nat → Bool) (h : Constraints p) : clause p c970 = true :=
  Snake9.LocalRup.prove_clause [c693, c470] c970 (by decide) p (sat_cons (step693 p h) (sat_cons (step470 p h) (sat_nil p)))
def c971 : List Lit := [(1500, false), (1515, true)]
theorem step971 (p : Nat → Bool) (h : Constraints p) : clause p c971 = true :=
  Snake9.LocalRup.prove_clause [c693, c471] c971 (by decide) p (sat_cons (step693 p h) (sat_cons (step471 p h) (sat_nil p)))
def c972 : List Lit := [(1501, false), (1516, true)]
theorem step972 (p : Nat → Bool) (h : Constraints p) : clause p c972 = true :=
  Snake9.LocalRup.prove_clause [c693, c472] c972 (by decide) p (sat_cons (step693 p h) (sat_cons (step472 p h) (sat_nil p)))
def c973 : List Lit := [(1514, true), (1444, false)]
theorem step973 (p : Nat → Bool) (h : Constraints p) : clause p c973 = true :=
  Snake9.LocalRup.prove_clause [c695, c484] c973 (by decide) p (sat_cons (step695 p h) (sat_cons (step484 p h) (sat_nil p)))
def c974 : List Lit := [(1515, true), (1445, false)]
theorem step974 (p : Nat → Bool) (h : Constraints p) : clause p c974 = true :=
  Snake9.LocalRup.prove_clause [c695, c489] c974 (by decide) p (sat_cons (step695 p h) (sat_cons (step489 p h) (sat_nil p)))
def c975 : List Lit := [(1516, true), (1446, false)]
theorem step975 (p : Nat → Bool) (h : Constraints p) : clause p c975 = true :=
  Snake9.LocalRup.prove_clause [c695, c493] c975 (by decide) p (sat_cons (step695 p h) (sat_cons (step493 p h) (sat_nil p)))
def c976 : List Lit := [(1517, true), (1447, false)]
theorem step976 (p : Nat → Bool) (h : Constraints p) : clause p c976 = true :=
  Snake9.LocalRup.prove_clause [c695, c496] c976 (by decide) p (sat_cons (step695 p h) (sat_cons (step496 p h) (sat_nil p)))
def c977 : List Lit := [(1561, false), (1569, true)]
theorem step977 (p : Nat → Bool) (h : Constraints p) : clause p c977 = true :=
  Snake9.LocalRup.prove_clause [c686, c563] c977 (by decide) p (sat_cons (step686 p h) (sat_cons (step563 p h) (sat_nil p)))
def c978 : List Lit := [(1562, false), (1570, true)]
theorem step978 (p : Nat → Bool) (h : Constraints p) : clause p c978 = true :=
  Snake9.LocalRup.prove_clause [c686, c564] c978 (by decide) p (sat_cons (step686 p h) (sat_cons (step564 p h) (sat_nil p)))
def c979 : List Lit := [(1541, false), (1569, true)]
theorem step979 (p : Nat → Bool) (h : Constraints p) : clause p c979 = true :=
  Snake9.LocalRup.prove_clause [c685, c569] c979 (by decide) p (sat_cons (step685 p h) (sat_cons (step569 p h) (sat_nil p)))
def c980 : List Lit := [(1542, false), (1570, true)]
theorem step980 (p : Nat → Bool) (h : Constraints p) : clause p c980 = true :=
  Snake9.LocalRup.prove_clause [c685, c575] c980 (by decide) p (sat_cons (step685 p h) (sat_cons (step575 p h) (sat_nil p)))
def c981 : List Lit := [(1543, false), (1571, true)]
theorem step981 (p : Nat → Bool) (h : Constraints p) : clause p c981 = true :=
  Snake9.LocalRup.prove_clause [c685, c579] c981 (by decide) p (sat_cons (step685 p h) (sat_cons (step579 p h) (sat_nil p)))
def c982 : List Lit := [(1587, false), (1590, true)]
theorem step982 (p : Nat → Bool) (h : Constraints p) : clause p c982 = true :=
  Snake9.LocalRup.prove_clause [c719, c591] c982 (by decide) p (sat_cons (step719 p h) (sat_cons (step591 p h) (sat_nil p)))
def c983 : List Lit := [(1582, false), (1594, true)]
theorem step983 (p : Nat → Bool) (h : Constraints p) : clause p c983 = true :=
  Snake9.LocalRup.prove_clause [c720, c595] c983 (by decide) p (sat_cons (step720 p h) (sat_cons (step595 p h) (sat_nil p)))
def c984 : List Lit := [(1613, false), (1618, true)]
theorem step984 (p : Nat → Bool) (h : Constraints p) : clause p c984 = true :=
  Snake9.LocalRup.prove_clause [c711, c623] c984 (by decide) p (sat_cons (step711 p h) (sat_cons (step623 p h) (sat_nil p)))
def c985 : List Lit := [(1605, false), (1618, true)]
theorem step985 (p : Nat → Bool) (h : Constraints p) : clause p c985 = true :=
  Snake9.LocalRup.prove_clause [c708, c624] c985 (by decide) p (sat_cons (step708 p h) (sat_cons (step624 p h) (sat_nil p)))
def c986 : List Lit := [(1606, false), (1619, true)]
theorem step986 (p : Nat → Bool) (h : Constraints p) : clause p c986 = true :=
  Snake9.LocalRup.prove_clause [c708, c626] c986 (by decide) p (sat_cons (step708 p h) (sat_cons (step626 p h) (sat_nil p)))
def c987 : List Lit := [(1618, false), (1627, true)]
theorem step987 (p : Nat → Bool) (h : Constraints p) : clause p c987 = true :=
  Snake9.LocalRup.prove_clause [c696, c631] c987 (by decide) p (sat_cons (step696 p h) (sat_cons (step631 p h) (sat_nil p)))
def c988 : List Lit := [(1619, false), (1628, true)]
theorem step988 (p : Nat → Bool) (h : Constraints p) : clause p c988 = true :=
  Snake9.LocalRup.prove_clause [c696, c632] c988 (by decide) p (sat_cons (step696 p h) (sat_cons (step632 p h) (sat_nil p)))
def c989 : List Lit := [(1620, false), (1629, true)]
theorem step989 (p : Nat → Bool) (h : Constraints p) : clause p c989 = true :=
  Snake9.LocalRup.prove_clause [c696, c633] c989 (by decide) p (sat_cons (step696 p h) (sat_cons (step633 p h) (sat_nil p)))
def c990 : List Lit := [(1594, false), (1627, true)]
theorem step990 (p : Nat → Bool) (h : Constraints p) : clause p c990 = true :=
  Snake9.LocalRup.prove_clause [c712, c634] c990 (by decide) p (sat_cons (step712 p h) (sat_cons (step634 p h) (sat_nil p)))
def c991 : List Lit := [(1595, false), (1628, true)]
theorem step991 (p : Nat → Bool) (h : Constraints p) : clause p c991 = true :=
  Snake9.LocalRup.prove_clause [c712, c637] c991 (by decide) p (sat_cons (step712 p h) (sat_cons (step637 p h) (sat_nil p)))
def c992 : List Lit := [(1627, false), (1645, true)]
theorem step992 (p : Nat → Bool) (h : Constraints p) : clause p c992 = true :=
  Snake9.LocalRup.prove_clause [c691, c640] c992 (by decide) p (sat_cons (step691 p h) (sat_cons (step640 p h) (sat_nil p)))
def c993 : List Lit := [(1628, false), (1646, true)]
theorem step993 (p : Nat → Bool) (h : Constraints p) : clause p c993 = true :=
  Snake9.LocalRup.prove_clause [c691, c641] c993 (by decide) p (sat_cons (step691 p h) (sat_cons (step641 p h) (sat_nil p)))
def c994 : List Lit := [(1629, false), (1647, true)]
theorem step994 (p : Nat → Bool) (h : Constraints p) : clause p c994 = true :=
  Snake9.LocalRup.prove_clause [c691, c642] c994 (by decide) p (sat_cons (step691 p h) (sat_cons (step642 p h) (sat_nil p)))
def c995 : List Lit := [(1646, true), (1570, false)]
theorem step995 (p : Nat → Bool) (h : Constraints p) : clause p c995 = true :=
  Snake9.LocalRup.prove_clause [c713, c648] c995 (by decide) p (sat_cons (step713 p h) (sat_cons (step648 p h) (sat_nil p)))
def c996 : List Lit := [(1647, true), (1571, false)]
theorem step996 (p : Nat → Bool) (h : Constraints p) : clause p c996 = true :=
  Snake9.LocalRup.prove_clause [c713, c652] c996 (by decide) p (sat_cons (step713 p h) (sat_cons (step652 p h) (sat_nil p)))
def c997 : List Lit := [(1572, false), (1648, true)]
theorem step997 (p : Nat → Bool) (h : Constraints p) : clause p c997 = true :=
  Snake9.LocalRup.prove_clause [c713, c655] c997 (by decide) p (sat_cons (step713 p h) (sat_cons (step655 p h) (sat_nil p)))
def c998 : List Lit := [(1573, false), (1648, true)]
theorem step998 (p : Nat → Bool) (h : Constraints p) : clause p c998 = true :=
  Snake9.LocalRup.prove_clause [c710, c658] c998 (by decide) p (sat_cons (step710 p h) (sat_cons (step658 p h) (sat_nil p)))
def c999 : List Lit := [(1573, false), (1649, true)]
theorem step999 (p : Nat → Bool) (h : Constraints p) : clause p c999 = true :=
  Snake9.LocalRup.prove_clause [c713, c659] c999 (by decide) p (sat_cons (step713 p h) (sat_cons (step659 p h) (sat_nil p)))
def c1000 : List Lit := [(1513, false), (1650, false)]
theorem step1000 (p : Nat → Bool) (h : Constraints p) : clause p c1000 = true :=
  Snake9.LocalRup.prove_clause [c668, c661] c1000 (by decide) p (sat_cons (step668 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1001 : List Lit := [(1514, false), (1649, false)]
theorem step1001 (p : Nat → Bool) (h : Constraints p) : clause p c1001 = true :=
  Snake9.LocalRup.prove_clause [c668, c662] c1001 (by decide) p (sat_cons (step668 p h) (sat_cons (step662 p h) (sat_nil p)))
def c1002 : List Lit := [(1515, false), (1648, false)]
theorem step1002 (p : Nat → Bool) (h : Constraints p) : clause p c1002 = true :=
  Snake9.LocalRup.prove_clause [c668, c663] c1002 (by decide) p (sat_cons (step668 p h) (sat_cons (step663 p h) (sat_nil p)))
end B112E058
