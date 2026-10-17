import B112E152Inputs
namespace B112E152
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c947 : List Lit := [(77, false), (76, false), (120, false)]
theorem step947 (p : Nat → Bool) (h : Constraints p) : clause p c947 = true :=
  Snake9.LocalRup.prove_clause [c152, c160] c947 (by decide) p (sat_cons (step152 p h) (sat_cons (step160 p h) (sat_nil p)))
def c948 : List Lit := [(115, false), (55, false), (112, false)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true :=
  Snake9.LocalRup.prove_clause [c152, c368] c948 (by decide) p (sat_cons (step152 p h) (sat_cons (step368 p h) (sat_nil p)))
def c949 : List Lit := [(115, false), (55, false), (113, false)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true :=
  Snake9.LocalRup.prove_clause [c152, c369] c949 (by decide) p (sat_cons (step152 p h) (sat_cons (step369 p h) (sat_nil p)))
def c950 : List Lit := [(115, false), (55, false), (114, false)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true :=
  Snake9.LocalRup.prove_clause [c152, c370] c950 (by decide) p (sat_cons (step152 p h) (sat_cons (step370 p h) (sat_nil p)))
def c951 : List Lit := [(115, false), (55, false), (120, false)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true :=
  Snake9.LocalRup.prove_clause [c152, c371] c951 (by decide) p (sat_cons (step152 p h) (sat_cons (step371 p h) (sat_nil p)))
def c952 : List Lit := [(115, false), (112, false), (113, false)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true :=
  Snake9.LocalRup.prove_clause [c152, c372] c952 (by decide) p (sat_cons (step152 p h) (sat_cons (step372 p h) (sat_nil p)))
def c953 : List Lit := [(115, false), (112, false), (114, false)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true :=
  Snake9.LocalRup.prove_clause [c152, c373] c953 (by decide) p (sat_cons (step152 p h) (sat_cons (step373 p h) (sat_nil p)))
def c954 : List Lit := [(115, false), (112, false), (120, false)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true :=
  Snake9.LocalRup.prove_clause [c152, c374] c954 (by decide) p (sat_cons (step152 p h) (sat_cons (step374 p h) (sat_nil p)))
def c955 : List Lit := [(115, false), (113, false), (120, false)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true :=
  Snake9.LocalRup.prove_clause [c152, c375] c955 (by decide) p (sat_cons (step152 p h) (sat_cons (step375 p h) (sat_nil p)))
def c956 : List Lit := [(115, false), (114, false), (120, false)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true :=
  Snake9.LocalRup.prove_clause [c152, c376] c956 (by decide) p (sat_cons (step152 p h) (sat_cons (step376 p h) (sat_nil p)))
def c957 : List Lit := [(3, false)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true :=
  Snake9.LocalRup.prove_clause [c399, c4] c957 (by decide) p (sat_cons (step399 p h) (sat_cons (step4 p h) (sat_nil p)))
def c958 : List Lit := [(356, false)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true :=
  Snake9.LocalRup.prove_clause [c546, c545] c958 (by decide) p (sat_cons (step546 p h) (sat_cons (step545 p h) (sat_nil p)))
def c959 : List Lit := [(296, false)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true :=
  Snake9.LocalRup.prove_clause [c958, c494] c959 (by decide) p (sat_cons (step958 p h) (sat_cons (step494 p h) (sat_nil p)))
def c960 : List Lit := [(266, false)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true :=
  Snake9.LocalRup.prove_clause [c959, c477] c960 (by decide) p (sat_cons (step959 p h) (sat_cons (step477 p h) (sat_nil p)))
def c961 : List Lit := [(252, false)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true :=
  Snake9.LocalRup.prove_clause [c960, c461] c961 (by decide) p (sat_cons (step960 p h) (sat_cons (step461 p h) (sat_nil p)))
def c962 : List Lit := [(244, false)]
theorem step962 (p : Nat → Bool) (h : Constraints p) : clause p c962 = true :=
  Snake9.LocalRup.prove_clause [c961, c455] c962 (by decide) p (sat_cons (step961 p h) (sat_cons (step455 p h) (sat_nil p)))
def c963 : List Lit := [(1459, true)]
theorem step963 (p : Nat → Bool) (h : Constraints p) : clause p c963 = true :=
  Snake9.LocalRup.prove_clause [c957, c550] c963 (by decide) p (sat_cons (step957 p h) (sat_cons (step550 p h) (sat_nil p)))
def c964 : List Lit := [(1457, false), (1460, true)]
theorem step964 (p : Nat → Bool) (h : Constraints p) : clause p c964 = true :=
  Snake9.LocalRup.prove_clause [c957, c551] c964 (by decide) p (sat_cons (step957 p h) (sat_cons (step551 p h) (sat_nil p)))
def c965 : List Lit := [(1458, false), (1461, true)]
theorem step965 (p : Nat → Bool) (h : Constraints p) : clause p c965 = true :=
  Snake9.LocalRup.prove_clause [c957, c552] c965 (by decide) p (sat_cons (step957 p h) (sat_cons (step552 p h) (sat_nil p)))
def c966 : List Lit := [(1466, false), (1471, true)]
theorem step966 (p : Nat → Bool) (h : Constraints p) : clause p c966 = true :=
  Snake9.LocalRup.prove_clause [c963, c565] c966 (by decide) p (sat_cons (step963 p h) (sat_cons (step565 p h) (sat_nil p)))
def c967 : List Lit := [(1467, false), (1472, true)]
theorem step967 (p : Nat → Bool) (h : Constraints p) : clause p c967 = true :=
  Snake9.LocalRup.prove_clause [c963, c566] c967 (by decide) p (sat_cons (step963 p h) (sat_cons (step566 p h) (sat_nil p)))
def c968 : List Lit := [(1468, false), (1473, true)]
theorem step968 (p : Nat → Bool) (h : Constraints p) : clause p c968 = true :=
  Snake9.LocalRup.prove_clause [c963, c567] c968 (by decide) p (sat_cons (step963 p h) (sat_cons (step567 p h) (sat_nil p)))
def c969 : List Lit := [(1520, true)]
theorem step969 (p : Nat → Bool) (h : Constraints p) : clause p c969 = true :=
  Snake9.LocalRup.prove_clause [c413, c620, c622, c618, c614, c615, c66, c67] c969 (by decide) p (sat_cons (step413 p h) (sat_cons (step620 p h) (sat_cons (step622 p h) (sat_cons (step618 p h) (sat_cons (step614 p h) (sat_cons (step615 p h) (sat_cons (step66 p h) (sat_cons (step67 p h) (sat_nil p)))))))))
def c970 : List Lit := [(1524, true)]
theorem step970 (p : Nat → Bool) (h : Constraints p) : clause p c970 = true :=
  Snake9.LocalRup.prove_clause [c969, c626] c970 (by decide) p (sat_cons (step969 p h) (sat_cons (step626 p h) (sat_nil p)))
def c971 : List Lit := [(1490, true)]
theorem step971 (p : Nat → Bool) (h : Constraints p) : clause p c971 = true :=
  Snake9.LocalRup.prove_clause [c407, c590, c592, c586, c576, c580, c581, c573, c37, c38] c971 (by decide) p (sat_cons (step407 p h) (sat_cons (step590 p h) (sat_cons (step592 p h) (sat_cons (step586 p h) (sat_cons (step576 p h) (sat_cons (step580 p h) (sat_cons (step581 p h) (sat_cons (step573 p h) (sat_cons (step37 p h) (sat_cons (step38 p h) (sat_nil p)))))))))))
def c972 : List Lit := [(1547, true)]
theorem step972 (p : Nat → Bool) (h : Constraints p) : clause p c972 = true :=
  Snake9.LocalRup.prove_clause [c418, c657, c659, c653, c639, c641, c646, c647, c636, c633, c634, c75, c91, c90] c972 (by decide) p (sat_cons (step418 p h) (sat_cons (step657 p h) (sat_cons (step659 p h) (sat_cons (step653 p h) (sat_cons (step639 p h) (sat_cons (step641 p h) (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step636 p h) (sat_cons (step633 p h) (sat_cons (step634 p h) (sat_cons (step75 p h) (sat_cons (step91 p h) (sat_cons (step90 p h) (sat_nil p)))))))))))))))
def c973 : List Lit := [(1556, true)]
theorem step973 (p : Nat → Bool) (h : Constraints p) : clause p c973 = true :=
  Snake9.LocalRup.prove_clause [c972, c970, c668] c973 (by decide) p (sat_cons (step972 p h) (sat_cons (step970 p h) (sat_cons (step668 p h) (sat_nil p))))
def c974 : List Lit := [(1471, true)]
theorem step974 (p : Nat → Bool) (h : Constraints p) : clause p c974 = true :=
  Snake9.LocalRup.prove_clause [c404, c401, c400, c966, c568, c559, c561, c964, c556, c554, c547, c548, c25, c9, c6, c12] c974 (by decide) p (sat_cons (step404 p h) (sat_cons (step401 p h) (sat_cons (step400 p h) (sat_cons (step966 p h) (sat_cons (step568 p h) (sat_cons (step559 p h) (sat_cons (step561 p h) (sat_cons (step964 p h) (sat_cons (step556 p h) (sat_cons (step554 p h) (sat_cons (step547 p h) (sat_cons (step548 p h) (sat_cons (step25 p h) (sat_cons (step9 p h) (sat_cons (step6 p h) (sat_cons (step12 p h) (sat_nil p)))))))))))))))))
def c975 : List Lit := [(1499, true)]
theorem step975 (p : Nat → Bool) (h : Constraints p) : clause p c975 = true :=
  Snake9.LocalRup.prove_clause [c974, c971, c599] c975 (by decide) p (sat_cons (step974 p h) (sat_cons (step971 p h) (sat_cons (step599 p h) (sat_nil p))))
def c976 : List Lit := [(1602, true)]
theorem step976 (p : Nat → Bool) (h : Constraints p) : clause p c976 = true :=
  Snake9.LocalRup.prove_clause [c425, c710, c713, c706, c696, c701, c702, c694, c126, c127] c976 (by decide) p (sat_cons (step425 p h) (sat_cons (step710 p h) (sat_cons (step713 p h) (sat_cons (step706 p h) (sat_cons (step696 p h) (sat_cons (step701 p h) (sat_cons (step702 p h) (sat_cons (step694 p h) (sat_cons (step126 p h) (sat_cons (step127 p h) (sat_nil p)))))))))))
def c977 : List Lit := [(1621, true), (30, false)]
theorem step977 (p : Nat → Bool) (h : Constraints p) : clause p c977 = true :=
  Snake9.LocalRup.prove_clause [c432, c742, c744, c739, c740, c736, c207, c186, c201] c977 (by decide) p (sat_cons (step432 p h) (sat_cons (step742 p h) (sat_cons (step744 p h) (sat_cons (step739 p h) (sat_cons (step740 p h) (sat_cons (step736 p h) (sat_cons (step207 p h) (sat_cons (step186 p h) (sat_cons (step201 p h) (sat_nil p))))))))))
def c978 : List Lit := [(99, false), (100, false), (82, true), (79, false), (80, false)]
theorem step978 (p : Nat → Bool) (h : Constraints p) : clause p c978 = true :=
  Snake9.LocalRup.prove_clause [c429, c264, c162, c166] c978 (by decide) p (sat_cons (step429 p h) (sat_cons (step264 p h) (sat_cons (step162 p h) (sat_cons (step166 p h) (sat_nil p)))))
def c979 : List Lit := [(1484, false), (1491, true)]
theorem step979 (p : Nat → Bool) (h : Constraints p) : clause p c979 = true :=
  Snake9.LocalRup.prove_clause [c407, c591, c585, c587, c593, c580, c581, c576, c37, c573, c38] c979 (by decide) p (sat_cons (step407 p h) (sat_cons (step591 p h) (sat_cons (step585 p h) (sat_cons (step587 p h) (sat_cons (step593 p h) (sat_cons (step580 p h) (sat_cons (step581 p h) (sat_cons (step576 p h) (sat_cons (step37 p h) (sat_cons (step573 p h) (sat_cons (step38 p h) (sat_nil p))))))))))))
def c980 : List Lit := [(1482, true), (1500, true)]
theorem step980 (p : Nat → Bool) (h : Constraints p) : clause p c980 = true :=
  Snake9.LocalRup.prove_clause [c971, c974, c407, c405, c404, c403, c600, c979, c583, c596, c577, c603, c967, c560, c580, c581, c37, c38, c573, c575, c579, c32, c35, c25, c556, c558, c559, c562, c569, c553, c964, c18, c547, c24, c10] c980 (by decide) p (sat_cons (step971 p h) (sat_cons (step974 p h) (sat_cons (step407 p h) (sat_cons (step405 p h) (sat_cons (step404 p h) (sat_cons (step403 p h) (sat_cons (step600 p h) (sat_cons (step979 p h) (sat_cons (step583 p h) (sat_cons (step596 p h) (sat_cons (step577 p h) (sat_cons (step603 p h) (sat_cons (step967 p h) (sat_cons (step560 p h) (sat_cons (step580 p h) (sat_cons (step581 p h) (sat_cons (step37 p h) (sat_cons (step38 p h) (sat_cons (step573 p h) (sat_cons (step575 p h) (sat_cons (step579 p h) (sat_cons (step32 p h) (sat_cons (step35 p h) (sat_cons (step25 p h) (sat_cons (step556 p h) (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step562 p h) (sat_cons (step569 p h) (sat_cons (step553 p h) (sat_cons (step964 p h) (sat_cons (step18 p h) (sat_cons (step547 p h) (sat_cons (step24 p h) (sat_cons (step10 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c981 : List Lit := [(1457, true), (1500, true)]
theorem step981 (p : Nat → Bool) (h : Constraints p) : clause p c981 = true :=
  Snake9.LocalRup.prove_clause [c971, c974, c401, c400, c404, c600, c979, c583, c603, c967, c560, c547, c548, c8, c9, c6, c10, c557, c558, c562, c25, c554, c12] c981 (by decide) p (sat_cons (step971 p h) (sat_cons (step974 p h) (sat_cons (step401 p h) (sat_cons (step400 p h) (sat_cons (step404 p h) (sat_cons (step600 p h) (sat_cons (step979 p h) (sat_cons (step583 p h) (sat_cons (step603 p h) (sat_cons (step967 p h) (sat_cons (step560 p h) (sat_cons (step547 p h) (sat_cons (step548 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step6 p h) (sat_cons (step10 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step562 p h) (sat_cons (step25 p h) (sat_cons (step554 p h) (sat_cons (step12 p h) (sat_nil p))))))))))))))))))))))))
def c982 : List Lit := [(1539, true), (54, false), (47, false)]
theorem step982 (p : Nat → Bool) (h : Constraints p) : clause p c982 = true :=
  Snake9.LocalRup.prove_clause [c646, c647, c91] c982 (by decide) p (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step91 p h) (sat_nil p))))
def c983 : List Lit := [(1533, false), (1548, true)]
theorem step983 (p : Nat → Bool) (h : Constraints p) : clause p c983 = true :=
  Snake9.LocalRup.prove_clause [c418, c663, c639, c642, c660, c633, c634, c653, c982, c647, c90, c74] c983 (by decide) p (sat_cons (step418 p h) (sat_cons (step663 p h) (sat_cons (step639 p h) (sat_cons (step642 p h) (sat_cons (step660 p h) (sat_cons (step633 p h) (sat_cons (step634 p h) (sat_cons (step653 p h) (sat_cons (step982 p h) (sat_cons (step647 p h) (sat_cons (step90 p h) (sat_cons (step74 p h) (sat_nil p)))))))))))))
def c984 : List Lit := [(1541, true), (1575, true)]
theorem step984 (p : Nat → Bool) (h : Constraints p) : clause p c984 = true :=
  Snake9.LocalRup.prove_clause [c973, c974, c972, c969, c975, c970, c416, c420, c680, c669, c983, c637, c672, c629, c610, c608, c612, c684, c600, c979, c584, c52, c627, c649, c650, c102, c83, c96, c84, c100, c617, c614, c623] c984 (by decide) p (sat_cons (step973 p h) (sat_cons (step974 p h) (sat_cons (step972 p h) (sat_cons (step969 p h) (sat_cons (step975 p h) (sat_cons (step970 p h) (sat_cons (step416 p h) (sat_cons (step420 p h) (sat_cons (step680 p h) (sat_cons (step669 p h) (sat_cons (step983 p h) (sat_cons (step637 p h) (sat_cons (step672 p h) (sat_cons (step629 p h) (sat_cons (step610 p h) (sat_cons (step608 p h) (sat_cons (step612 p h) (sat_cons (step684 p h) (sat_cons (step600 p h) (sat_cons (step979 p h) (sat_cons (step584 p h) (sat_cons (step52 p h) (sat_cons (step627 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step102 p h) (sat_cons (step83 p h) (sat_cons (step96 p h) (sat_cons (step84 p h) (sat_cons (step100 p h) (sat_cons (step617 p h) (sat_cons (step614 p h) (sat_cons (step623 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c985 : List Lit := [(1575, true)]
theorem step985 (p : Nat → Bool) (h : Constraints p) : clause p c985 = true :=
  Snake9.LocalRup.prove_clause [c975, c970, c418, c680, c669, c658, c983, c636, c984, c652, c654, c660, c647, c641, c633, c982, c76, c90] c985 (by decide) p (sat_cons (step975 p h) (sat_cons (step970 p h) (sat_cons (step418 p h) (sat_cons (step680 p h) (sat_cons (step669 p h) (sat_cons (step658 p h) (sat_cons (step983 p h) (sat_cons (step636 p h) (sat_cons (step984 p h) (sat_cons (step652 p h) (sat_cons (step654 p h) (sat_cons (step660 p h) (sat_cons (step647 p h) (sat_cons (step641 p h) (sat_cons (step633 p h) (sat_cons (step982 p h) (sat_cons (step76 p h) (sat_cons (step90 p h) (sat_nil p)))))))))))))))))))
def c986 : List Lit := [(1719, false)]
theorem step986 (p : Nat → Bool) (h : Constraints p) : clause p c986 = true :=
  Snake9.LocalRup.prove_clause [c985, c921, c915] c986 (by decide) p (sat_cons (step985 p h) (sat_cons (step921 p h) (sat_cons (step915 p h) (sat_nil p))))
def c987 : List Lit := [(1662, true), (1655, false)]
theorem step987 (p : Nat → Bool) (h : Constraints p) : clause p c987 = true :=
  Snake9.LocalRup.prove_clause [c434, c795, c804, c808, c798, c784, c786, c790, c781, c782, c211, c227, c224] c987 (by decide) p (sat_cons (step434 p h) (sat_cons (step795 p h) (sat_cons (step804 p h) (sat_cons (step808 p h) (sat_cons (step798 p h) (sat_cons (step784 p h) (sat_cons (step786 p h) (sat_cons (step790 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step211 p h) (sat_cons (step227 p h) (sat_cons (step224 p h) (sat_nil p))))))))))))))
def c988 : List Lit := [(1655, true), (105, false), (48, false)]
theorem step988 (p : Nat → Bool) (h : Constraints p) : clause p c988 = true :=
  Snake9.LocalRup.prove_clause [c792, c793, c300] c988 (by decide) p (sat_cons (step792 p h) (sat_cons (step793 p h) (sat_cons (step300 p h) (sat_nil p))))
def c989 : List Lit := [(1635, true), (1621, false), (115, false)]
theorem step989 (p : Nat → Bool) (h : Constraints p) : clause p c989 = true :=
  Snake9.LocalRup.prove_clause [c426, c153, c976, c428, c750, c148, c150, c133, c704, c705, c151, c763, c766, c755, c711, c714, c732, c707, c698, c724, c702, c159, c122] c989 (by decide) p (sat_cons (step426 p h) (sat_cons (step153 p h) (sat_cons (step976 p h) (sat_cons (step428 p h) (sat_cons (step750 p h) (sat_cons (step148 p h) (sat_cons (step150 p h) (sat_cons (step133 p h) (sat_cons (step704 p h) (sat_cons (step705 p h) (sat_cons (step151 p h) (sat_cons (step763 p h) (sat_cons (step766 p h) (sat_cons (step755 p h) (sat_cons (step711 p h) (sat_cons (step714 p h) (sat_cons (step732 p h) (sat_cons (step707 p h) (sat_cons (step698 p h) (sat_cons (step724 p h) (sat_cons (step702 p h) (sat_cons (step159 p h) (sat_cons (step122 p h) (sat_nil p))))))))))))))))))))))))
def c990 : List Lit := [(1626, true), (81, true)]
theorem step990 (p : Nat → Bool) (h : Constraints p) : clause p c990 = true :=
  Snake9.LocalRup.prove_clause [c429, c737, c744, c751, c755, c747, c745, c730, c738, c739, c727, c728, c161, c183, c196, c167] c990 (by decide) p (sat_cons (step429 p h) (sat_cons (step737 p h) (sat_cons (step744 p h) (sat_cons (step751 p h) (sat_cons (step755 p h) (sat_cons (step747 p h) (sat_cons (step745 p h) (sat_cons (step730 p h) (sat_cons (step738 p h) (sat_cons (step739 p h) (sat_cons (step727 p h) (sat_cons (step728 p h) (sat_cons (step161 p h) (sat_cons (step183 p h) (sat_cons (step196 p h) (sat_cons (step167 p h) (sat_nil p)))))))))))))))))
def c991 : List Lit := [(84, false), (88, false), (1611, true)]
theorem step991 (p : Nat → Bool) (h : Constraints p) : clause p c991 = true :=
  Snake9.LocalRup.prove_clause [c429, c728, c727, c183, c161, c196, c167] c991 (by decide) p (sat_cons (step429 p h) (sat_cons (step728 p h) (sat_cons (step727 p h) (sat_cons (step183 p h) (sat_cons (step161 p h) (sat_cons (step196 p h) (sat_cons (step167 p h) (sat_nil p))))))))
def c992 : List Lit := [(67, false), (106, false), (86, false), (1669, true)]
theorem step992 (p : Nat → Bool) (h : Constraints p) : clause p c992 = true :=
  Snake9.LocalRup.prove_clause [c320, c321, c817] c992 (by decide) p (sat_cons (step320 p h) (sat_cons (step321 p h) (sat_cons (step817 p h) (sat_nil p))))
def c993 : List Lit := [(67, true), (66, false), (76, false), (1604, true), (1596, false)]
theorem step993 (p : Nat → Bool) (h : Constraints p) : clause p c993 = true :=
  Snake9.LocalRup.prove_clause [c712, c709, c701, c703, c707, c122, c715, c698] c993 (by decide) p (sat_cons (step712 p h) (sat_cons (step709 p h) (sat_cons (step701 p h) (sat_cons (step703 p h) (sat_cons (step707 p h) (sat_cons (step122 p h) (sat_cons (step715 p h) (sat_cons (step698 p h) (sat_nil p)))))))))
def c994 : List Lit := [(107, true), (1700, true), (1682, false), (1671, false), (105, false), (48, false)]
theorem step994 (p : Nat → Bool) (h : Constraints p) : clause p c994 = true :=
  Snake9.LocalRup.prove_clause [c434, c988, c987, c877, c862, c828, c816, c817, c825, c301, c302, c857, c794, c883, c796, c805, c809, c799, c784, c786, c790, c781, c782, c211, c227, c224] c994 (by decide) p (sat_cons (step434 p h) (sat_cons (step988 p h) (sat_cons (step987 p h) (sat_cons (step877 p h) (sat_cons (step862 p h) (sat_cons (step828 p h) (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step825 p h) (sat_cons (step301 p h) (sat_cons (step302 p h) (sat_cons (step857 p h) (sat_cons (step794 p h) (sat_cons (step883 p h) (sat_cons (step796 p h) (sat_cons (step805 p h) (sat_cons (step809 p h) (sat_cons (step799 p h) (sat_cons (step784 p h) (sat_cons (step786 p h) (sat_cons (step790 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step211 p h) (sat_cons (step227 p h) (sat_cons (step224 p h) (sat_nil p)))))))))))))))))))))))))))
def c995 : List Lit := [(1663, true), (1656, false)]
theorem step995 (p : Nat → Bool) (h : Constraints p) : clause p c995 = true :=
  Snake9.LocalRup.prove_clause [c434, c796, c805, c809, c799, c784, c786, c790, c781, c782, c211, c227, c224] c995 (by decide) p (sat_cons (step434 p h) (sat_cons (step796 p h) (sat_cons (step805 p h) (sat_cons (step809 p h) (sat_cons (step799 p h) (sat_cons (step784 p h) (sat_cons (step786 p h) (sat_cons (step790 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step211 p h) (sat_cons (step227 p h) (sat_cons (step224 p h) (sat_nil p))))))))))))))
def c996 : List Lit := [(115, false), (1682, true), (116, true), (55, false)]
theorem step996 (p : Nat → Bool) (h : Constraints p) : clause p c996 = true :=
  Snake9.LocalRup.prove_clause [c950, c951, c831, c832, c841] c996 (by decide) p (sat_cons (step950 p h) (sat_cons (step951 p h) (sat_cons (step831 p h) (sat_cons (step832 p h) (sat_cons (step841 p h) (sat_nil p))))))
def c997 : List Lit := [(1682, true), (116, true), (59, false), (1539, true)]
theorem step997 (p : Nat → Bool) (h : Constraints p) : clause p c997 = true :=
  Snake9.LocalRup.prove_clause [c419, c647, c646, c996, c94, c95, c104, c93, c832, c831, c841] c997 (by decide) p (sat_cons (step419 p h) (sat_cons (step647 p h) (sat_cons (step646 p h) (sat_cons (step996 p h) (sat_cons (step94 p h) (sat_cons (step95 p h) (sat_cons (step104 p h) (sat_cons (step93 p h) (sat_cons (step832 p h) (sat_cons (step831 p h) (sat_cons (step841 p h) (sat_nil p))))))))))))
def c998 : List Lit := [(1513, true), (32, false), (48, false)]
theorem step998 (p : Nat → Bool) (h : Constraints p) : clause p c998 = true :=
  Snake9.LocalRup.prove_clause [c610, c612, c608, c55] c998 (by decide) p (sat_cons (step610 p h) (sat_cons (step612 p h) (sat_cons (step608 p h) (sat_cons (step55 p h) (sat_nil p)))))
def c999 : List Lit := [(1516, true), (40, false)]
theorem step999 (p : Nat → Bool) (h : Constraints p) : clause p c999 = true :=
  Snake9.LocalRup.prove_clause [c413, c66, c614, c615, c67] c999 (by decide) p (sat_cons (step413 p h) (sat_cons (step66 p h) (sat_cons (step614 p h) (sat_cons (step615 p h) (sat_cons (step67 p h) (sat_nil p))))))
def c1000 : List Lit := [(99, false), (1670, true), (100, false)]
theorem step1000 (p : Nat → Bool) (h : Constraints p) : clause p c1000 = true :=
  Snake9.LocalRup.prove_clause [c439, c818, c819, c952, c267, c354, c363] c1000 (by decide) p (sat_cons (step439 p h) (sat_cons (step818 p h) (sat_cons (step819 p h) (sat_cons (step952 p h) (sat_cons (step267 p h) (sat_cons (step354 p h) (sat_cons (step363 p h) (sat_nil p))))))))
def c1001 : List Lit := [(1539, true), (47, false), (115, true)]
theorem step1001 (p : Nat → Bool) (h : Constraints p) : clause p c1001 = true :=
  Snake9.LocalRup.prove_clause [c419, c646, c982, c95] c1001 (by decide) p (sat_cons (step419 p h) (sat_cons (step646 p h) (sat_cons (step982 p h) (sat_cons (step95 p h) (sat_nil p)))))
def c1002 : List Lit := [(50, false), (1531, true), (106, false), (107, false)]
theorem step1002 (p : Nat → Bool) (h : Constraints p) : clause p c1002 = true :=
  Snake9.LocalRup.prove_clause [c417, c634, c633, c927, c73, c87] c1002 (by decide) p (sat_cons (step417 p h) (sat_cons (step634 p h) (sat_cons (step633 p h) (sat_cons (step927 p h) (sat_cons (step73 p h) (sat_cons (step87 p h) (sat_nil p)))))))
def c1003 : List Lit := [(1543, true), (120, false), (115, true)]
theorem step1003 (p : Nat → Bool) (h : Constraints p) : clause p c1003 = true :=
  Snake9.LocalRup.prove_clause [c419, c652, c653, c649, c646, c94, c104] c1003 (by decide) p (sat_cons (step419 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step649 p h) (sat_cons (step646 p h) (sat_cons (step94 p h) (sat_cons (step104 p h) (sat_nil p))))))))
def c1004 : List Lit := [(1549, false), (86, true), (67, true), (1658, false), (1687, false), (32, true), (1577, true), (71, true)]
theorem step1004 (p : Nat → Bool) (h : Constraints p) : clause p c1004 = true :=
  Snake9.LocalRup.prove_clause [c970, c975, c969, c921, c971, c974, c412, c411, c404, c152, c426, c682, c670, c674, c681, c686, c629, c916, c603, c600, c981, c610, c979, c964, c607, c608, c583, c584, c569, c61, c44, c60, c559, c561, c56, c786, c556, c554, c57, c809, c25, c741, c881, c27, c743, c903, c703, c751, c708, c772, c712, c715, c709, c696, c704, c693, c142, c133] c1004 (by decide) p (sat_cons (step970 p h) (sat_cons (step975 p h) (sat_cons (step969 p h) (sat_cons (step921 p h) (sat_cons (step971 p h) (sat_cons (step974 p h) (sat_cons (step412 p h) (sat_cons (step411 p h) (sat_cons (step404 p h) (sat_cons (step152 p h) (sat_cons (step426 p h) (sat_cons (step682 p h) (sat_cons (step670 p h) (sat_cons (step674 p h) (sat_cons (step681 p h) (sat_cons (step686 p h) (sat_cons (step629 p h) (sat_cons (step916 p h) (sat_cons (step603 p h) (sat_cons (step600 p h) (sat_cons (step981 p h) (sat_cons (step610 p h) (sat_cons (step979 p h) (sat_cons (step964 p h) (sat_cons (step607 p h) (sat_cons (step608 p h) (sat_cons (step583 p h) (sat_cons (step584 p h) (sat_cons (step569 p h) (sat_cons (step61 p h) (sat_cons (step44 p h) (sat_cons (step60 p h) (sat_cons (step559 p h) (sat_cons (step561 p h) (sat_cons (step56 p h) (sat_cons (step786 p h) (sat_cons (step556 p h) (sat_cons (step554 p h) (sat_cons (step57 p h) (sat_cons (step809 p h) (sat_cons (step25 p h) (sat_cons (step741 p h) (sat_cons (step881 p h) (sat_cons (step27 p h) (sat_cons (step743 p h) (sat_cons (step903 p h) (sat_cons (step703 p h) (sat_cons (step751 p h) (sat_cons (step708 p h) (sat_cons (step772 p h) (sat_cons (step712 p h) (sat_cons (step715 p h) (sat_cons (step709 p h) (sat_cons (step696 p h) (sat_cons (step704 p h) (sat_cons (step693 p h) (sat_cons (step142 p h) (sat_cons (step133 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1005 : List Lit := [(53, true), (115, true), (1549, true), (1531, false), (32, true)]
theorem step1005 (p : Nat → Bool) (h : Constraints p) : clause p c1005 = true :=
  Snake9.LocalRup.prove_clause [c419, c420, c416, c641, c661, c656, c647, c648, c653, c654, c94, c664, c649, c650, c642, c637, c102, c96, c83, c103] c1005 (by decide) p (sat_cons (step419 p h) (sat_cons (step420 p h) (sat_cons (step416 p h) (sat_cons (step641 p h) (sat_cons (step661 p h) (sat_cons (step656 p h) (sat_cons (step647 p h) (sat_cons (step648 p h) (sat_cons (step653 p h) (sat_cons (step654 p h) (sat_cons (step94 p h) (sat_cons (step664 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step642 p h) (sat_cons (step637 p h) (sat_cons (step102 p h) (sat_cons (step96 p h) (sat_cons (step83 p h) (sat_cons (step103 p h) (sat_nil p)))))))))))))))))))))
def c1006 : List Lit := [(115, true), (45, false), (1549, true), (1531, false), (50, false), (32, true)]
theorem step1006 (p : Nat → Bool) (h : Constraints p) : clause p c1006 = true :=
  Snake9.LocalRup.prove_clause [c419, c420, c666, c1005, c76, c75, c635, c644, c645, c664, c637, c652, c653, c649, c650, c646, c102, c95, c97, c89] c1006 (by decide) p (sat_cons (step419 p h) (sat_cons (step420 p h) (sat_cons (step666 p h) (sat_cons (step1005 p h) (sat_cons (step76 p h) (sat_cons (step75 p h) (sat_cons (step635 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step664 p h) (sat_cons (step637 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step646 p h) (sat_cons (step102 p h) (sat_cons (step95 p h) (sat_cons (step97 p h) (sat_cons (step89 p h) (sat_nil p)))))))))))))))))))))
def c1007 : List Lit := [(55, true), (1540, true), (45, false), (1549, true), (50, false)]
theorem step1007 (p : Nat → Bool) (h : Constraints p) : clause p c1007 = true :=
  Snake9.LocalRup.prove_clause [c646, c648, c653, c76, c75, c664, c635, c644] c1007 (by decide) p (sat_cons (step646 p h) (sat_cons (step648 p h) (sat_cons (step653 p h) (sat_cons (step76 p h) (sat_cons (step75 p h) (sat_cons (step664 p h) (sat_cons (step635 p h) (sat_cons (step644 p h) (sat_nil p)))))))))
def c1008 : List Lit := [(47, false), (1539, true), (50, false)]
theorem step1008 (p : Nat → Bool) (h : Constraints p) : clause p c1008 = true :=
  Snake9.LocalRup.prove_clause [c418, c647, c982, c76, c90] c1008 (by decide) p (sat_cons (step418 p h) (sat_cons (step647 p h) (sat_cons (step982 p h) (sat_cons (step76 p h) (sat_cons (step90 p h) (sat_nil p))))))
def c1009 : List Lit := [(48, false), (56, false), (59, false), (1548, false), (107, true), (1539, true), (1621, false), (32, true)]
theorem step1009 (p : Nat → Bool) (h : Constraints p) : clause p c1009 = true :=
  Snake9.LocalRup.prove_clause [c420, c416, c419, c975, c921, c646, c102, c96, c82, c83, c101, c100, c84, c103, c997, c614, c617, c94, c623, c989, c948, c949, c627, c820, c673, c994, c681, c892, c916] c1009 (by decide) p (sat_cons (step420 p h) (sat_cons (step416 p h) (sat_cons (step419 p h) (sat_cons (step975 p h) (sat_cons (step921 p h) (sat_cons (step646 p h) (sat_cons (step102 p h) (sat_cons (step96 p h) (sat_cons (step82 p h) (sat_cons (step83 p h) (sat_cons (step101 p h) (sat_cons (step100 p h) (sat_cons (step84 p h) (sat_cons (step103 p h) (sat_cons (step997 p h) (sat_cons (step614 p h) (sat_cons (step617 p h) (sat_cons (step94 p h) (sat_cons (step623 p h) (sat_cons (step989 p h) (sat_cons (step948 p h) (sat_cons (step949 p h) (sat_cons (step627 p h) (sat_cons (step820 p h) (sat_cons (step673 p h) (sat_cons (step994 p h) (sat_cons (step681 p h) (sat_cons (step892 p h) (sat_cons (step916 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1010 : List Lit := [(1596, false), (67, true), (1636, true), (1621, false)]
theorem step1010 (p : Nat → Bool) (h : Constraints p) : clause p c1010 = true :=
  Snake9.LocalRup.prove_clause [c421, c701, c750, c771, c712, c707, c709, c711, c715, c703, c767, c696, c698, c755, c694, c105, c732, c113, c724, c122] c1010 (by decide) p (sat_cons (step421 p h) (sat_cons (step701 p h) (sat_cons (step750 p h) (sat_cons (step771 p h) (sat_cons (step712 p h) (sat_cons (step707 p h) (sat_cons (step709 p h) (sat_cons (step711 p h) (sat_cons (step715 p h) (sat_cons (step703 p h) (sat_cons (step767 p h) (sat_cons (step696 p h) (sat_cons (step698 p h) (sat_cons (step755 p h) (sat_cons (step694 p h) (sat_cons (step105 p h) (sat_cons (step732 p h) (sat_cons (step113 p h) (sat_cons (step724 p h) (sat_cons (step122 p h) (sat_nil p)))))))))))))))))))))
end B112E152
