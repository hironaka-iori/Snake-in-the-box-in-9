import B112E034Part0136
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c10547 : List Lit := [(1749, false), (1760, true)]
theorem step10547 (p : Nat → Bool) (h : Constraints p) : clause p c10547 = true :=
  Snake9.LocalRup.prove_clause [c8663, c1482] c10547 (by decide) p (sat_cons (step8663 p h) (sat_cons (step1482 p h) (sat_nil p)))
def c10548 : List Lit := [(118, false), (93, false), (115, false)]
theorem step10548 (p : Nat → Bool) (h : Constraints p) : clause p c10548 = true :=
  Snake9.LocalRup.prove_clause [c10428, c700] c10548 (by decide) p (sat_cons (step10428 p h) (sat_cons (step700 p h) (sat_nil p)))
def c10549 : List Lit := [(93, false), (115, false), (107, false)]
theorem step10549 (p : Nat → Bool) (h : Constraints p) : clause p c10549 = true :=
  Snake9.LocalRup.prove_clause [c10428, c697] c10549 (by decide) p (sat_cons (step10428 p h) (sat_cons (step697 p h) (sat_nil p)))
def c10550 : List Lit := [(126, false), (93, false), (115, false)]
theorem step10550 (p : Nat → Bool) (h : Constraints p) : clause p c10550 = true :=
  Snake9.LocalRup.prove_clause [c10428, c701] c10550 (by decide) p (sat_cons (step10428 p h) (sat_cons (step701 p h) (sat_nil p)))
def c10551 : List Lit := [(119, true), (35, true), (120, false), (1623, true), (115, true)]
theorem step10551 (p : Nat → Bool) (h : Constraints p) : clause p c10551 = true :=
  Snake9.LocalRup.prove_clause [c10424, c2192] c10551 (by decide) p (sat_cons (step10424 p h) (sat_cons (step2192 p h) (sat_nil p)))
def c10552 : List Lit := [(126, false), (37, false), (115, false)]
theorem step10552 (p : Nat → Bool) (h : Constraints p) : clause p c10552 = true :=
  Snake9.LocalRup.prove_clause [c10428, c685] c10552 (by decide) p (sat_cons (step10428 p h) (sat_cons (step685 p h) (sat_nil p)))
def c10553 : List Lit := [(118, false), (126, false), (115, false)]
theorem step10553 (p : Nat → Bool) (h : Constraints p) : clause p c10553 = true :=
  Snake9.LocalRup.prove_clause [c10428, c706] c10553 (by decide) p (sat_cons (step10428 p h) (sat_cons (step706 p h) (sat_nil p)))
def c10554 : List Lit := [(37, false), (115, false), (107, false)]
theorem step10554 (p : Nat → Bool) (h : Constraints p) : clause p c10554 = true :=
  Snake9.LocalRup.prove_clause [c10428, c681] c10554 (by decide) p (sat_cons (step10428 p h) (sat_cons (step681 p h) (sat_nil p)))
def c10555 : List Lit := [(118, false), (115, false), (107, false)]
theorem step10555 (p : Nat → Bool) (h : Constraints p) : clause p c10555 = true :=
  Snake9.LocalRup.prove_clause [c10428, c703] c10555 (by decide) p (sat_cons (step10428 p h) (sat_cons (step703 p h) (sat_nil p)))
def c10556 : List Lit := [(93, false), (37, false), (115, false)]
theorem step10556 (p : Nat → Bool) (h : Constraints p) : clause p c10556 = true :=
  Snake9.LocalRup.prove_clause [c10428, c678] c10556 (by decide) p (sat_cons (step10428 p h) (sat_cons (step678 p h) (sat_nil p)))
def c10557 : List Lit := [(106, false), (109, false), (107, false)]
theorem step10557 (p : Nat → Bool) (h : Constraints p) : clause p c10557 = true :=
  Snake9.LocalRup.prove_clause [c10428, c536] c10557 (by decide) p (sat_cons (step10428 p h) (sat_cons (step536 p h) (sat_nil p)))
def c10558 : List Lit := [(106, false), (107, false), (86, false)]
theorem step10558 (p : Nat → Bool) (h : Constraints p) : clause p c10558 = true :=
  Snake9.LocalRup.prove_clause [c10428, c534] c10558 (by decide) p (sat_cons (step10428 p h) (sat_cons (step534 p h) (sat_nil p)))
def c10559 : List Lit := [(37, false), (118, false), (115, false)]
theorem step10559 (p : Nat → Bool) (h : Constraints p) : clause p c10559 = true :=
  Snake9.LocalRup.prove_clause [c10428, c684] c10559 (by decide) p (sat_cons (step10428 p h) (sat_cons (step684 p h) (sat_nil p)))
def c10560 : List Lit := [(106, false), (115, false), (107, false)]
theorem step10560 (p : Nat → Bool) (h : Constraints p) : clause p c10560 = true :=
  Snake9.LocalRup.prove_clause [c10428, c1764] c10560 (by decide) p (sat_cons (step10428 p h) (sat_cons (step1764 p h) (sat_nil p)))
def c10561 : List Lit := [(1831, false), (1761, false)]
theorem step10561 (p : Nat → Bool) (h : Constraints p) : clause p c10561 = true :=
  Snake9.LocalRup.prove_clause [c10429, c1699] c10561 (by decide) p (sat_cons (step10429 p h) (sat_cons (step1699 p h) (sat_nil p)))
def c10562 : List Lit := [(1706, false), (1719, true)]
theorem step10562 (p : Nat → Bool) (h : Constraints p) : clause p c10562 = true :=
  Snake9.LocalRup.prove_clause [c8662, c1407] c10562 (by decide) p (sat_cons (step8662 p h) (sat_cons (step1407 p h) (sat_nil p)))
def c10563 : List Lit := [(1853, true), (1832, false)]
theorem step10563 (p : Nat → Bool) (h : Constraints p) : clause p c10563 = true :=
  Snake9.LocalRup.prove_clause [c8664, c1669] c10563 (by decide) p (sat_cons (step8664 p h) (sat_cons (step1669 p h) (sat_nil p)))
def c10564 : List Lit := [(1651, false), (1662, true)]
theorem step10564 (p : Nat → Bool) (h : Constraints p) : clause p c10564 = true :=
  Snake9.LocalRup.prove_clause [c10426, c1300] c10564 (by decide) p (sat_cons (step10426 p h) (sat_cons (step1300 p h) (sat_nil p)))
def c10565 : List Lit := [(1652, false), (1663, true)]
theorem step10565 (p : Nat → Bool) (h : Constraints p) : clause p c10565 = true :=
  Snake9.LocalRup.prove_clause [c10426, c1301] c10565 (by decide) p (sat_cons (step10426 p h) (sat_cons (step1301 p h) (sat_nil p)))
def c10566 : List Lit := [(48, true), (1628, false), (1685, true)]
theorem step10566 (p : Nat → Bool) (h : Constraints p) : clause p c10566 = true :=
  Snake9.LocalRup.prove_clause [c10426, c2289] c10566 (by decide) p (sat_cons (step10426 p h) (sat_cons (step2289 p h) (sat_nil p)))
def c10567 : List Lit := [(1852, true), (1831, false)]
theorem step10567 (p : Nat → Bool) (h : Constraints p) : clause p c10567 = true :=
  Snake9.LocalRup.prove_clause [c8664, c1668] c10567 (by decide) p (sat_cons (step8664 p h) (sat_cons (step1668 p h) (sat_nil p)))
def c10568 : List Lit := [(1709, false), (114, true), (1758, true)]
theorem step10568 (p : Nat → Bool) (h : Constraints p) : clause p c10568 = true :=
  Snake9.LocalRup.prove_clause [c8660, c2638] c10568 (by decide) p (sat_cons (step8660 p h) (sat_cons (step2638 p h) (sat_nil p)))
def c10569 : List Lit := [(1714, true), (58, false), (114, true)]
theorem step10569 (p : Nat → Bool) (h : Constraints p) : clause p c10569 = true :=
  Snake9.LocalRup.prove_clause [c8660, c2876] c10569 (by decide) p (sat_cons (step8660 p h) (sat_cons (step2876 p h) (sat_nil p)))
def c10570 : List Lit := [(124, false), (46, false), (1806, true)]
theorem step10570 (p : Nat → Bool) (h : Constraints p) : clause p c10570 = true :=
  Snake9.LocalRup.prove_clause [c10428, c2971] c10570 (by decide) p (sat_cons (step10428 p h) (sat_cons (step2971 p h) (sat_nil p)))
def c10571 : List Lit := [(1709, false), (1759, true), (1737, false), (114, true)]
theorem step10571 (p : Nat → Bool) (h : Constraints p) : clause p c10571 = true :=
  Snake9.LocalRup.prove_clause [c8660, c2890] c10571 (by decide) p (sat_cons (step8660 p h) (sat_cons (step2890 p h) (sat_nil p)))
def c10572 : List Lit := [(1712, true), (58, false), (114, true), (1706, false), (1737, false), (1760, true)]
theorem step10572 (p : Nat → Bool) (h : Constraints p) : clause p c10572 = true :=
  Snake9.LocalRup.prove_clause [c8660, c2885] c10572 (by decide) p (sat_cons (step8660 p h) (sat_cons (step2885 p h) (sat_nil p)))
def c10573 : List Lit := [(1584, false), (1686, true), (1644, false)]
theorem step10573 (p : Nat → Bool) (h : Constraints p) : clause p c10573 = true :=
  Snake9.LocalRup.prove_clause [c10426, c2811] c10573 (by decide) p (sat_cons (step10426 p h) (sat_cons (step2811 p h) (sat_nil p)))
def c10574 : List Lit := [(1584, false), (1687, true), (1644, false), (122, false)]
theorem step10574 (p : Nat → Bool) (h : Constraints p) : clause p c10574 = true :=
  Snake9.LocalRup.prove_clause [c10426, c2902] c10574 (by decide) p (sat_cons (step10426 p h) (sat_cons (step2902 p h) (sat_nil p)))
def c10575 : List Lit := [(1720, true), (114, true), (1644, true), (86, false)]
theorem step10575 (p : Nat → Bool) (h : Constraints p) : clause p c10575 = true :=
  Snake9.LocalRup.prove_clause [c8660, c3656] c10575 (by decide) p (sat_cons (step8660 p h) (sat_cons (step3656 p h) (sat_nil p)))
def c10576 : List Lit := [(1709, false), (114, true), (86, true), (1760, true), (1737, false)]
theorem step10576 (p : Nat → Bool) (h : Constraints p) : clause p c10576 = true :=
  Snake9.LocalRup.prove_clause [c8660, c3238] c10576 (by decide) p (sat_cons (step8660 p h) (sat_cons (step3238 p h) (sat_nil p)))
def c10577 : List Lit := [(124, true), (114, true), (86, true), (107, true), (115, true), (234, true)]
theorem step10577 (p : Nat → Bool) (h : Constraints p) : clause p c10577 = true :=
  Snake9.LocalRup.prove_clause [c10428, c3751] c10577 (by decide) p (sat_cons (step10428 p h) (sat_cons (step3751 p h) (sat_nil p)))
def c10578 : List Lit := [(114, true), (1706, false), (86, true), (1761, true), (1738, false)]
theorem step10578 (p : Nat → Bool) (h : Constraints p) : clause p c10578 = true :=
  Snake9.LocalRup.prove_clause [c8660, c3688] c10578 (by decide) p (sat_cons (step8660 p h) (sat_cons (step3688 p h) (sat_nil p)))
def c10579 : List Lit := [(124, false), (1805, true)]
theorem step10579 (p : Nat → Bool) (h : Constraints p) : clause p c10579 = true :=
  Snake9.LocalRup.prove_clause [c10428, c3882] c10579 (by decide) p (sat_cons (step10428 p h) (sat_cons (step3882 p h) (sat_nil p)))
def c10580 : List Lit := [(1805, true), (115, true), (120, false)]
theorem step10580 (p : Nat → Bool) (h : Constraints p) : clause p c10580 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4082] c10580 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4082 p h) (sat_nil p)))
def c10581 : List Lit := [(1805, true), (120, false), (93, false)]
theorem step10581 (p : Nat → Bool) (h : Constraints p) : clause p c10581 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4141] c10581 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4141 p h) (sat_nil p)))
def c10582 : List Lit := [(114, true), (121, false), (120, false), (1830, true), (107, true), (234, true), (1818, true), (115, true), (119, true), (86, true), (1775, false), (117, false), (92, false)]
theorem step10582 (p : Nat → Bool) (h : Constraints p) : clause p c10582 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4104] c10582 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4104 p h) (sat_nil p)))
def c10583 : List Lit := [(1738, false), (114, true), (86, true), (1749, true), (1803, true), (1761, true)]
theorem step10583 (p : Nat → Bool) (h : Constraints p) : clause p c10583 = true :=
  Snake9.LocalRup.prove_clause [c8660, c4588] c10583 (by decide) p (sat_cons (step8660 p h) (sat_cons (step4588 p h) (sat_nil p)))
def c10584 : List Lit := [(42, true), (1623, true), (115, true)]
theorem step10584 (p : Nat → Bool) (h : Constraints p) : clause p c10584 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4741] c10584 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4741 p h) (sat_nil p)))
def c10585 : List Lit := [(114, true), (109, false), (117, false), (115, true), (1623, true)]
theorem step10585 (p : Nat → Bool) (h : Constraints p) : clause p c10585 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4794] c10585 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4794 p h) (sat_nil p)))
def c10586 : List Lit := [(112, false), (1623, true), (117, false), (37, true), (92, false)]
theorem step10586 (p : Nat → Bool) (h : Constraints p) : clause p c10586 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4728] c10586 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4728 p h) (sat_nil p)))
def c10587 : List Lit := [(1622, true), (1803, true)]
theorem step10587 (p : Nat → Bool) (h : Constraints p) : clause p c10587 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4737] c10587 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4737 p h) (sat_nil p)))
def c10588 : List Lit := [(42, true), (1623, true), (37, true)]
theorem step10588 (p : Nat → Bool) (h : Constraints p) : clause p c10588 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4725] c10588 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4725 p h) (sat_nil p)))
def c10589 : List Lit := [(35, true), (1622, true), (89, false), (120, false), (1623, true)]
theorem step10589 (p : Nat → Bool) (h : Constraints p) : clause p c10589 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4273] c10589 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4273 p h) (sat_nil p)))
def c10590 : List Lit := [(35, true), (119, true), (120, false), (1622, true)]
theorem step10590 (p : Nat → Bool) (h : Constraints p) : clause p c10590 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4275] c10590 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4275 p h) (sat_nil p)))
def c10591 : List Lit := [(35, true), (119, true), (1612, false), (1623, true), (120, false)]
theorem step10591 (p : Nat → Bool) (h : Constraints p) : clause p c10591 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4519] c10591 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4519 p h) (sat_nil p)))
def c10592 : List Lit := [(1623, true), (37, true), (1686, true), (92, false), (125, false), (119, true), (1803, true), (120, false)]
theorem step10592 (p : Nat → Bool) (h : Constraints p) : clause p c10592 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4943] c10592 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4943 p h) (sat_nil p)))
def c10593 : List Lit := [(1609, true), (35, false), (1803, true), (37, true), (119, true), (1623, true)]
theorem step10593 (p : Nat → Bool) (h : Constraints p) : clause p c10593 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4627] c10593 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4627 p h) (sat_nil p)))
def c10594 : List Lit := [(1832, false), (1738, false), (1803, true), (1622, false)]
theorem step10594 (p : Nat → Bool) (h : Constraints p) : clause p c10594 = true :=
  Snake9.LocalRup.prove_clause [c8661, c4440] c10594 (by decide) p (sat_cons (step8661 p h) (sat_cons (step4440 p h) (sat_nil p)))
def c10595 : List Lit := [(1709, false), (1759, true), (125, false), (93, true)]
theorem step10595 (p : Nat → Bool) (h : Constraints p) : clause p c10595 = true :=
  Snake9.LocalRup.prove_clause [c8660, c4378] c10595 (by decide) p (sat_cons (step8660 p h) (sat_cons (step4378 p h) (sat_nil p)))
def c10596 : List Lit := [(75, true), (77, false), (1715, true), (117, false)]
theorem step10596 (p : Nat → Bool) (h : Constraints p) : clause p c10596 = true :=
  Snake9.LocalRup.prove_clause [c8660, c4873] c10596 (by decide) p (sat_cons (step8660 p h) (sat_cons (step4873 p h) (sat_nil p)))
def c10597 : List Lit := [(73, false), (77, false), (125, false)]
theorem step10597 (p : Nat → Bool) (h : Constraints p) : clause p c10597 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4091] c10597 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4091 p h) (sat_nil p)))
def c10598 : List Lit := [(51, false), (1632, false), (1617, false), (1686, true), (92, false), (1623, true)]
theorem step10598 (p : Nat → Bool) (h : Constraints p) : clause p c10598 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4729] c10598 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4729 p h) (sat_nil p)))
def c10599 : List Lit := [(1738, false), (1706, false), (1803, true), (1760, true)]
theorem step10599 (p : Nat → Bool) (h : Constraints p) : clause p c10599 = true :=
  Snake9.LocalRup.prove_clause [c8661, c4421] c10599 (by decide) p (sat_cons (step8661 p h) (sat_cons (step4421 p h) (sat_nil p)))
def c10600 : List Lit := [(27, true), (1628, true), (125, false)]
theorem step10600 (p : Nat → Bool) (h : Constraints p) : clause p c10600 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4679] c10600 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4679 p h) (sat_nil p)))
def c10601 : List Lit := [(93, false), (1644, true), (107, false)]
theorem step10601 (p : Nat → Bool) (h : Constraints p) : clause p c10601 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4663] c10601 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4663 p h) (sat_nil p)))
def c10602 : List Lit := [(1819, true), (1805, false), (107, false), (1803, false), (117, true)]
theorem step10602 (p : Nat → Bool) (h : Constraints p) : clause p c10602 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4669] c10602 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4669 p h) (sat_nil p)))
def c10603 : List Lit := [(114, true), (109, false), (107, false), (115, true), (1805, true)]
theorem step10603 (p : Nat → Bool) (h : Constraints p) : clause p c10603 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4798] c10603 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4798 p h) (sat_nil p)))
def c10604 : List Lit := [(109, false), (114, true), (117, false), (107, false), (115, true)]
theorem step10604 (p : Nat → Bool) (h : Constraints p) : clause p c10604 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4078] c10604 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4078 p h) (sat_nil p)))
def c10605 : List Lit := [(72, false), (46, true), (115, true), (114, true), (1644, false), (92, false), (1623, true), (1687, true), (109, false)]
theorem step10605 (p : Nat → Bool) (h : Constraints p) : clause p c10605 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4792] c10605 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4792 p h) (sat_nil p)))
def c10606 : List Lit := [(1720, true), (114, true), (1644, true)]
theorem step10606 (p : Nat → Bool) (h : Constraints p) : clause p c10606 = true :=
  Snake9.LocalRup.prove_clause [c8661, c4695] c10606 (by decide) p (sat_cons (step8661 p h) (sat_cons (step4695 p h) (sat_nil p)))
def c10607 : List Lit := [(1622, true), (38, false)]
theorem step10607 (p : Nat → Bool) (h : Constraints p) : clause p c10607 = true :=
  Snake9.LocalRup.prove_clause [c10424, c4698] c10607 (by decide) p (sat_cons (step10424 p h) (sat_cons (step4698 p h) (sat_nil p)))
def c10608 : List Lit := [(118, false), (107, false), (117, false)]
theorem step10608 (p : Nat → Bool) (h : Constraints p) : clause p c10608 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4670] c10608 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4670 p h) (sat_nil p)))
def c10609 : List Lit := [(114, true), (109, false), (1805, true), (115, true), (234, true), (107, true)]
theorem step10609 (p : Nat → Bool) (h : Constraints p) : clause p c10609 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4795] c10609 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4795 p h) (sat_nil p)))
def c10610 : List Lit := [(109, true), (1782, true), (1805, false), (1803, false), (117, true), (92, false), (1775, false), (1831, true)]
theorem step10610 (p : Nat → Bool) (h : Constraints p) : clause p c10610 = true :=
  Snake9.LocalRup.prove_clause [c10428, c4789] c10610 (by decide) p (sat_cons (step10428 p h) (sat_cons (step4789 p h) (sat_nil p)))
end B112E034
