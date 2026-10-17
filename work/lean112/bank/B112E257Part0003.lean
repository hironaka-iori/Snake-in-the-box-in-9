import B112E257Part0002
namespace B112E257
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1710 : List Lit := [(73, true), (24, true), (32, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c571, c166] c1710 (by decide) p (sat_cons (step571 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1711 : List Lit := [(33, true), (24, true), (32, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c571, c167] c1711 (by decide) p (sat_cons (step571 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1712 : List Lit := [(76, true), (35, true), (34, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c572, c174] c1712 (by decide) p (sat_cons (step572 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1713 : List Lit := [(17, true), (76, true), (34, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c572, c175] c1713 (by decide) p (sat_cons (step572 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1714 : List Lit := [(17, true), (35, true), (34, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c572, c176] c1714 (by decide) p (sat_cons (step572 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1715 : List Lit := [(38, true), (37, true), (40, false), (39, true)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c573, c204] c1715 (by decide) p (sat_cons (step573 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1716 : List Lit := [(38, true), (5, true), (40, false), (39, true)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c573, c205] c1716 (by decide) p (sat_cons (step573 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1717 : List Lit := [(37, true), (5, true), (40, false), (39, true)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c573, c206] c1717 (by decide) p (sat_cons (step573 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1718 : List Lit := [(37, true), (5, true), (40, false), (38, true)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c573, c207] c1718 (by decide) p (sat_cons (step573 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1719 : List Lit := [(53, true), (41, true), (42, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c574, c214] c1719 (by decide) p (sat_cons (step574 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1720 : List Lit := [(37, true), (53, true), (42, false)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c574, c215] c1720 (by decide) p (sat_cons (step574 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1721 : List Lit := [(37, true), (42, false), (41, true)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c574, c216] c1721 (by decide) p (sat_cons (step574 p h) (sat_cons (step216 p h) (sat_nil p)))
def c1722 : List Lit := [(38, true), (55, true), (43, true), (44, false), (65, true)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c575, c225] c1722 (by decide) p (sat_cons (step575 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1723 : List Lit := [(43, true), (8, true), (55, true), (44, false), (65, true)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c575, c226] c1723 (by decide) p (sat_cons (step575 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1724 : List Lit := [(38, true), (55, true), (44, false), (43, true), (8, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c575, c227] c1724 (by decide) p (sat_cons (step575 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1725 : List Lit := [(36, true), (67, true), (46, false), (47, true), (51, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c576, c239] c1725 (by decide) p (sat_cons (step576 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1726 : List Lit := [(51, true), (10, true), (46, false), (47, true), (67, true)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c576, c240] c1726 (by decide) p (sat_cons (step576 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1727 : List Lit := [(36, true), (51, true), (46, false), (47, true), (10, true)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c576, c241] c1727 (by decide) p (sat_cons (step576 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1728 : List Lit := [(53, true), (69, true), (47, true), (48, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c577, c255] c1728 (by decide) p (sat_cons (step577 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1729 : List Lit := [(53, true), (69, true), (37, true), (48, false)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c577, c256] c1729 (by decide) p (sat_cons (step577 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1730 : List Lit := [(69, true), (37, true), (47, true), (48, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c577, c257] c1730 (by decide) p (sat_cons (step577 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1731 : List Lit := [(47, true), (53, true), (37, true), (48, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c577, c258] c1731 (by decide) p (sat_cons (step577 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1732 : List Lit := [(38, true), (55, true), (49, false), (47, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c578, c261] c1732 (by decide) p (sat_cons (step578 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1733 : List Lit := [(55, true), (38, true), (13, true), (49, false)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c578, c262] c1733 (by decide) p (sat_cons (step578 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1734 : List Lit := [(39, true), (56, true), (50, false)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c579, c263] c1734 (by decide) p (sat_cons (step579 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1735 : List Lit := [(14, true), (56, true), (50, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c579, c264] c1735 (by decide) p (sat_cons (step579 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1736 : List Lit := [(14, true), (39, true), (50, false)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c579, c265] c1736 (by decide) p (sat_cons (step579 p h) (sat_cons (step265 p h) (sat_nil p)))
def c1737 : List Lit := [(53, true), (51, true), (52, false), (55, true), (73, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c580, c284] c1737 (by decide) p (sat_cons (step580 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1738 : List Lit := [(53, true), (47, true), (52, false), (55, true), (73, true)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c580, c285] c1738 (by decide) p (sat_cons (step580 p h) (sat_cons (step285 p h) (sat_nil p)))
def c1739 : List Lit := [(51, true), (73, true), (52, false), (55, true), (47, true)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c580, c286] c1739 (by decide) p (sat_cons (step580 p h) (sat_cons (step286 p h) (sat_nil p)))
def c1740 : List Lit := [(53, true), (47, true), (52, false), (51, true), (73, true)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c580, c287] c1740 (by decide) p (sat_cons (step580 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1741 : List Lit := [(53, true), (47, true), (52, false), (51, true), (55, true)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c580, c288] c1741 (by decide) p (sat_cons (step580 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1742 : List Lit := [(43, true), (55, true), (76, true), (54, false), (56, true), (51, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c581, c307] c1742 (by decide) p (sat_cons (step581 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1743 : List Lit := [(17, true), (51, true), (43, true), (55, true), (54, false), (56, true)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c581, c308] c1743 (by decide) p (sat_cons (step581 p h) (sat_cons (step308 p h) (sat_nil p)))
def c1744 : List Lit := [(65, true), (57, true), (59, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c582, c322] c1744 (by decide) p (sat_cons (step582 p h) (sat_cons (step322 p h) (sat_nil p)))
def c1745 : List Lit := [(38, true), (65, true), (59, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c582, c323] c1745 (by decide) p (sat_cons (step582 p h) (sat_cons (step323 p h) (sat_nil p)))
def c1746 : List Lit := [(38, true), (57, true), (59, false)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c582, c324] c1746 (by decide) p (sat_cons (step582 p h) (sat_cons (step324 p h) (sat_nil p)))
def c1747 : List Lit := [(58, true), (60, false), (39, true)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c583, c326] c1747 (by decide) p (sat_cons (step583 p h) (sat_cons (step326 p h) (sat_nil p)))
def c1748 : List Lit := [(58, true), (60, false), (22, true)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c583, c327] c1748 (by decide) p (sat_cons (step583 p h) (sat_cons (step327 p h) (sat_nil p)))
def c1749 : List Lit := [(22, true), (60, false), (39, true)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c583, c328] c1749 (by decide) p (sat_cons (step583 p h) (sat_cons (step328 p h) (sat_nil p)))
def c1750 : List Lit := [(57, true), (65, true), (62, false), (61, true), (73, true)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c584, c346] c1750 (by decide) p (sat_cons (step584 p h) (sat_cons (step346 p h) (sat_nil p)))
def c1751 : List Lit := [(24, true), (65, true), (62, false), (61, true), (73, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c584, c347] c1751 (by decide) p (sat_cons (step584 p h) (sat_cons (step347 p h) (sat_nil p)))
def c1752 : List Lit := [(57, true), (65, true), (24, true), (62, false), (61, true)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c584, c348] c1752 (by decide) p (sat_cons (step584 p h) (sat_cons (step348 p h) (sat_nil p)))
def c1753 : List Lit := [(65, true), (76, true), (61, true), (64, false)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c585, c350] c1753 (by decide) p (sat_cons (step585 p h) (sat_cons (step350 p h) (sat_nil p)))
def c1754 : List Lit := [(43, true), (76, true), (64, false), (61, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c585, c351] c1754 (by decide) p (sat_cons (step585 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1755 : List Lit := [(65, true), (43, true), (61, true), (64, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c585, c352] c1755 (by decide) p (sat_cons (step585 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1756 : List Lit := [(66, true), (181, true), (64, true), (26, true), (62, true), (65, false), (44, true)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c1520, c371] c1756 (by decide) p (sat_cons (step1520 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1757 : List Lit := [(77, true), (65, true), (66, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c586, c372] c1757 (by decide) p (sat_cons (step586 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1758 : List Lit := [(77, true), (27, true), (66, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c586, c373] c1758 (by decide) p (sat_cons (step586 p h) (sat_cons (step373 p h) (sat_nil p)))
def c1759 : List Lit := [(65, true), (27, true), (66, false)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c586, c374] c1759 (by decide) p (sat_cons (step586 p h) (sat_cons (step374 p h) (sat_nil p)))
def c1760 : List Lit := [(58, true), (74, true), (68, false), (69, true), (67, true)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c587, c389] c1760 (by decide) p (sat_cons (step587 p h) (sat_cons (step389 p h) (sat_nil p)))
def c1761 : List Lit := [(70, false), (76, true)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c588, c398] c1761 (by decide) p (sat_cons (step588 p h) (sat_cons (step398 p h) (sat_nil p)))
def c1762 : List Lit := [(70, false), (67, true)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c588, c399] c1762 (by decide) p (sat_cons (step588 p h) (sat_cons (step399 p h) (sat_nil p)))
def c1763 : List Lit := [(77, true), (71, false), (69, true)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c589, c401] c1763 (by decide) p (sat_cons (step589 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1764 : List Lit := [(31, true), (77, true), (71, false)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c589, c402] c1764 (by decide) p (sat_cons (step589 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1765 : List Lit := [(31, true), (69, true), (71, false)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c589, c403] c1765 (by decide) p (sat_cons (step589 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1766 : List Lit := [(67, true), (74, true), (72, false), (61, true), (73, true), (76, true), (78, true)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c590, c413] c1766 (by decide) p (sat_cons (step590 p h) (sat_cons (step413 p h) (sat_nil p)))
def c1767 : List Lit := [(74, true), (76, true), (72, false), (61, true), (51, true), (73, true), (78, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c590, c414] c1767 (by decide) p (sat_cons (step590 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1768 : List Lit := [(74, true), (67, true), (72, false), (51, true), (61, true), (76, true), (78, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c590, c415] c1768 (by decide) p (sat_cons (step590 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1769 : List Lit := [(67, true), (76, true), (72, false), (51, true), (61, true), (73, true), (78, true)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c590, c416] c1769 (by decide) p (sat_cons (step590 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1770 : List Lit := [(67, true), (74, true), (72, false), (51, true), (61, true), (73, true), (78, true)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c590, c417] c1770 (by decide) p (sat_cons (step590 p h) (sat_cons (step417 p h) (sat_nil p)))
def c1771 : List Lit := [(67, true), (74, true), (72, false), (51, true), (61, true), (73, true), (76, true)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c590, c418] c1771 (by decide) p (sat_cons (step590 p h) (sat_cons (step418 p h) (sat_nil p)))
def c1772 : List Lit := [(79, false), (97, true)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c591, c465] c1772 (by decide) p (sat_cons (step591 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1773 : List Lit := [(79, false), (80, true)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c591, c466] c1773 (by decide) p (sat_cons (step591 p h) (sat_cons (step466 p h) (sat_nil p)))
end B112E257
