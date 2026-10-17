import B112E205Part0001
namespace B112E205
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c715 : List Lit := [(375, false)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true :=
  Snake9.LocalRup.prove_clause [c713, c331] c715 (by decide) p (sat_cons (step713 p h) (sat_cons (step331 p h) (sat_nil p)))
def c716 : List Lit := [(317, false)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true :=
  Snake9.LocalRup.prove_clause [c714, c231] c716 (by decide) p (sat_cons (step714 p h) (sat_cons (step231 p h) (sat_nil p)))
def c717 : List Lit := [(305, false)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true :=
  Snake9.LocalRup.prove_clause [c714, c232] c717 (by decide) p (sat_cons (step714 p h) (sat_cons (step232 p h) (sat_nil p)))
def c718 : List Lit := [(373, false)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true :=
  Snake9.LocalRup.prove_clause [c715, c269] c718 (by decide) p (sat_cons (step715 p h) (sat_cons (step269 p h) (sat_nil p)))
def c719 : List Lit := [(347, false)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true :=
  Snake9.LocalRup.prove_clause [c715, c271] c719 (by decide) p (sat_cons (step715 p h) (sat_cons (step271 p h) (sat_nil p)))
def c720 : List Lit := [(315, false)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true :=
  Snake9.LocalRup.prove_clause [c716, c229] c720 (by decide) p (sat_cons (step716 p h) (sat_cons (step229 p h) (sat_nil p)))
def c721 : List Lit := [(309, false)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true :=
  Snake9.LocalRup.prove_clause [c716, c230] c721 (by decide) p (sat_cons (step716 p h) (sat_cons (step230 p h) (sat_nil p)))
def c722 : List Lit := [(303, false)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true :=
  Snake9.LocalRup.prove_clause [c717, c221] c722 (by decide) p (sat_cons (step717 p h) (sat_cons (step221 p h) (sat_nil p)))
def c723 : List Lit := [(359, false)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true :=
  Snake9.LocalRup.prove_clause [c718, c267] c723 (by decide) p (sat_cons (step718 p h) (sat_cons (step267 p h) (sat_nil p)))
def c724 : List Lit := [(345, false)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true :=
  Snake9.LocalRup.prove_clause [c719, c248] c724 (by decide) p (sat_cons (step719 p h) (sat_cons (step248 p h) (sat_nil p)))
def c725 : List Lit := [(333, false)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true :=
  Snake9.LocalRup.prove_clause [c719, c249] c725 (by decide) p (sat_cons (step719 p h) (sat_cons (step249 p h) (sat_nil p)))
def c726 : List Lit := [(313, false)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true :=
  Snake9.LocalRup.prove_clause [c720, c227] c726 (by decide) p (sat_cons (step720 p h) (sat_cons (step227 p h) (sat_nil p)))
def c727 : List Lit := [(311, false)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true :=
  Snake9.LocalRup.prove_clause [c720, c228] c727 (by decide) p (sat_cons (step720 p h) (sat_cons (step228 p h) (sat_nil p)))
def c728 : List Lit := [(307, false)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true :=
  Snake9.LocalRup.prove_clause [c721, c224] c728 (by decide) p (sat_cons (step721 p h) (sat_cons (step224 p h) (sat_nil p)))
def c729 : List Lit := [(301, false)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true :=
  Snake9.LocalRup.prove_clause [c722, c219] c729 (by decide) p (sat_cons (step722 p h) (sat_cons (step219 p h) (sat_nil p)))
def c730 : List Lit := [(357, false)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true :=
  Snake9.LocalRup.prove_clause [c723, c258] c730 (by decide) p (sat_cons (step723 p h) (sat_cons (step258 p h) (sat_nil p)))
def c731 : List Lit := [(351, false)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true :=
  Snake9.LocalRup.prove_clause [c723, c259] c731 (by decide) p (sat_cons (step723 p h) (sat_cons (step259 p h) (sat_nil p)))
def c732 : List Lit := [(343, false)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true :=
  Snake9.LocalRup.prove_clause [c724, c246] c732 (by decide) p (sat_cons (step724 p h) (sat_cons (step246 p h) (sat_nil p)))
def c733 : List Lit := [(331, false)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true :=
  Snake9.LocalRup.prove_clause [c725, c240] c733 (by decide) p (sat_cons (step725 p h) (sat_cons (step240 p h) (sat_nil p)))
def c734 : List Lit := [(162, false)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true :=
  Snake9.LocalRup.prove_clause [c726, c226] c734 (by decide) p (sat_cons (step726 p h) (sat_cons (step226 p h) (sat_nil p)))
def c735 : List Lit := [(160, false)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true :=
  Snake9.LocalRup.prove_clause [c727, c225] c735 (by decide) p (sat_cons (step727 p h) (sat_cons (step225 p h) (sat_nil p)))
def c736 : List Lit := [(158, false)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true :=
  Snake9.LocalRup.prove_clause [c728, c223] c736 (by decide) p (sat_cons (step728 p h) (sat_cons (step223 p h) (sat_nil p)))
def c737 : List Lit := [(155, false)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true :=
  Snake9.LocalRup.prove_clause [c729, c218] c737 (by decide) p (sat_cons (step729 p h) (sat_cons (step218 p h) (sat_nil p)))
def c738 : List Lit := [(355, false)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true :=
  Snake9.LocalRup.prove_clause [c730, c256] c738 (by decide) p (sat_cons (step730 p h) (sat_cons (step256 p h) (sat_nil p)))
def c739 : List Lit := [(353, false)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true :=
  Snake9.LocalRup.prove_clause [c730, c257] c739 (by decide) p (sat_cons (step730 p h) (sat_cons (step257 p h) (sat_nil p)))
def c740 : List Lit := [(349, false)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true :=
  Snake9.LocalRup.prove_clause [c731, c252] c740 (by decide) p (sat_cons (step731 p h) (sat_cons (step252 p h) (sat_nil p)))
def c741 : List Lit := [(341, false)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true :=
  Snake9.LocalRup.prove_clause [c732, c244] c741 (by decide) p (sat_cons (step732 p h) (sat_cons (step244 p h) (sat_nil p)))
def c742 : List Lit := [(329, false)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true :=
  Snake9.LocalRup.prove_clause [c733, c239] c742 (by decide) p (sat_cons (step733 p h) (sat_cons (step239 p h) (sat_nil p)))
def c743 : List Lit := [(46, false)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true :=
  Snake9.LocalRup.prove_clause [c737, c38] c743 (by decide) p (sat_cons (step737 p h) (sat_cons (step38 p h) (sat_nil p)))
def c744 : List Lit := [(183, false)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true :=
  Snake9.LocalRup.prove_clause [c738, c255] c744 (by decide) p (sat_cons (step738 p h) (sat_cons (step255 p h) (sat_nil p)))
def c745 : List Lit := [(181, false)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true :=
  Snake9.LocalRup.prove_clause [c739, c253] c745 (by decide) p (sat_cons (step739 p h) (sat_cons (step253 p h) (sat_nil p)))
def c746 : List Lit := [(180, false)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true :=
  Snake9.LocalRup.prove_clause [c739, c254] c746 (by decide) p (sat_cons (step739 p h) (sat_cons (step254 p h) (sat_nil p)))
def c747 : List Lit := [(178, false)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true :=
  Snake9.LocalRup.prove_clause [c740, c251] c747 (by decide) p (sat_cons (step740 p h) (sat_cons (step251 p h) (sat_nil p)))
def c748 : List Lit := [(175, false)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true :=
  Snake9.LocalRup.prove_clause [c741, c243] c748 (by decide) p (sat_cons (step741 p h) (sat_cons (step243 p h) (sat_nil p)))
def c749 : List Lit := [(168, false)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true :=
  Snake9.LocalRup.prove_clause [c742, c238] c749 (by decide) p (sat_cons (step742 p h) (sat_cons (step238 p h) (sat_nil p)))
def c750 : List Lit := [(1379, true)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true :=
  Snake9.LocalRup.prove_clause [c743, c395] c750 (by decide) p (sat_cons (step743 p h) (sat_cons (step395 p h) (sat_nil p)))
def c751 : List Lit := [(62, true)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true :=
  Snake9.LocalRup.prove_clause [c748, c708, c70] c751 (by decide) p (sat_cons (step748 p h) (sat_cons (step708 p h) (sat_cons (step70 p h) (sat_nil p))))
def c752 : List Lit := [(1381, true)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true :=
  Snake9.LocalRup.prove_clause [c750, c397] c752 (by decide) p (sat_cons (step750 p h) (sat_cons (step397 p h) (sat_nil p)))
def c753 : List Lit := [(63, false)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true :=
  Snake9.LocalRup.prove_clause [c751, c708, c707, c64] c753 (by decide) p (sat_cons (step751 p h) (sat_cons (step708 p h) (sat_cons (step707 p h) (sat_cons (step64 p h) (sat_nil p)))))
def c754 : List Lit := [(1423, true)]
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true :=
  Snake9.LocalRup.prove_clause [c753, c438] c754 (by decide) p (sat_cons (step753 p h) (sat_cons (step438 p h) (sat_nil p)))
def c755 : List Lit := [(1425, true)]
theorem step755 (p : Nat → Bool) (h : Constraints p) : clause p c755 = true :=
  Snake9.LocalRup.prove_clause [c754, c441] c755 (by decide) p (sat_cons (step754 p h) (sat_cons (step441 p h) (sat_nil p)))
def c756 : List Lit := [(1433, true)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true :=
  Snake9.LocalRup.prove_clause [c755, c452] c756 (by decide) p (sat_cons (step755 p h) (sat_cons (step452 p h) (sat_nil p)))
def c757 : List Lit := [(72, false), (57, false)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true :=
  Snake9.LocalRup.prove_clause [c745, c707, c84, c71] c757 (by decide) p (sat_cons (step745 p h) (sat_cons (step707 p h) (sat_cons (step84 p h) (sat_cons (step71 p h) (sat_nil p)))))
def c758 : List Lit := [(68, false), (57, false)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true :=
  Snake9.LocalRup.prove_clause [c751, c707, c746, c744, c646, c756, c664, c757, c458, c76, c72, c82, c527, c463, c633, c530, c483, c486, c550, c490, c491, c555, c573, c576, c578, c556, c492, c663, c487, c622] c758 (by decide) p (sat_cons (step751 p h) (sat_cons (step707 p h) (sat_cons (step746 p h) (sat_cons (step744 p h) (sat_cons (step646 p h) (sat_cons (step756 p h) (sat_cons (step664 p h) (sat_cons (step757 p h) (sat_cons (step458 p h) (sat_cons (step76 p h) (sat_cons (step72 p h) (sat_cons (step82 p h) (sat_cons (step527 p h) (sat_cons (step463 p h) (sat_cons (step633 p h) (sat_cons (step530 p h) (sat_cons (step483 p h) (sat_cons (step486 p h) (sat_cons (step550 p h) (sat_cons (step490 p h) (sat_cons (step491 p h) (sat_cons (step555 p h) (sat_cons (step573 p h) (sat_cons (step576 p h) (sat_cons (step578 p h) (sat_cons (step556 p h) (sat_cons (step492 p h) (sat_cons (step663 p h) (sat_cons (step487 p h) (sat_cons (step622 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c759 : List Lit := [(1502, false), (57, false)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true :=
  Snake9.LocalRup.prove_clause [c744, c172, c706, c747, c707, c171, c746, c173, c753, c646, c757, c458, c460, c479, c758, c77, c80, c81, c89, c85, c88, c67, c440, c442, c455, c494, c573, c556, c559, c576, c519, c495, c622, c480] c759 (by decide) p (sat_cons (step744 p h) (sat_cons (step172 p h) (sat_cons (step706 p h) (sat_cons (step747 p h) (sat_cons (step707 p h) (sat_cons (step171 p h) (sat_cons (step746 p h) (sat_cons (step173 p h) (sat_cons (step753 p h) (sat_cons (step646 p h) (sat_cons (step757 p h) (sat_cons (step458 p h) (sat_cons (step460 p h) (sat_cons (step479 p h) (sat_cons (step758 p h) (sat_cons (step77 p h) (sat_cons (step80 p h) (sat_cons (step81 p h) (sat_cons (step89 p h) (sat_cons (step85 p h) (sat_cons (step88 p h) (sat_cons (step67 p h) (sat_cons (step440 p h) (sat_cons (step442 p h) (sat_cons (step455 p h) (sat_cons (step494 p h) (sat_cons (step573 p h) (sat_cons (step556 p h) (sat_cons (step559 p h) (sat_cons (step576 p h) (sat_cons (step519 p h) (sat_cons (step495 p h) (sat_cons (step622 p h) (sat_cons (step480 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c760 : List Lit := [(57, false)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true :=
  Snake9.LocalRup.prove_clause [c172, c707, c747, c171, c746, c173, c744, c706, c753, c664, c646, c757, c85, c458, c460, c479, c758, c77, c80, c81, c89, c88, c69, c67, c532, c440, c550, c442, c455, c494, c573, c759, c551, c663, c651, c622, c511, c480, c516, c495, c558, c576] c760 (by decide) p (sat_cons (step172 p h) (sat_cons (step707 p h) (sat_cons (step747 p h) (sat_cons (step171 p h) (sat_cons (step746 p h) (sat_cons (step173 p h) (sat_cons (step744 p h) (sat_cons (step706 p h) (sat_cons (step753 p h) (sat_cons (step664 p h) (sat_cons (step646 p h) (sat_cons (step757 p h) (sat_cons (step85 p h) (sat_cons (step458 p h) (sat_cons (step460 p h) (sat_cons (step479 p h) (sat_cons (step758 p h) (sat_cons (step77 p h) (sat_cons (step80 p h) (sat_cons (step81 p h) (sat_cons (step89 p h) (sat_cons (step88 p h) (sat_cons (step69 p h) (sat_cons (step67 p h) (sat_cons (step532 p h) (sat_cons (step440 p h) (sat_cons (step550 p h) (sat_cons (step442 p h) (sat_cons (step455 p h) (sat_cons (step494 p h) (sat_cons (step573 p h) (sat_cons (step759 p h) (sat_cons (step551 p h) (sat_cons (step663 p h) (sat_cons (step651 p h) (sat_cons (step622 p h) (sat_cons (step511 p h) (sat_cons (step480 p h) (sat_cons (step516 p h) (sat_cons (step495 p h) (sat_cons (step558 p h) (sat_cons (step576 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c761 : List Lit := [(48, false)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true :=
  Snake9.LocalRup.prove_clause [c760, c165, c40] c761 (by decide) p (sat_cons (step760 p h) (sat_cons (step165 p h) (sat_cons (step40 p h) (sat_nil p))))
def c762 : List Lit := [(58, false)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true :=
  Snake9.LocalRup.prove_clause [c760, c169, c56] c762 (by decide) p (sat_cons (step760 p h) (sat_cons (step169 p h) (sat_cons (step56 p h) (sat_nil p))))
def c763 : List Lit := [(49, false)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true :=
  Snake9.LocalRup.prove_clause [c761, c736, c41] c763 (by decide) p (sat_cons (step761 p h) (sat_cons (step736 p h) (sat_cons (step41 p h) (sat_nil p))))
def c764 : List Lit := [(59, false)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true :=
  Snake9.LocalRup.prove_clause [c762, c749, c58] c764 (by decide) p (sat_cons (step762 p h) (sat_cons (step749 p h) (sat_cons (step58 p h) (sat_nil p))))
def c765 : List Lit := [(50, false)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true :=
  Snake9.LocalRup.prove_clause [c763, c166, c743, c43] c765 (by decide) p (sat_cons (step763 p h) (sat_cons (step166 p h) (sat_cons (step743 p h) (sat_cons (step43 p h) (sat_nil p)))))
def c766 : List Lit := [(1426, true)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true :=
  Snake9.LocalRup.prove_clause [c764, c754, c444] c766 (by decide) p (sat_cons (step764 p h) (sat_cons (step754 p h) (sat_cons (step444 p h) (sat_nil p))))
def c767 : List Lit := [(51, false)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true :=
  Snake9.LocalRup.prove_clause [c765, c735, c45] c767 (by decide) p (sat_cons (step765 p h) (sat_cons (step735 p h) (sat_cons (step45 p h) (sat_nil p))))
def c768 : List Lit := [(1434, true)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true :=
  Snake9.LocalRup.prove_clause [c766, c455] c768 (by decide) p (sat_cons (step766 p h) (sat_cons (step455 p h) (sat_nil p)))
def c769 : List Lit := [(54, false)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true :=
  Snake9.LocalRup.prove_clause [c767, c168, c50] c769 (by decide) p (sat_cons (step767 p h) (sat_cons (step168 p h) (sat_cons (step50 p h) (sat_nil p))))
def c770 : List Lit := [(1385, true)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true :=
  Snake9.LocalRup.prove_clause [c767, c763, c402] c770 (by decide) p (sat_cons (step767 p h) (sat_cons (step763 p h) (sat_cons (step402 p h) (sat_nil p))))
def c771 : List Lit := [(53, false)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true :=
  Snake9.LocalRup.prove_clause [c769, c590, c734, c47] c771 (by decide) p (sat_cons (step769 p h) (sat_cons (step590 p h) (sat_cons (step734 p h) (sat_cons (step47 p h) (sat_nil p)))))
def c772 : List Lit := [(1387, true)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true :=
  Snake9.LocalRup.prove_clause [c771, c760, c404] c772 (by decide) p (sat_cons (step771 p h) (sat_cons (step760 p h) (sat_cons (step404 p h) (sat_nil p))))
def c773 : List Lit := [(1391, true)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true :=
  Snake9.LocalRup.prove_clause [c772, c770, c410] c773 (by decide) p (sat_cons (step772 p h) (sat_cons (step770 p h) (sat_cons (step410 p h) (sat_nil p))))
def c774 : List Lit := [(1396, true)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true :=
  Snake9.LocalRup.prove_clause [c773, c752, c415] c774 (by decide) p (sat_cons (step773 p h) (sat_cons (step752 p h) (sat_cons (step415 p h) (sat_nil p))))
def c775 : List Lit := [(1404, true)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true :=
  Snake9.LocalRup.prove_clause [c774, c616, c424] c775 (by decide) p (sat_cons (step774 p h) (sat_cons (step616 p h) (sat_cons (step424 p h) (sat_nil p))))
def c776 : List Lit := [(1417, true)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true :=
  Snake9.LocalRup.prove_clause [c775, c619, c430] c776 (by decide) p (sat_cons (step775 p h) (sat_cons (step619 p h) (sat_cons (step430 p h) (sat_nil p))))
def c777 : List Lit := [(1523, false)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true :=
  Snake9.LocalRup.prove_clause [c776, c584, c582] c777 (by decide) p (sat_cons (step776 p h) (sat_cons (step584 p h) (sat_cons (step582 p h) (sat_nil p))))
def c778 : List Lit := [(1509, false)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true :=
  Snake9.LocalRup.prove_clause [c777, c628, c568] c778 (by decide) p (sat_cons (step777 p h) (sat_cons (step628 p h) (sat_cons (step568 p h) (sat_nil p))))
end B112E205
