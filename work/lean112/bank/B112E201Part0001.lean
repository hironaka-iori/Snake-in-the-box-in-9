import B112E201Part0000
namespace B112E201
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c736 : List Lit := [(323, true)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true :=
  Snake9.LocalRup.prove_clause [c734, c318] c736 (by decide) p (sat_cons (step734 p h) (sat_cons (step318 p h) (sat_nil p)))
def c737 : List Lit := [(321, false)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true :=
  Snake9.LocalRup.prove_clause [c734, c677, c319] c737 (by decide) p (sat_cons (step734 p h) (sat_cons (step677 p h) (sat_cons (step319 p h) (sat_nil p))))
def c738 : List Lit := [(265, false)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true :=
  Snake9.LocalRup.prove_clause [c735, c272] c738 (by decide) p (sat_cons (step735 p h) (sat_cons (step272 p h) (sat_nil p)))
def c739 : List Lit := [(253, false)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true :=
  Snake9.LocalRup.prove_clause [c735, c273] c739 (by decide) p (sat_cons (step735 p h) (sat_cons (step273 p h) (sat_nil p)))
def c740 : List Lit := [(429, false)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true :=
  Snake9.LocalRup.prove_clause [c736, c415, c413] c740 (by decide) p (sat_cons (step736 p h) (sat_cons (step415 p h) (sat_cons (step413 p h) (sat_nil p))))
def c741 : List Lit := [(319, false)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true :=
  Snake9.LocalRup.prove_clause [c737, c312] c741 (by decide) p (sat_cons (step737 p h) (sat_cons (step312 p h) (sat_nil p)))
def c742 : List Lit := [(293, false)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true :=
  Snake9.LocalRup.prove_clause [c737, c313] c742 (by decide) p (sat_cons (step737 p h) (sat_cons (step313 p h) (sat_nil p)))
def c743 : List Lit := [(263, false)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true :=
  Snake9.LocalRup.prove_clause [c738, c270] c743 (by decide) p (sat_cons (step738 p h) (sat_cons (step270 p h) (sat_nil p)))
def c744 : List Lit := [(257, false)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true :=
  Snake9.LocalRup.prove_clause [c738, c271] c744 (by decide) p (sat_cons (step738 p h) (sat_cons (step271 p h) (sat_nil p)))
def c745 : List Lit := [(251, false)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true :=
  Snake9.LocalRup.prove_clause [c739, c262] c745 (by decide) p (sat_cons (step739 p h) (sat_cons (step262 p h) (sat_nil p)))
def c746 : List Lit := [(245, false)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true :=
  Snake9.LocalRup.prove_clause [c739, c263] c746 (by decide) p (sat_cons (step739 p h) (sat_cons (step263 p h) (sat_nil p)))
def c747 : List Lit := [(427, false)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true :=
  Snake9.LocalRup.prove_clause [c740, c408] c747 (by decide) p (sat_cons (step740 p h) (sat_cons (step408 p h) (sat_nil p)))
def c748 : List Lit := [(375, false)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true :=
  Snake9.LocalRup.prove_clause [c740, c410] c748 (by decide) p (sat_cons (step740 p h) (sat_cons (step410 p h) (sat_nil p)))
def c749 : List Lit := [(317, false)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true :=
  Snake9.LocalRup.prove_clause [c741, c310] c749 (by decide) p (sat_cons (step741 p h) (sat_cons (step310 p h) (sat_nil p)))
def c750 : List Lit := [(305, false)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true :=
  Snake9.LocalRup.prove_clause [c741, c311] c750 (by decide) p (sat_cons (step741 p h) (sat_cons (step311 p h) (sat_nil p)))
def c751 : List Lit := [(291, false)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true :=
  Snake9.LocalRup.prove_clause [c742, c291] c751 (by decide) p (sat_cons (step742 p h) (sat_cons (step291 p h) (sat_nil p)))
def c752 : List Lit := [(279, false)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true :=
  Snake9.LocalRup.prove_clause [c742, c293] c752 (by decide) p (sat_cons (step742 p h) (sat_cons (step293 p h) (sat_nil p)))
def c753 : List Lit := [(261, false)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true :=
  Snake9.LocalRup.prove_clause [c743, c268] c753 (by decide) p (sat_cons (step743 p h) (sat_cons (step268 p h) (sat_nil p)))
def c754 : List Lit := [(259, false)]
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true :=
  Snake9.LocalRup.prove_clause [c743, c269] c754 (by decide) p (sat_cons (step743 p h) (sat_cons (step269 p h) (sat_nil p)))
def c755 : List Lit := [(255, false)]
theorem step755 (p : Nat → Bool) (h : Constraints p) : clause p c755 = true :=
  Snake9.LocalRup.prove_clause [c744, c265] c755 (by decide) p (sat_cons (step744 p h) (sat_cons (step265 p h) (sat_nil p)))
def c756 : List Lit := [(249, false)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true :=
  Snake9.LocalRup.prove_clause [c745, c261] c756 (by decide) p (sat_cons (step745 p h) (sat_cons (step261 p h) (sat_nil p)))
def c757 : List Lit := [(243, false)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true :=
  Snake9.LocalRup.prove_clause [c746, c257] c757 (by decide) p (sat_cons (step746 p h) (sat_cons (step257 p h) (sat_nil p)))
def c758 : List Lit := [(123, false)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true :=
  Snake9.LocalRup.prove_clause [c746, c258] c758 (by decide) p (sat_cons (step746 p h) (sat_cons (step258 p h) (sat_nil p)))
def c759 : List Lit := [(425, false)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true :=
  Snake9.LocalRup.prove_clause [c747, c405] c759 (by decide) p (sat_cons (step747 p h) (sat_cons (step405 p h) (sat_nil p)))
def c760 : List Lit := [(399, false)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true :=
  Snake9.LocalRup.prove_clause [c747, c406] c760 (by decide) p (sat_cons (step747 p h) (sat_cons (step406 p h) (sat_nil p)))
def c761 : List Lit := [(373, false)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true :=
  Snake9.LocalRup.prove_clause [c748, c366] c761 (by decide) p (sat_cons (step748 p h) (sat_cons (step366 p h) (sat_nil p)))
def c762 : List Lit := [(347, false)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true :=
  Snake9.LocalRup.prove_clause [c748, c368] c762 (by decide) p (sat_cons (step748 p h) (sat_cons (step368 p h) (sat_nil p)))
def c763 : List Lit := [(315, false)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true :=
  Snake9.LocalRup.prove_clause [c749, c308] c763 (by decide) p (sat_cons (step749 p h) (sat_cons (step308 p h) (sat_nil p)))
def c764 : List Lit := [(309, false)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true :=
  Snake9.LocalRup.prove_clause [c749, c309] c764 (by decide) p (sat_cons (step749 p h) (sat_cons (step309 p h) (sat_nil p)))
def c765 : List Lit := [(303, false)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true :=
  Snake9.LocalRup.prove_clause [c750, c300] c765 (by decide) p (sat_cons (step750 p h) (sat_cons (step300 p h) (sat_nil p)))
def c766 : List Lit := [(297, false)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true :=
  Snake9.LocalRup.prove_clause [c750, c301] c766 (by decide) p (sat_cons (step750 p h) (sat_cons (step301 p h) (sat_nil p)))
def c767 : List Lit := [(289, false)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true :=
  Snake9.LocalRup.prove_clause [c751, c288] c767 (by decide) p (sat_cons (step751 p h) (sat_cons (step288 p h) (sat_nil p)))
def c768 : List Lit := [(283, false)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true :=
  Snake9.LocalRup.prove_clause [c751, c289] c768 (by decide) p (sat_cons (step751 p h) (sat_cons (step289 p h) (sat_nil p)))
def c769 : List Lit := [(277, false)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true :=
  Snake9.LocalRup.prove_clause [c752, c279] c769 (by decide) p (sat_cons (step752 p h) (sat_cons (step279 p h) (sat_nil p)))
def c770 : List Lit := [(273, false)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true :=
  Snake9.LocalRup.prove_clause [c752, c280] c770 (by decide) p (sat_cons (step752 p h) (sat_cons (step280 p h) (sat_nil p)))
def c771 : List Lit := [(135, false)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true :=
  Snake9.LocalRup.prove_clause [c753, c267] c771 (by decide) p (sat_cons (step753 p h) (sat_cons (step267 p h) (sat_nil p)))
def c772 : List Lit := [(134, false)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true :=
  Snake9.LocalRup.prove_clause [c754, c266] c772 (by decide) p (sat_cons (step754 p h) (sat_cons (step266 p h) (sat_nil p)))
def c773 : List Lit := [(131, false)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true :=
  Snake9.LocalRup.prove_clause [c755, c264] c773 (by decide) p (sat_cons (step755 p h) (sat_cons (step264 p h) (sat_nil p)))
def c774 : List Lit := [(129, false)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true :=
  Snake9.LocalRup.prove_clause [c756, c259] c774 (by decide) p (sat_cons (step756 p h) (sat_cons (step259 p h) (sat_nil p)))
def c775 : List Lit := [(128, false)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true :=
  Snake9.LocalRup.prove_clause [c756, c260] c775 (by decide) p (sat_cons (step756 p h) (sat_cons (step260 p h) (sat_nil p)))
def c776 : List Lit := [(124, false)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true :=
  Snake9.LocalRup.prove_clause [c757, c256] c776 (by decide) p (sat_cons (step757 p h) (sat_cons (step256 p h) (sat_nil p)))
def c777 : List Lit := [(423, false)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true :=
  Snake9.LocalRup.prove_clause [c759, c403] c777 (by decide) p (sat_cons (step759 p h) (sat_cons (step403 p h) (sat_nil p)))
def c778 : List Lit := [(411, false)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true :=
  Snake9.LocalRup.prove_clause [c759, c404] c778 (by decide) p (sat_cons (step759 p h) (sat_cons (step404 p h) (sat_nil p)))
def c779 : List Lit := [(397, false)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true :=
  Snake9.LocalRup.prove_clause [c760, c384] c779 (by decide) p (sat_cons (step760 p h) (sat_cons (step384 p h) (sat_nil p)))
def c780 : List Lit := [(385, false)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true :=
  Snake9.LocalRup.prove_clause [c760, c385] c780 (by decide) p (sat_cons (step760 p h) (sat_cons (step385 p h) (sat_nil p)))
def c781 : List Lit := [(371, false)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true :=
  Snake9.LocalRup.prove_clause [c761, c363] c781 (by decide) p (sat_cons (step761 p h) (sat_cons (step363 p h) (sat_nil p)))
def c782 : List Lit := [(359, false)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true :=
  Snake9.LocalRup.prove_clause [c761, c364] c782 (by decide) p (sat_cons (step761 p h) (sat_cons (step364 p h) (sat_nil p)))
def c783 : List Lit := [(345, false)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true :=
  Snake9.LocalRup.prove_clause [c762, c339] c783 (by decide) p (sat_cons (step762 p h) (sat_cons (step339 p h) (sat_nil p)))
def c784 : List Lit := [(333, false)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true :=
  Snake9.LocalRup.prove_clause [c762, c341] c784 (by decide) p (sat_cons (step762 p h) (sat_cons (step341 p h) (sat_nil p)))
def c785 : List Lit := [(313, false)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true :=
  Snake9.LocalRup.prove_clause [c763, c306] c785 (by decide) p (sat_cons (step763 p h) (sat_cons (step306 p h) (sat_nil p)))
def c786 : List Lit := [(311, false)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true :=
  Snake9.LocalRup.prove_clause [c763, c307] c786 (by decide) p (sat_cons (step763 p h) (sat_cons (step307 p h) (sat_nil p)))
def c787 : List Lit := [(307, false)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true :=
  Snake9.LocalRup.prove_clause [c764, c303] c787 (by decide) p (sat_cons (step764 p h) (sat_cons (step303 p h) (sat_nil p)))
def c788 : List Lit := [(301, false)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true :=
  Snake9.LocalRup.prove_clause [c765, c298] c788 (by decide) p (sat_cons (step765 p h) (sat_cons (step298 p h) (sat_nil p)))
def c789 : List Lit := [(299, false)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true :=
  Snake9.LocalRup.prove_clause [c765, c299] c789 (by decide) p (sat_cons (step765 p h) (sat_cons (step299 p h) (sat_nil p)))
def c790 : List Lit := [(295, false)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true :=
  Snake9.LocalRup.prove_clause [c766, c295] c790 (by decide) p (sat_cons (step766 p h) (sat_cons (step295 p h) (sat_nil p)))
def c791 : List Lit := [(287, false)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true :=
  Snake9.LocalRup.prove_clause [c767, c286] c791 (by decide) p (sat_cons (step767 p h) (sat_cons (step286 p h) (sat_nil p)))
def c792 : List Lit := [(285, false)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true :=
  Snake9.LocalRup.prove_clause [c767, c287] c792 (by decide) p (sat_cons (step767 p h) (sat_cons (step287 p h) (sat_nil p)))
def c793 : List Lit := [(281, false)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true :=
  Snake9.LocalRup.prove_clause [c768, c282] c793 (by decide) p (sat_cons (step768 p h) (sat_cons (step282 p h) (sat_nil p)))
def c794 : List Lit := [(143, false)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true :=
  Snake9.LocalRup.prove_clause [c768, c283] c794 (by decide) p (sat_cons (step768 p h) (sat_cons (step283 p h) (sat_nil p)))
def c795 : List Lit := [(140, false)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true :=
  Snake9.LocalRup.prove_clause [c769, c278] c795 (by decide) p (sat_cons (step769 p h) (sat_cons (step278 p h) (sat_nil p)))
def c796 : List Lit := [(137, false)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true :=
  Snake9.LocalRup.prove_clause [c770, c277] c796 (by decide) p (sat_cons (step770 p h) (sat_cons (step277 p h) (sat_nil p)))
def c797 : List Lit := [(421, false)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true :=
  Snake9.LocalRup.prove_clause [c777, c401] c797 (by decide) p (sat_cons (step777 p h) (sat_cons (step401 p h) (sat_nil p)))
def c798 : List Lit := [(415, false)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true :=
  Snake9.LocalRup.prove_clause [c777, c402] c798 (by decide) p (sat_cons (step777 p h) (sat_cons (step402 p h) (sat_nil p)))
def c799 : List Lit := [(409, false)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true :=
  Snake9.LocalRup.prove_clause [c778, c393] c799 (by decide) p (sat_cons (step778 p h) (sat_cons (step393 p h) (sat_nil p)))
end B112E201
