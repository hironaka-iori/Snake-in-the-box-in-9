import B112E148Part0002
namespace B112E148
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c732 : List Lit := [(81, true), (1475, true), (1487, true), (71, false), (69, false)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true :=
  Snake9.LocalRup.prove_clause [c206, c453, c449, c451, c452, c455, c458, c446, c447, c475, c155, c587, c436, c144, c432, c143, c430] c732 (by decide) p (sat_cons (step206 p h) (sat_cons (step453 p h) (sat_cons (step449 p h) (sat_cons (step451 p h) (sat_cons (step452 p h) (sat_cons (step455 p h) (sat_cons (step458 p h) (sat_cons (step446 p h) (sat_cons (step447 p h) (sat_cons (step475 p h) (sat_cons (step155 p h) (sat_cons (step587 p h) (sat_cons (step436 p h) (sat_cons (step144 p h) (sat_cons (step432 p h) (sat_cons (step143 p h) (sat_cons (step430 p h) (sat_nil p))))))))))))))))))
def c733 : List Lit := [(1558, true), (1458, false)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true :=
  Snake9.LocalRup.prove_clause [c574, c200, c558, c570, c518, c725, c515, c500, c731, c129, c590, c722, c499, c443, c514, c442, c521, c472, c459, c732, c172, c584, c486, c489, c495] c733 (by decide) p (sat_cons (step574 p h) (sat_cons (step200 p h) (sat_cons (step558 p h) (sat_cons (step570 p h) (sat_cons (step518 p h) (sat_cons (step725 p h) (sat_cons (step515 p h) (sat_cons (step500 p h) (sat_cons (step731 p h) (sat_cons (step129 p h) (sat_cons (step590 p h) (sat_cons (step722 p h) (sat_cons (step499 p h) (sat_cons (step443 p h) (sat_cons (step514 p h) (sat_cons (step442 p h) (sat_cons (step521 p h) (sat_cons (step472 p h) (sat_cons (step459 p h) (sat_cons (step732 p h) (sat_cons (step172 p h) (sat_cons (step584 p h) (sat_cons (step486 p h) (sat_cons (step489 p h) (sat_cons (step495 p h) (sat_nil p))))))))))))))))))))))))))
def c734 : List Lit := [(1367, true)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true :=
  Snake9.LocalRup.prove_clause [c671, c729, c730, c605, c670] c734 (by decide) p (sat_cons (step671 p h) (sat_cons (step729 p h) (sat_cons (step730 p h) (sat_cons (step605 p h) (sat_cons (step670 p h) (sat_nil p))))))
def c735 : List Lit := [(1438, true)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true :=
  Snake9.LocalRup.prove_clause [c734, c613, c421] c735 (by decide) p (sat_cons (step734 p h) (sat_cons (step613 p h) (sat_cons (step421 p h) (sat_nil p))))
def c736 : List Lit := [(1558, false)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true :=
  Snake9.LocalRup.prove_clause [c735, c528, c526] c736 (by decide) p (sat_cons (step735 p h) (sat_cons (step528 p h) (sat_cons (step526 p h) (sat_nil p))))
def c737 : List Lit := [(69, true)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true :=
  Snake9.LocalRup.prove_clause [c736, c725] c737 (by decide) p (sat_cons (step736 p h) (sat_cons (step725 p h) (sat_nil p)))
def c738 : List Lit := [(1458, false)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true :=
  Snake9.LocalRup.prove_clause [c736, c733] c738 (by decide) p (sat_cons (step736 p h) (sat_cons (step733 p h) (sat_nil p)))
def c739 : List Lit := [(1454, false)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true :=
  Snake9.LocalRup.prove_clause [c738, c435] c739 (by decide) p (sat_cons (step738 p h) (sat_cons (step435 p h) (sat_nil p)))
def c740 : List Lit := [(1450, false)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true :=
  Snake9.LocalRup.prove_clause [c739, c433] c740 (by decide) p (sat_cons (step739 p h) (sat_cons (step433 p h) (sat_nil p)))
def c741 : List Lit := [(68, false)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true :=
  Snake9.LocalRup.prove_clause [c739, c737, c721] c741 (by decide) p (sat_cons (step739 p h) (sat_cons (step737 p h) (sat_cons (step721 p h) (sat_nil p))))
def c742 : List Lit := [(64, true)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true :=
  Snake9.LocalRup.prove_clause [c740, c427] c742 (by decide) p (sat_cons (step740 p h) (sat_cons (step427 p h) (sat_nil p)))
def c743 : List Lit := [(4, true)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true :=
  Snake9.LocalRup.prove_clause [c741, c203, c742, c136] c743 (by decide) p (sat_cons (step741 p h) (sat_cons (step203 p h) (sat_cons (step742 p h) (sat_cons (step136 p h) (sat_nil p)))))
def c744 : List Lit := [(79, true)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true :=
  Snake9.LocalRup.prove_clause [c741, c206, c737, c144] c744 (by decide) p (sat_cons (step741 p h) (sat_cons (step206 p h) (sat_cons (step737 p h) (sat_cons (step144 p h) (sat_nil p)))))
def c745 : List Lit := [(1339, true)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true :=
  Snake9.LocalRup.prove_clause [c742, c727, c737, c743, c581] c745 (by decide) p (sat_cons (step742 p h) (sat_cons (step727 p h) (sat_cons (step737 p h) (sat_cons (step743 p h) (sat_cons (step581 p h) (sat_nil p))))))
def c746 : List Lit := [(18, false)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true :=
  Snake9.LocalRup.prove_clause [c744, c727, c737, c532] c746 (by decide) p (sat_cons (step744 p h) (sat_cons (step727 p h) (sat_cons (step737 p h) (sat_cons (step532 p h) (sat_nil p)))))
def c747 : List Lit := [(1358, false)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true :=
  Snake9.LocalRup.prove_clause [c745, c625, c352] c747 (by decide) p (sat_cons (step745 p h) (sat_cons (step625 p h) (sat_cons (step352 p h) (sat_nil p))))
def c748 : List Lit := [(1343, true)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true :=
  Snake9.LocalRup.prove_clause [c746, c317] c748 (by decide) p (sat_cons (step746 p h) (sat_cons (step317 p h) (sat_nil p)))
def c749 : List Lit := [(1346, false)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true :=
  Snake9.LocalRup.prove_clause [c747, c730, c343] c749 (by decide) p (sat_cons (step747 p h) (sat_cons (step730 p h) (sat_cons (step343 p h) (sat_nil p))))
def c750 : List Lit := [(1345, true)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true :=
  Snake9.LocalRup.prove_clause [c748, c320] c750 (by decide) p (sat_cons (step748 p h) (sat_cons (step320 p h) (sat_nil p)))
def c751 : List Lit := [(20, false)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true :=
  Snake9.LocalRup.prove_clause [c749, c746, c705] c751 (by decide) p (sat_cons (step749 p h) (sat_cons (step746 p h) (sat_cons (step705 p h) (sat_nil p))))
def c752 : List Lit := [(1353, false)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true :=
  Snake9.LocalRup.prove_clause [c750, c747, c340] c752 (by decide) p (sat_cons (step750 p h) (sat_cons (step747 p h) (sat_cons (step340 p h) (sat_nil p))))
def c753 : List Lit := [(1348, true)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true :=
  Snake9.LocalRup.prove_clause [c751, c326] c753 (by decide) p (sat_cons (step751 p h) (sat_cons (step326 p h) (sat_nil p)))
def c754 : List Lit := []
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true :=
  Snake9.LocalRup.prove_clause [c753, c752, c729, c332] c754 (by decide) p (sat_cons (step753 p h) (sat_cons (step752 p h) (sat_cons (step729 p h) (sat_cons (step332 p h) (sat_nil p)))))
end B112E148
