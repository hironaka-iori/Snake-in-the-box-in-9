import B112E123Inputs
namespace B112E123
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c711 : List Lit := [(25, false)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true :=
  Snake9.LocalRup.prove_clause [c229, c116] c711 (by decide) p (sat_cons (step229 p h) (sat_cons (step116 p h) (sat_nil p)))
def c712 : List Lit := [(29, false)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true :=
  Snake9.LocalRup.prove_clause [c231, c121] c712 (by decide) p (sat_cons (step231 p h) (sat_cons (step121 p h) (sat_nil p)))
def c713 : List Lit := [(30, false)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true :=
  Snake9.LocalRup.prove_clause [c232, c122] c713 (by decide) p (sat_cons (step232 p h) (sat_cons (step122 p h) (sat_nil p)))
def c714 : List Lit := [(80, false)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true :=
  Snake9.LocalRup.prove_clause [c246, c194] c714 (by decide) p (sat_cons (step246 p h) (sat_cons (step194 p h) (sat_nil p)))
def c715 : List Lit := [(92, false)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true :=
  Snake9.LocalRup.prove_clause [c249, c207] c715 (by decide) p (sat_cons (step249 p h) (sat_cons (step207 p h) (sat_nil p)))
def c716 : List Lit := [(434, false)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true :=
  Snake9.LocalRup.prove_clause [c357, c354] c716 (by decide) p (sat_cons (step357 p h) (sat_cons (step354 p h) (sat_nil p)))
def c717 : List Lit := [(326, false)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true :=
  Snake9.LocalRup.prove_clause [c357, c356] c717 (by decide) p (sat_cons (step357 p h) (sat_cons (step356 p h) (sat_nil p)))
def c718 : List Lit := [(432, false)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true :=
  Snake9.LocalRup.prove_clause [c716, c350] c718 (by decide) p (sat_cons (step716 p h) (sat_cons (step350 p h) (sat_nil p)))
def c719 : List Lit := [(378, false)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true :=
  Snake9.LocalRup.prove_clause [c716, c353] c719 (by decide) p (sat_cons (step716 p h) (sat_cons (step353 p h) (sat_nil p)))
def c720 : List Lit := [(324, false)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true :=
  Snake9.LocalRup.prove_clause [c717, c310] c720 (by decide) p (sat_cons (step717 p h) (sat_cons (step310 p h) (sat_nil p)))
def c721 : List Lit := [(272, false)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true :=
  Snake9.LocalRup.prove_clause [c717, c313] c721 (by decide) p (sat_cons (step717 p h) (sat_cons (step313 p h) (sat_nil p)))
def c722 : List Lit := [(404, false)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true :=
  Snake9.LocalRup.prove_clause [c718, c349] c722 (by decide) p (sat_cons (step718 p h) (sat_cons (step349 p h) (sat_nil p)))
def c723 : List Lit := [(296, false)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true :=
  Snake9.LocalRup.prove_clause [c720, c308] c723 (by decide) p (sat_cons (step720 p h) (sat_cons (step308 p h) (sat_nil p)))
def c724 : List Lit := [(270, false)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true :=
  Snake9.LocalRup.prove_clause [c721, c292] c724 (by decide) p (sat_cons (step721 p h) (sat_cons (step292 p h) (sat_nil p)))
def c725 : List Lit := [(244, false)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true :=
  Snake9.LocalRup.prove_clause [c721, c295] c725 (by decide) p (sat_cons (step721 p h) (sat_cons (step295 p h) (sat_nil p)))
def c726 : List Lit := [(390, false)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true :=
  Snake9.LocalRup.prove_clause [c722, c343] c726 (by decide) p (sat_cons (step722 p h) (sat_cons (step343 p h) (sat_nil p)))
def c727 : List Lit := [(294, false)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true :=
  Snake9.LocalRup.prove_clause [c723, c304] c727 (by decide) p (sat_cons (step723 p h) (sat_cons (step304 p h) (sat_nil p)))
def c728 : List Lit := [(282, false)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true :=
  Snake9.LocalRup.prove_clause [c723, c306] c728 (by decide) p (sat_cons (step723 p h) (sat_cons (step306 p h) (sat_nil p)))
def c729 : List Lit := [(256, false)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true :=
  Snake9.LocalRup.prove_clause [c724, c290] c729 (by decide) p (sat_cons (step724 p h) (sat_cons (step290 p h) (sat_nil p)))
def c730 : List Lit := [(242, false)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true :=
  Snake9.LocalRup.prove_clause [c725, c271] c730 (by decide) p (sat_cons (step725 p h) (sat_cons (step271 p h) (sat_nil p)))
def c731 : List Lit := [(230, false)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true :=
  Snake9.LocalRup.prove_clause [c725, c274] c731 (by decide) p (sat_cons (step725 p h) (sat_cons (step274 p h) (sat_nil p)))
def c732 : List Lit := [(388, false)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true :=
  Snake9.LocalRup.prove_clause [c726, c341] c732 (by decide) p (sat_cons (step726 p h) (sat_cons (step341 p h) (sat_nil p)))
def c733 : List Lit := [(382, false)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true :=
  Snake9.LocalRup.prove_clause [c726, c342] c733 (by decide) p (sat_cons (step726 p h) (sat_cons (step342 p h) (sat_nil p)))
def c734 : List Lit := [(292, false)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true :=
  Snake9.LocalRup.prove_clause [c727, c303] c734 (by decide) p (sat_cons (step727 p h) (sat_cons (step303 p h) (sat_nil p)))
def c735 : List Lit := [(248, false)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true :=
  Snake9.LocalRup.prove_clause [c729, c280] c735 (by decide) p (sat_cons (step729 p h) (sat_cons (step280 p h) (sat_nil p)))
def c736 : List Lit := [(224, false)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true :=
  Snake9.LocalRup.prove_clause [c731, c259] c736 (by decide) p (sat_cons (step731 p h) (sat_cons (step259 p h) (sat_nil p)))
def c737 : List Lit := [(380, false)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true :=
  Snake9.LocalRup.prove_clause [c733, c337] c737 (by decide) p (sat_cons (step733 p h) (sat_cons (step337 p h) (sat_nil p)))
def c738 : List Lit := [(288, false)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true :=
  Snake9.LocalRup.prove_clause [c734, c302] c738 (by decide) p (sat_cons (step734 p h) (sat_cons (step302 p h) (sat_nil p)))
def c739 : List Lit := [(222, false)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true :=
  Snake9.LocalRup.prove_clause [c736, c257] c739 (by decide) p (sat_cons (step736 p h) (sat_cons (step257 p h) (sat_nil p)))
def c740 : List Lit := [(784, true)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true :=
  Snake9.LocalRup.prove_clause [c711, c408] c740 (by decide) p (sat_cons (step711 p h) (sat_cons (step408 p h) (sat_nil p)))
def c741 : List Lit := [(24, true), (785, true)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true :=
  Snake9.LocalRup.prove_clause [c711, c409] c741 (by decide) p (sat_cons (step711 p h) (sat_cons (step409 p h) (sat_nil p)))
def c742 : List Lit := [(786, true)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true :=
  Snake9.LocalRup.prove_clause [c740, c410] c742 (by decide) p (sat_cons (step740 p h) (sat_cons (step410 p h) (sat_nil p)))
def c743 : List Lit := [(782, false), (787, true)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true :=
  Snake9.LocalRup.prove_clause [c740, c412] c743 (by decide) p (sat_cons (step740 p h) (sat_cons (step412 p h) (sat_nil p)))
def c744 : List Lit := [(783, false), (788, true)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true :=
  Snake9.LocalRup.prove_clause [c740, c414] c744 (by decide) p (sat_cons (step740 p h) (sat_cons (step414 p h) (sat_nil p)))
def c745 : List Lit := [(790, true)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true :=
  Snake9.LocalRup.prove_clause [c742, c416] c745 (by decide) p (sat_cons (step742 p h) (sat_cons (step416 p h) (sat_nil p)))
def c746 : List Lit := [(779, false), (791, true)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true :=
  Snake9.LocalRup.prove_clause [c742, c419] c746 (by decide) p (sat_cons (step742 p h) (sat_cons (step419 p h) (sat_nil p)))
def c747 : List Lit := [(780, false), (792, true)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true :=
  Snake9.LocalRup.prove_clause [c742, c423] c747 (by decide) p (sat_cons (step742 p h) (sat_cons (step423 p h) (sat_nil p)))
def c748 : List Lit := [(781, false), (793, true)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true :=
  Snake9.LocalRup.prove_clause [c742, c427] c748 (by decide) p (sat_cons (step742 p h) (sat_cons (step427 p h) (sat_nil p)))
def c749 : List Lit := [(773, false), (801, true)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true :=
  Snake9.LocalRup.prove_clause [c745, c439] c749 (by decide) p (sat_cons (step745 p h) (sat_cons (step439 p h) (sat_nil p)))
def c750 : List Lit := [(775, false), (803, true)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true :=
  Snake9.LocalRup.prove_clause [c745, c446] c750 (by decide) p (sat_cons (step745 p h) (sat_cons (step446 p h) (sat_nil p)))
def c751 : List Lit := [(812, true)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true :=
  Snake9.LocalRup.prove_clause [c712, c713, c449] c751 (by decide) p (sat_cons (step712 p h) (sat_cons (step713 p h) (sat_cons (step449 p h) (sat_nil p))))
def c752 : List Lit := [(814, true)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true :=
  Snake9.LocalRup.prove_clause [c751, c450] c752 (by decide) p (sat_cons (step751 p h) (sat_cons (step450 p h) (sat_nil p)))
def c753 : List Lit := [(27, true), (815, true)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true :=
  Snake9.LocalRup.prove_clause [c751, c451] c753 (by decide) p (sat_cons (step751 p h) (sat_cons (step451 p h) (sat_nil p)))
def c754 : List Lit := [(825, true)]
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true :=
  Snake9.LocalRup.prove_clause [c752, c460] c754 (by decide) p (sat_cons (step752 p h) (sat_cons (step460 p h) (sat_nil p)))
def c755 : List Lit := [(820, false), (826, true)]
theorem step755 (p : Nat → Bool) (h : Constraints p) : clause p c755 = true :=
  Snake9.LocalRup.prove_clause [c752, c461] c755 (by decide) p (sat_cons (step752 p h) (sat_cons (step461 p h) (sat_nil p)))
def c756 : List Lit := [(821, false), (827, true)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true :=
  Snake9.LocalRup.prove_clause [c752, c462] c756 (by decide) p (sat_cons (step752 p h) (sat_cons (step462 p h) (sat_nil p)))
def c757 : List Lit := [(852, true)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true :=
  Snake9.LocalRup.prove_clause [c754, c478] c757 (by decide) p (sat_cons (step754 p h) (sat_cons (step478 p h) (sat_nil p)))
def c758 : List Lit := [(844, false), (853, true)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true :=
  Snake9.LocalRup.prove_clause [c754, c479] c758 (by decide) p (sat_cons (step754 p h) (sat_cons (step479 p h) (sat_nil p)))
def c759 : List Lit := [(845, false), (854, true)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true :=
  Snake9.LocalRup.prove_clause [c754, c480] c759 (by decide) p (sat_cons (step754 p h) (sat_cons (step480 p h) (sat_nil p)))
def c760 : List Lit := [(803, false), (873, true)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true :=
  Snake9.LocalRup.prove_clause [c757, c490] c760 (by decide) p (sat_cons (step757 p h) (sat_cons (step490 p h) (sat_nil p)))
def c761 : List Lit := [(909, true)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true :=
  Snake9.LocalRup.prove_clause [c714, c522] c761 (by decide) p (sat_cons (step714 p h) (sat_cons (step522 p h) (sat_nil p)))
def c762 : List Lit := [(79, true), (910, true)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true :=
  Snake9.LocalRup.prove_clause [c714, c523] c762 (by decide) p (sat_cons (step714 p h) (sat_cons (step523 p h) (sat_nil p)))
def c763 : List Lit := [(907, false), (912, true)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true :=
  Snake9.LocalRup.prove_clause [c761, c525] c763 (by decide) p (sat_cons (step761 p h) (sat_cons (step525 p h) (sat_nil p)))
def c764 : List Lit := [(908, false), (913, true)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true :=
  Snake9.LocalRup.prove_clause [c761, c527] c764 (by decide) p (sat_cons (step761 p h) (sat_cons (step527 p h) (sat_nil p)))
def c765 : List Lit := [(943, true)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true :=
  Snake9.LocalRup.prove_clause [c715, c556] c765 (by decide) p (sat_cons (step715 p h) (sat_cons (step556 p h) (sat_nil p)))
def c766 : List Lit := [(945, true)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true :=
  Snake9.LocalRup.prove_clause [c765, c557] c766 (by decide) p (sat_cons (step765 p h) (sat_cons (step557 p h) (sat_nil p)))
def c767 : List Lit := [(941, false), (946, true)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true :=
  Snake9.LocalRup.prove_clause [c765, c558] c767 (by decide) p (sat_cons (step765 p h) (sat_cons (step558 p h) (sat_nil p)))
def c768 : List Lit := [(949, true)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true :=
  Snake9.LocalRup.prove_clause [c766, c559] c768 (by decide) p (sat_cons (step766 p h) (sat_cons (step559 p h) (sat_nil p)))
def c769 : List Lit := [(938, false), (950, true)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true :=
  Snake9.LocalRup.prove_clause [c766, c561] c769 (by decide) p (sat_cons (step766 p h) (sat_cons (step561 p h) (sat_nil p)))
def c770 : List Lit := [(939, false), (951, true)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true :=
  Snake9.LocalRup.prove_clause [c766, c563] c770 (by decide) p (sat_cons (step766 p h) (sat_cons (step563 p h) (sat_nil p)))
def c771 : List Lit := [(980, true)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true :=
  Snake9.LocalRup.prove_clause [c768, c578] c771 (by decide) p (sat_cons (step768 p h) (sat_cons (step578 p h) (sat_nil p)))
def c772 : List Lit := [(972, false), (981, true)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true :=
  Snake9.LocalRup.prove_clause [c768, c579] c772 (by decide) p (sat_cons (step768 p h) (sat_cons (step579 p h) (sat_nil p)))
def c773 : List Lit := [(973, false), (982, true)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true :=
  Snake9.LocalRup.prove_clause [c768, c580] c773 (by decide) p (sat_cons (step768 p h) (sat_cons (step580 p h) (sat_nil p)))
def c774 : List Lit := [(928, false), (1002, true)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true :=
  Snake9.LocalRup.prove_clause [c771, c594] c774 (by decide) p (sat_cons (step771 p h) (sat_cons (step594 p h) (sat_nil p)))
end B112E123
