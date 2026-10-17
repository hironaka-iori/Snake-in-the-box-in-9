import B112E115Part0035
namespace B112E115
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3543 : List Lit := [(53, true)]
theorem step3543 (p : Nat → Bool) (h : Constraints p) : clause p c3543 = true :=
  Snake9.LocalRup.prove_clause [c3539, c3509, c1544] c3543 (by decide) p (sat_cons (step3539 p h) (sat_cons (step3509 p h) (sat_cons (step1544 p h) (sat_nil p))))
def c3544 : List Lit := [(822, true)]
theorem step3544 (p : Nat → Bool) (h : Constraints p) : clause p c3544 = true :=
  Snake9.LocalRup.prove_clause [c3540, c778] c3544 (by decide) p (sat_cons (step3540 p h) (sat_cons (step778 p h) (sat_nil p)))
def c3545 : List Lit := [(819, true)]
theorem step3545 (p : Nat → Bool) (h : Constraints p) : clause p c3545 = true :=
  Snake9.LocalRup.prove_clause [c3541, c773] c3545 (by decide) p (sat_cons (step3541 p h) (sat_cons (step773 p h) (sat_nil p)))
def c3546 : List Lit := [(1001, true)]
theorem step3546 (p : Nat → Bool) (h : Constraints p) : clause p c3546 = true :=
  Snake9.LocalRup.prove_clause [c3542, c1130] c3546 (by decide) p (sat_cons (step3542 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c3547 : List Lit := [(48, false)]
theorem step3547 (p : Nat → Bool) (h : Constraints p) : clause p c3547 = true :=
  Snake9.LocalRup.prove_clause [c3543, c3509, c3510, c322] c3547 (by decide) p (sat_cons (step3543 p h) (sat_cons (step3509 p h) (sat_cons (step3510 p h) (sat_cons (step322 p h) (sat_nil p)))))
def c3548 : List Lit := [(826, true)]
theorem step3548 (p : Nat → Bool) (h : Constraints p) : clause p c3548 = true :=
  Snake9.LocalRup.prove_clause [c3544, c786] c3548 (by decide) p (sat_cons (step3544 p h) (sat_cons (step786 p h) (sat_nil p)))
def c3549 : List Lit := [(873, true)]
theorem step3549 (p : Nat → Bool) (h : Constraints p) : clause p c3549 = true :=
  Snake9.LocalRup.prove_clause [c3547, c887] c3549 (by decide) p (sat_cons (step3547 p h) (sat_cons (step887 p h) (sat_nil p)))
def c3550 : List Lit := [(821, false)]
theorem step3550 (p : Nat → Bool) (h : Constraints p) : clause p c3550 = true :=
  Snake9.LocalRup.prove_clause [c3548, c3395, c805] c3550 (by decide) p (sat_cons (step3548 p h) (sat_cons (step3395 p h) (sat_cons (step805 p h) (sat_nil p))))
def c3551 : List Lit := [(875, true)]
theorem step3551 (p : Nat → Bool) (h : Constraints p) : clause p c3551 = true :=
  Snake9.LocalRup.prove_clause [c3549, c889] c3551 (by decide) p (sat_cons (step3549 p h) (sat_cons (step889 p h) (sat_nil p)))
def c3552 : List Lit := [(812, true)]
theorem step3552 (p : Nat → Bool) (h : Constraints p) : clause p c3552 = true :=
  Snake9.LocalRup.prove_clause [c3550, c3538, c2050] c3552 (by decide) p (sat_cons (step3550 p h) (sat_cons (step3538 p h) (sat_cons (step2050 p h) (sat_nil p))))
def c3553 : List Lit := [(887, true)]
theorem step3553 (p : Nat → Bool) (h : Constraints p) : clause p c3553 = true :=
  Snake9.LocalRup.prove_clause [c3551, c914] c3553 (by decide) p (sat_cons (step3551 p h) (sat_cons (step914 p h) (sat_nil p)))
def c3554 : List Lit := [(896, true)]
theorem step3554 (p : Nat → Bool) (h : Constraints p) : clause p c3554 = true :=
  Snake9.LocalRup.prove_clause [c3553, c3517, c932] c3554 (by decide) p (sat_cons (step3553 p h) (sat_cons (step3517 p h) (sat_cons (step932 p h) (sat_nil p))))
def c3555 : List Lit := [(861, false), (865, false), (966, false), (842, false)]
theorem step3555 (p : Nat → Bool) (h : Constraints p) : clause p c3555 = true :=
  Snake9.LocalRup.prove_clause [c3546, c3544, c3526, c3527] c3555 (by decide) p (sat_cons (step3546 p h) (sat_cons (step3544 p h) (sat_cons (step3526 p h) (sat_cons (step3527 p h) (sat_nil p)))))
def c3556 : List Lit := [(842, false), (966, false)]
theorem step3556 (p : Nat → Bool) (h : Constraints p) : clause p c3556 = true :=
  Snake9.LocalRup.prove_clause [c3554, c3510, c3546, c3547, c3539, c3535, c3515, c984, c1631, c3356, c3287, c890, c888, c1877, c857, c1298, c863, c3555] c3556 (by decide) p (sat_cons (step3554 p h) (sat_cons (step3510 p h) (sat_cons (step3546 p h) (sat_cons (step3547 p h) (sat_cons (step3539 p h) (sat_cons (step3535 p h) (sat_cons (step3515 p h) (sat_cons (step984 p h) (sat_cons (step1631 p h) (sat_cons (step3356 p h) (sat_cons (step3287 p h) (sat_cons (step890 p h) (sat_cons (step888 p h) (sat_cons (step1877 p h) (sat_cons (step857 p h) (sat_cons (step1298 p h) (sat_cons (step863 p h) (sat_cons (step3555 p h) (sat_nil p)))))))))))))))))))
def c3557 : List Lit := [(842, true)]
theorem step3557 (p : Nat → Bool) (h : Constraints p) : clause p c3557 = true :=
  Snake9.LocalRup.prove_clause [c3535, c3514, c3509, c3548, c3552, c3545, c3544, c3492, c825, c782, c797, c787] c3557 (by decide) p (sat_cons (step3535 p h) (sat_cons (step3514 p h) (sat_cons (step3509 p h) (sat_cons (step3548 p h) (sat_cons (step3552 p h) (sat_cons (step3545 p h) (sat_cons (step3544 p h) (sat_cons (step3492 p h) (sat_cons (step825 p h) (sat_cons (step782 p h) (sat_cons (step797 p h) (sat_cons (step787 p h) (sat_nil p)))))))))))))
def c3558 : List Lit := [(966, false)]
theorem step3558 (p : Nat → Bool) (h : Constraints p) : clause p c3558 = true :=
  Snake9.LocalRup.prove_clause [c3557, c3556] c3558 (by decide) p (sat_cons (step3557 p h) (sat_cons (step3556 p h) (sat_nil p)))
def c3559 : List Lit := [(962, false)]
theorem step3559 (p : Nat → Bool) (h : Constraints p) : clause p c3559 = true :=
  Snake9.LocalRup.prove_clause [c3558, c1080] c3559 (by decide) p (sat_cons (step3558 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c3560 : List Lit := [(949, false)]
theorem step3560 (p : Nat → Bool) (h : Constraints p) : clause p c3560 = true :=
  Snake9.LocalRup.prove_clause [c3558, c1292] c3560 (by decide) p (sat_cons (step3558 p h) (sat_cons (step1292 p h) (sat_nil p)))
def c3561 : List Lit := [(76, false)]
theorem step3561 (p : Nat → Bool) (h : Constraints p) : clause p c3561 = true :=
  Snake9.LocalRup.prove_clause [c3558, c1788] c3561 (by decide) p (sat_cons (step3558 p h) (sat_cons (step1788 p h) (sat_nil p)))
def c3562 : List Lit := [(78, true)]
theorem step3562 (p : Nat → Bool) (h : Constraints p) : clause p c3562 = true :=
  Snake9.LocalRup.prove_clause [c3558, c1789] c3562 (by decide) p (sat_cons (step3558 p h) (sat_cons (step1789 p h) (sat_nil p)))
def c3563 : List Lit := [(2, true)]
theorem step3563 (p : Nat → Bool) (h : Constraints p) : clause p c3563 = true :=
  Snake9.LocalRup.prove_clause [c3558, c3198] c3563 (by decide) p (sat_cons (step3558 p h) (sat_cons (step3198 p h) (sat_nil p)))
def c3564 : List Lit := [(75, true)]
theorem step3564 (p : Nat → Bool) (h : Constraints p) : clause p c3564 = true :=
  Snake9.LocalRup.prove_clause [c3560, c1052] c3564 (by decide) p (sat_cons (step3560 p h) (sat_cons (step1052 p h) (sat_nil p)))
def c3565 : List Lit := [(77, true)]
theorem step3565 (p : Nat → Bool) (h : Constraints p) : clause p c3565 = true :=
  Snake9.LocalRup.prove_clause [c3561, c3562, c1570] c3565 (by decide) p (sat_cons (step3561 p h) (sat_cons (step3562 p h) (sat_cons (step1570 p h) (sat_nil p))))
def c3566 : List Lit := [(824, true)]
theorem step3566 (p : Nat → Bool) (h : Constraints p) : clause p c3566 = true :=
  Snake9.LocalRup.prove_clause [c3563, c3225, c1731] c3566 (by decide) p (sat_cons (step3563 p h) (sat_cons (step3225 p h) (sat_cons (step1731 p h) (sat_nil p))))
def c3567 : List Lit := [(82, false)]
theorem step3567 (p : Nat → Bool) (h : Constraints p) : clause p c3567 = true :=
  Snake9.LocalRup.prove_clause [c3564, c3562, c3565, c470] c3567 (by decide) p (sat_cons (step3564 p h) (sat_cons (step3562 p h) (sat_cons (step3565 p h) (sat_cons (step470 p h) (sat_nil p)))))
def c3568 : List Lit := [(827, true)]
theorem step3568 (p : Nat → Bool) (h : Constraints p) : clause p c3568 = true :=
  Snake9.LocalRup.prove_clause [c3566, c3544, c787] c3568 (by decide) p (sat_cons (step3566 p h) (sat_cons (step3544 p h) (sat_cons (step787 p h) (sat_nil p))))
def c3569 : List Lit := [(957, true)]
theorem step3569 (p : Nat → Bool) (h : Constraints p) : clause p c3569 = true :=
  Snake9.LocalRup.prove_clause [c3567, c1066] c3569 (by decide) p (sat_cons (step3567 p h) (sat_cons (step1066 p h) (sat_nil p)))
def c3570 : List Lit := [(820, false)]
theorem step3570 (p : Nat → Bool) (h : Constraints p) : clause p c3570 = true :=
  Snake9.LocalRup.prove_clause [c3568, c3395, c802] c3570 (by decide) p (sat_cons (step3568 p h) (sat_cons (step3395 p h) (sat_cons (step802 p h) (sat_nil p))))
def c3571 : List Lit := [(959, false)]
theorem step3571 (p : Nat → Bool) (h : Constraints p) : clause p c3571 = true :=
  Snake9.LocalRup.prove_clause [c3569, c3559, c1074] c3571 (by decide) p (sat_cons (step3569 p h) (sat_cons (step3559 p h) (sat_cons (step1074 p h) (sat_nil p))))
def c3572 : List Lit := [(16, true)]
theorem step3572 (p : Nat → Bool) (h : Constraints p) : clause p c3572 = true :=
  Snake9.LocalRup.prove_clause [c3570, c3541, c776] c3572 (by decide) p (sat_cons (step3570 p h) (sat_cons (step3541 p h) (sat_cons (step776 p h) (sat_nil p))))
def c3573 : List Lit := [(86, true)]
theorem step3573 (p : Nat → Bool) (h : Constraints p) : clause p c3573 = true :=
  Snake9.LocalRup.prove_clause [c3571, c1069] c3573 (by decide) p (sat_cons (step3571 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c3574 : List Lit := []
theorem step3574 (p : Nat → Bool) (h : Constraints p) : clause p c3574 = true :=
  Snake9.LocalRup.prove_clause [c3573, c3572, c3564, c3562, c1293] c3574 (by decide) p (sat_cons (step3573 p h) (sat_cons (step3572 p h) (sat_cons (step3564 p h) (sat_cons (step3562 p h) (sat_cons (step1293 p h) (sat_nil p))))))
end B112E115
