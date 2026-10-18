import B112E057Part0103
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c8681 : List Lit := [(1061, true), (1096, true), (88, true), (1045, false)]
theorem step8681 (p : Nat → Bool) (h : Constraints p) : clause p c8681 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4160] c8681 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4160 p h) (sat_nil p)))
def c8682 : List Lit := [(1040, false), (1124, false), (88, true), (1061, true), (1088, false), (1045, false)]
theorem step8682 (p : Nat → Bool) (h : Constraints p) : clause p c8682 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5340] c8682 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5340 p h) (sat_nil p)))
def c8683 : List Lit := [(1041, false), (1053, false), (1045, false), (88, true), (1124, false)]
theorem step8683 (p : Nat → Bool) (h : Constraints p) : clause p c8683 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5343] c8683 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5343 p h) (sat_nil p)))
def c8684 : List Lit := [(95, true), (1040, false), (88, true), (1045, false), (1124, false)]
theorem step8684 (p : Nat → Bool) (h : Constraints p) : clause p c8684 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5347] c8684 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5347 p h) (sat_nil p)))
def c8685 : List Lit := [(1040, false), (1075, true), (79, false), (1124, false), (88, true)]
theorem step8685 (p : Nat → Bool) (h : Constraints p) : clause p c8685 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5351] c8685 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5351 p h) (sat_nil p)))
def c8686 : List Lit := [(95, true), (1040, false), (1124, false), (1052, false), (1095, false)]
theorem step8686 (p : Nat → Bool) (h : Constraints p) : clause p c8686 = true :=
  Snake9.LocalRup.prove_clause [c8057, c5352] c8686 (by decide) p (sat_cons (step8057 p h) (sat_cons (step5352 p h) (sat_nil p)))
def c8687 : List Lit := [(89, true), (69, true), (88, true), (79, false), (1124, false), (1053, true), (1032, false), (1039, false)]
theorem step8687 (p : Nat → Bool) (h : Constraints p) : clause p c8687 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5355] c8687 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5355 p h) (sat_nil p)))
def c8688 : List Lit := [(86, true), (1039, false), (88, true), (1089, true), (1124, false), (1055, false), (1087, false), (95, true), (79, false)]
theorem step8688 (p : Nat → Bool) (h : Constraints p) : clause p c8688 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5357] c8688 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5357 p h) (sat_nil p)))
def c8689 : List Lit := [(79, false), (88, true), (1063, true), (1089, true), (95, true), (1051, false), (86, true)]
theorem step8689 (p : Nat → Bool) (h : Constraints p) : clause p c8689 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3797] c8689 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3797 p h) (sat_nil p)))
def c8690 : List Lit := [(1159, true), (1041, false), (1095, false), (1124, false)]
theorem step8690 (p : Nat → Bool) (h : Constraints p) : clause p c8690 = true :=
  Snake9.LocalRup.prove_clause [c8058, c8056, c3774] c8690 (by decide) p (sat_cons (step8058 p h) (sat_cons (step8056 p h) (sat_cons (step3774 p h) (sat_nil p))))
def c8691 : List Lit := [(1040, false), (89, true), (1124, false), (88, true), (1134, false), (1087, false), (1074, false), (1159, true)]
theorem step8691 (p : Nat → Bool) (h : Constraints p) : clause p c8691 = true :=
  Snake9.LocalRup.prove_clause [c8057, c4294] c8691 (by decide) p (sat_cons (step8057 p h) (sat_cons (step4294 p h) (sat_nil p)))
def c8692 : List Lit := [(123, false), (86, true), (1056, false), (88, false), (1029, false), (1026, false), (73, true), (1077, true)]
theorem step8692 (p : Nat → Bool) (h : Constraints p) : clause p c8692 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3838] c8692 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3838 p h) (sat_nil p)))
def c8693 : List Lit := [(1026, false), (1030, false), (1095, false), (123, false), (95, true), (1159, true), (88, false), (86, true), (1051, false)]
theorem step8693 (p : Nat → Bool) (h : Constraints p) : clause p c8693 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3842] c8693 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3842 p h) (sat_nil p)))
def c8694 : List Lit := [(11, false), (1049, true), (86, true), (88, true), (82, true)]
theorem step8694 (p : Nat → Bool) (h : Constraints p) : clause p c8694 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3958] c8694 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3958 p h) (sat_nil p)))
def c8695 : List Lit := [(1052, false), (79, false), (86, true), (88, true), (1064, true), (1089, true), (95, true)]
theorem step8695 (p : Nat → Bool) (h : Constraints p) : clause p c8695 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3865] c8695 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3865 p h) (sat_nil p)))
def c8696 : List Lit := [(945, false), (59, false), (40, false), (112, false)]
theorem step8696 (p : Nat → Bool) (h : Constraints p) : clause p c8696 = true :=
  Snake9.LocalRup.prove_clause [c6908, c5176] c8696 (by decide) p (sat_cons (step6908 p h) (sat_cons (step5176 p h) (sat_nil p)))
def c8697 : List Lit := [(1049, true), (1096, true), (90, false), (1045, false)]
theorem step8697 (p : Nat → Bool) (h : Constraints p) : clause p c8697 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4632] c8697 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4632 p h) (sat_nil p)))
def c8698 : List Lit := [(1048, true), (1074, true), (75, true), (90, true), (79, true)]
theorem step8698 (p : Nat → Bool) (h : Constraints p) : clause p c8698 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4930] c8698 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4930 p h) (sat_nil p)))
def c8699 : List Lit := [(1040, false), (86, false), (88, true), (1124, false), (95, true)]
theorem step8699 (p : Nat → Bool) (h : Constraints p) : clause p c8699 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4967] c8699 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4967 p h) (sat_nil p)))
def c8700 : List Lit := [(1101, true), (88, false), (79, false), (1062, true), (1051, false), (87, true)]
theorem step8700 (p : Nat → Bool) (h : Constraints p) : clause p c8700 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4667] c8700 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4667 p h) (sat_nil p)))
def c8701 : List Lit := [(1061, true), (89, true), (73, false)]
theorem step8701 (p : Nat → Bool) (h : Constraints p) : clause p c8701 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4635] c8701 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4635 p h) (sat_nil p)))
def c8702 : List Lit := [(1062, true), (86, true), (79, false), (75, false), (89, true)]
theorem step8702 (p : Nat → Bool) (h : Constraints p) : clause p c8702 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4775] c8702 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4775 p h) (sat_nil p)))
def c8703 : List Lit := [(89, true), (1039, false), (1159, true), (1124, false), (1061, false), (1075, true), (1087, false), (1045, false)]
theorem step8703 (p : Nat → Bool) (h : Constraints p) : clause p c8703 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5021] c8703 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5021 p h) (sat_nil p)))
def c8704 : List Lit := [(1096, false), (1085, false), (1134, false), (1124, false), (88, true), (1040, false), (1056, true)]
theorem step8704 (p : Nat → Bool) (h : Constraints p) : clause p c8704 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5117] c8704 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5117 p h) (sat_nil p)))
def c8705 : List Lit := [(88, false), (1062, true), (1055, false), (75, false), (1048, false), (1053, false)]
theorem step8705 (p : Nat → Bool) (h : Constraints p) : clause p c8705 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5131] c8705 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5131 p h) (sat_nil p)))
def c8706 : List Lit := [(1053, false), (1063, true), (90, true), (73, false), (88, true), (86, true)]
theorem step8706 (p : Nat → Bool) (h : Constraints p) : clause p c8706 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4996] c8706 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4996 p h) (sat_nil p)))
def c8707 : List Lit := [(1049, true), (86, true), (82, true), (89, false), (79, false)]
theorem step8707 (p : Nat → Bool) (h : Constraints p) : clause p c8707 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5132] c8707 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5132 p h) (sat_nil p)))
def c8708 : List Lit := [(95, false), (90, false), (1088, true), (1040, true), (88, true), (1061, true), (1053, true), (89, true)]
theorem step8708 (p : Nat → Bool) (h : Constraints p) : clause p c8708 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4785] c8708 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4785 p h) (sat_nil p)))
def c8709 : List Lit := [(1049, true), (1096, true), (90, false), (85, true)]
theorem step8709 (p : Nat → Bool) (h : Constraints p) : clause p c8709 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4850] c8709 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4850 p h) (sat_nil p)))
def c8710 : List Lit := [(1088, false), (72, false), (89, false), (1135, true), (1048, true)]
theorem step8710 (p : Nat → Bool) (h : Constraints p) : clause p c8710 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5173] c8710 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5173 p h) (sat_nil p)))
def c8711 : List Lit := [(1096, false), (97, true), (77, true), (90, false), (73, true), (88, true), (69, true), (1089, true), (1053, true)]
theorem step8711 (p : Nat → Bool) (h : Constraints p) : clause p c8711 = true :=
  Snake9.LocalRup.prove_clause [c8058, c5118] c8711 (by decide) p (sat_cons (step8058 p h) (sat_cons (step5118 p h) (sat_nil p)))
def c8712 : List Lit := [(79, false), (1096, false), (75, false), (90, true), (1125, false), (95, true), (1101, false)]
theorem step8712 (p : Nat → Bool) (h : Constraints p) : clause p c8712 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6655] c8712 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6655 p h) (sat_nil p)))
def c8713 : List Lit := [(1049, true), (1051, true), (1096, true)]
theorem step8713 (p : Nat → Bool) (h : Constraints p) : clause p c8713 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5174] c8713 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5174 p h) (sat_nil p)))
def c8714 : List Lit := [(1026, false), (1051, false), (79, false), (1075, true), (89, false), (1053, false)]
theorem step8714 (p : Nat → Bool) (h : Constraints p) : clause p c8714 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5138] c8714 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5138 p h) (sat_nil p)))
def c8715 : List Lit := [(1057, false), (1076, true), (1048, false), (1025, false), (88, true), (86, true), (1064, true), (1027, false)]
theorem step8715 (p : Nat → Bool) (h : Constraints p) : clause p c8715 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5123] c8715 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5123 p h) (sat_nil p)))
def c8716 : List Lit := [(1061, true), (88, false), (1048, false), (75, false)]
theorem step8716 (p : Nat → Bool) (h : Constraints p) : clause p c8716 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4790] c8716 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4790 p h) (sat_nil p)))
def c8717 : List Lit := [(1032, true), (1052, false), (1064, true), (95, true), (82, true), (1089, true), (86, true), (77, true)]
theorem step8717 (p : Nat → Bool) (h : Constraints p) : clause p c8717 = true :=
  Snake9.LocalRup.prove_clause [c8056, c4726] c8717 (by decide) p (sat_cons (step8056 p h) (sat_cons (step4726 p h) (sat_nil p)))
def c8718 : List Lit := [(1039, false), (1089, true), (1124, false), (79, false), (97, true), (1083, false), (1096, false)]
theorem step8718 (p : Nat → Bool) (h : Constraints p) : clause p c8718 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5374] c8718 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5374 p h) (sat_nil p)))
def c8719 : List Lit := [(88, false), (1074, true), (70, true), (1039, true), (79, true), (1053, true), (1088, true), (1045, false)]
theorem step8719 (p : Nat → Bool) (h : Constraints p) : clause p c8719 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6591] c8719 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6591 p h) (sat_nil p)))
def c8720 : List Lit := [(1062, true), (1096, true), (1053, false), (1048, false)]
theorem step8720 (p : Nat → Bool) (h : Constraints p) : clause p c8720 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6554] c8720 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6554 p h) (sat_nil p)))
def c8721 : List Lit := [(1048, false), (1096, true), (1061, true)]
theorem step8721 (p : Nat → Bool) (h : Constraints p) : clause p c8721 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5524] c8721 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5524 p h) (sat_nil p)))
def c8722 : List Lit := [(90, false), (77, false), (1045, false), (1087, false), (70, true), (1101, true), (1095, false), (1051, false), (1063, true)]
theorem step8722 (p : Nat → Bool) (h : Constraints p) : clause p c8722 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6421] c8722 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6421 p h) (sat_nil p)))
def c8723 : List Lit := [(86, true), (123, false), (1030, false), (1026, false), (105, true), (1049, true), (1101, true), (1045, false), (121, false), (1052, false), (88, false)]
theorem step8723 (p : Nat → Bool) (h : Constraints p) : clause p c8723 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5665] c8723 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5665 p h) (sat_nil p)))
def c8724 : List Lit := [(1032, true), (90, true), (1053, false), (86, true), (1063, true), (88, true)]
theorem step8724 (p : Nat → Bool) (h : Constraints p) : clause p c8724 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6565] c8724 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6565 p h) (sat_nil p)))
def c8725 : List Lit := [(88, false), (89, true), (123, false), (1076, true), (1029, false), (86, true), (1026, false)]
theorem step8725 (p : Nat → Bool) (h : Constraints p) : clause p c8725 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5627] c8725 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5627 p h) (sat_nil p)))
def c8726 : List Lit := [(88, false), (1056, false), (1026, false), (123, false), (86, true), (1062, false), (1077, true), (1030, false)]
theorem step8726 (p : Nat → Bool) (h : Constraints p) : clause p c8726 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5664] c8726 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5664 p h) (sat_nil p)))
def c8727 : List Lit := [(1051, false), (1101, false), (70, true), (90, false), (1045, false), (1048, false), (1159, true), (1124, false), (77, false)]
theorem step8727 (p : Nat → Bool) (h : Constraints p) : clause p c8727 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6426] c8727 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6426 p h) (sat_nil p)))
def c8728 : List Lit := [(4, true), (112, true), (1007, true), (75, false), (89, true), (88, false), (1124, true), (76, true), (73, false), (77, false)]
theorem step8728 (p : Nat → Bool) (h : Constraints p) : clause p c8728 = true :=
  Snake9.LocalRup.prove_clause [c6907, c6038] c8728 (by decide) p (sat_cons (step6907 p h) (sat_cons (step6038 p h) (sat_nil p)))
def c8729 : List Lit := [(95, false), (1062, true), (70, false), (1032, true), (1048, false), (1053, false), (79, false), (88, false)]
theorem step8729 (p : Nat → Bool) (h : Constraints p) : clause p c8729 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6629] c8729 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6629 p h) (sat_nil p)))
def c8730 : List Lit := [(86, false), (1087, true), (75, false), (1125, true), (1053, false), (1101, true), (1091, false), (23, true), (88, false), (1027, false)]
theorem step8730 (p : Nat → Bool) (h : Constraints p) : clause p c8730 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5559] c8730 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5559 p h) (sat_nil p)))
def c8731 : List Lit := [(88, false), (1053, false), (1040, true), (1076, true), (89, true), (1048, false), (1026, false), (1029, false)]
theorem step8731 (p : Nat → Bool) (h : Constraints p) : clause p c8731 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5605] c8731 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5605 p h) (sat_nil p)))
def c8732 : List Lit := [(1074, true), (75, true), (1056, false), (1053, false), (88, true)]
theorem step8732 (p : Nat → Bool) (h : Constraints p) : clause p c8732 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5468] c8732 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5468 p h) (sat_nil p)))
def c8733 : List Lit := [(17, false), (1063, true), (89, true), (88, false), (1053, false)]
theorem step8733 (p : Nat → Bool) (h : Constraints p) : clause p c8733 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5915] c8733 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5915 p h) (sat_nil p)))
def c8734 : List Lit := [(86, true), (1025, false), (89, true), (123, false), (88, false), (1076, true), (1030, false)]
theorem step8734 (p : Nat → Bool) (h : Constraints p) : clause p c8734 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5608] c8734 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5608 p h) (sat_nil p)))
def c8735 : List Lit := [(105, false), (1053, false), (87, true), (1086, true), (1124, true), (90, true), (1063, true), (88, true)]
theorem step8735 (p : Nat → Bool) (h : Constraints p) : clause p c8735 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6833] c8735 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6833 p h) (sat_nil p)))
def c8736 : List Lit := [(1134, true), (1063, true), (88, true), (1124, true), (79, false), (86, true), (1053, false)]
theorem step8736 (p : Nat → Bool) (h : Constraints p) : clause p c8736 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6835] c8736 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6835 p h) (sat_nil p)))
def c8737 : List Lit := [(1040, false), (1100, false), (70, false), (88, true), (1124, false), (1045, false), (112, false), (1033, false)]
theorem step8737 (p : Nat → Bool) (h : Constraints p) : clause p c8737 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8058, c6917] c8737 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8058 p h) (sat_cons (step6917 p h) (sat_nil p))))
def c8738 : List Lit := [(1061, true), (90, true), (1055, false), (88, true)]
theorem step8738 (p : Nat → Bool) (h : Constraints p) : clause p c8738 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6926] c8738 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6926 p h) (sat_nil p)))
def c8739 : List Lit := [(86, false), (90, true), (1124, false), (88, true), (1040, false), (1087, true), (1051, false)]
theorem step8739 (p : Nat → Bool) (h : Constraints p) : clause p c8739 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6927] c8739 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6927 p h) (sat_nil p)))
def c8740 : List Lit := [(1096, true), (87, true), (1077, true), (1040, false), (1053, false), (1045, false), (88, true), (90, true), (1124, true), (1033, false), (1051, false), (69, true)]
theorem step8740 (p : Nat → Bool) (h : Constraints p) : clause p c8740 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6930] c8740 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6930 p h) (sat_nil p)))
def c8741 : List Lit := [(1041, false), (1088, false), (1045, false), (88, true)]
theorem step8741 (p : Nat → Bool) (h : Constraints p) : clause p c8741 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6997] c8741 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6997 p h) (sat_nil p)))
def c8742 : List Lit := [(1041, false), (86, false), (79, false), (88, true)]
theorem step8742 (p : Nat → Bool) (h : Constraints p) : clause p c8742 = true :=
  Snake9.LocalRup.prove_clause [c8056, c6998] c8742 (by decide) p (sat_cons (step8056 p h) (sat_cons (step6998 p h) (sat_nil p)))
def c8743 : List Lit := [(11, false), (83, false), (80, false), (86, true), (70, false), (4, false), (1076, true), (1031, false), (1056, false)]
theorem step8743 (p : Nat → Bool) (h : Constraints p) : clause p c8743 = true :=
  Snake9.LocalRup.prove_clause [c8056, c7029] c8743 (by decide) p (sat_cons (step8056 p h) (sat_cons (step7029 p h) (sat_nil p)))
def c8744 : List Lit := [(4, false), (1056, false), (86, true), (79, true), (70, false), (1076, true), (89, false)]
theorem step8744 (p : Nat → Bool) (h : Constraints p) : clause p c8744 = true :=
  Snake9.LocalRup.prove_clause [c8056, c7032] c8744 (by decide) p (sat_cons (step8056 p h) (sat_cons (step7032 p h) (sat_nil p)))
end B112E057
