import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := by
  have hs : count459 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal (baseVal q)) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_right (literal (valuation q) (457)) (literal (valuation q) (459)) (countLit q [233, 234]) (countLit q [235, 236]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuation q 457 = false ∨ valuation q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 459 = true := by
  have hs : count459 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal (baseVal q)) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuation q) (455)) (literal (valuation q) (459)) (countLit q [233, 234]) (countLit q [235, 236]) (count459 q) 1 (meaning455 q) (meaning459 q) hs
  change valuation q 455 = false ∨ valuation q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := by
  have hs : count461 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_right (literal (valuation q) (459)) (literal (valuation q) (461)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuation q 459 = false ∨ valuation q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 461 = true := by
  have hs : count461 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_left (literal (valuation q) (453)) (literal (valuation q) (461)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count461 q) 1 (meaning453 q) (meaning461 q) hs
  change valuation q 453 = false ∨ valuation q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 463 = true := by
  have hs : count463 q = (countLit q [237]) + (countLit q [238]) := List.countP_append (p := literal (baseVal q)) (l₁ := [237]) (l₂ := [238])
  have hm := merge_left (literal (valuation q) (237)) (literal (valuation q) (463)) (countLit q [237]) (countLit q [238]) (count463 q) 1 (meaning237 q) (meaning463 q) hs
  change valuation q 237 = false ∨ valuation q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := by
  have hs : count467 q = (countLit q [237, 238]) + (countLit q [239, 240]) := List.countP_append (p := literal (baseVal q)) (l₁ := [237, 238]) (l₂ := [239, 240])
  have hm := merge_left (literal (valuation q) (463)) (literal (valuation q) (467)) (countLit q [237, 238]) (countLit q [239, 240]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuation q 463 = false ∨ valuation q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 469 = true := by
  have hs : count469 q = (countLit q [241]) + (countLit q [242]) := List.countP_append (p := literal (baseVal q)) (l₁ := [241]) (l₂ := [242])
  have hm := merge_right (literal (valuation q) (242)) (literal (valuation q) (469)) (countLit q [241]) (countLit q [242]) (count469 q) 1 (meaning242 q) (meaning469 q) hs
  change valuation q 242 = false ∨ valuation q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 471 = true := by
  have hs : count471 q = (countLit q [243]) + (countLit q [244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [243]) (l₂ := [244])
  have hm := merge_left (literal (valuation q) (243)) (literal (valuation q) (471)) (countLit q [243]) (countLit q [244]) (count471 q) 1 (meaning243 q) (meaning471 q) hs
  change valuation q 243 = false ∨ valuation q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 471 = false ∨ valuation q 473 = true := by
  have hs : count473 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_right (literal (valuation q) (471)) (literal (valuation q) (473)) (countLit q [241, 242]) (countLit q [243, 244]) (count473 q) 1 (meaning471 q) (meaning473 q) hs
  change valuation q 471 = false ∨ valuation q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 473 = true := by
  have hs : count473 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_left (literal (valuation q) (469)) (literal (valuation q) (473)) (countLit q [241, 242]) (countLit q [243, 244]) (count473 q) 1 (meaning469 q) (meaning473 q) hs
  change valuation q 469 = false ∨ valuation q 473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = false ∨ valuation q 474 = true := by
  have hs : count473 q = (countLit q [241, 242]) + (countLit q [243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [241, 242]) (l₂ := [243, 244])
  have hm := merge_two (literal (valuation q) (469)) (literal (valuation q) (471)) (literal (valuation q) (474)) (countLit q [241, 242]) (countLit q [243, 244]) (count473 q) 1 1 (meaning469 q) (meaning471 q) (meaning474 q) hs
  change valuation q 469 = false ∨ valuation q 471 = false ∨ valuation q 474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 475 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (473)) (literal (valuation q) (475)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 1 (meaning473 q) (meaning475 q) hs
  change valuation q 473 = false ∨ valuation q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 474 = false ∨ valuation q 476 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (474)) (literal (valuation q) (476)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 2 (meaning474 q) (meaning476 q) hs
  change valuation q 474 = false ∨ valuation q 476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 475 = true := by
  have hs : count475 q = (countLit q [237, 238, 239, 240]) + (countLit q [241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [237, 238, 239, 240]) (l₂ := [241, 242, 243, 244])
  have hm := merge_left (literal (valuation q) (467)) (literal (valuation q) (475)) (countLit q [237, 238, 239, 240]) (countLit q [241, 242, 243, 244]) (count475 q) 1 (meaning467 q) (meaning475 q) hs
  change valuation q 467 = false ∨ valuation q 475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 477 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (475)) (literal (valuation q) (477)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 1 (meaning475 q) (meaning477 q) hs
  change valuation q 475 = false ∨ valuation q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 476 = false ∨ valuation q 478 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (476)) (literal (valuation q) (478)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 2 (meaning476 q) (meaning478 q) hs
  change valuation q 476 = false ∨ valuation q 478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 477 = true := by
  have hs : count477 q = (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) + (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [229, 230, 231, 232, 233, 234, 235, 236]) (l₂ := [237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuation q) (461)) (literal (valuation q) (477)) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (countLit q [237, 238, 239, 240, 241, 242, 243, 244]) (count477 q) 1 (meaning461 q) (meaning477 q) hs
  change valuation q 461 = false ∨ valuation q 477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 477 = false ∨ valuation q 479 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (477)) (literal (valuation q) (479)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 (meaning477 q) (meaning479 q) hs
  change valuation q 477 = false ∨ valuation q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 478 = false ∨ valuation q 480 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (478)) (literal (valuation q) (480)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 2 (meaning478 q) (meaning480 q) hs
  change valuation q 478 = false ∨ valuation q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 479 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuation q) (447)) (literal (valuation q) (479)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 (meaning447 q) (meaning479 q) hs
  change valuation q 447 = false ∨ valuation q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := by
  have hs : count479 q = (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuation q) (447)) (literal (valuation q) (477)) (literal (valuation q) (480)) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count479 q) 1 1 (meaning447 q) (meaning477 q) (meaning480 q) hs
  change valuation q 447 = false ∨ valuation q 477 = false ∨ valuation q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := by
  have hs : count481 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (479)) (literal (valuation q) (481)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuation q 479 = false ∨ valuation q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 480 = false ∨ valuation q 482 = true := by
  have hs : count481 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (480)) (literal (valuation q) (482)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 2 (meaning480 q) (meaning482 q) hs
  change valuation q 480 = false ∨ valuation q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 481 = true := by
  have hs : count481 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuation q) (419)) (literal (valuation q) (481)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 (meaning419 q) (meaning481 q) hs
  change valuation q 419 = false ∨ valuation q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := by
  have hs : count481 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuation q) (419)) (literal (valuation q) (479)) (literal (valuation q) (482)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 1 1 (meaning419 q) (meaning479 q) (meaning482 q) hs
  change valuation q 419 = false ∨ valuation q 479 = false ∨ valuation q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 420 = false ∨ valuation q 482 = true := by
  have hs : count481 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuation q) (420)) (literal (valuation q) (482)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count481 q) 2 (meaning420 q) (meaning482 q) hs
  change valuation q 420 = false ∨ valuation q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_right (literal (valuation q) (482)) (literal (valuation q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 2 (meaning482 q) (meaning484 q) hs
  change valuation q 482 = false ∨ valuation q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 481 = false ∨ valuation q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_two (literal (valuation q) (361)) (literal (valuation q) (481)) (literal (valuation q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 1 1 (meaning361 q) (meaning481 q) (meaning484 q) hs
  change valuation q 361 = false ∨ valuation q 481 = false ∨ valuation q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 484 = true := by
  have hs : count483 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244])
  have hm := merge_left (literal (valuation q) (362)) (literal (valuation q) (484)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]) (count483 q) 2 (meaning362 q) (meaning484 q) hs
  change valuation q 362 = false ∨ valuation q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 484 = false := by
  rw [value484]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count483 q = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true ∨ valuation q 243 = true ∨ valuation q 244 = true := by
  rw [value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242, value243, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1461 = true := by
  have hs : count1461 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuation q) (-6)) (literal (valuation q) (1461)) (countLit q [-4]) (countLit q [-6]) (count1461 q) 1 (meaningNeg6 q) (meaning1461 q) hs
  change (! (valuation q 6)) = false ∨ valuation q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem block28 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.First112
