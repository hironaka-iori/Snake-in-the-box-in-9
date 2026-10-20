import W2423CG1C0
import W2423CG1C1
import W2423CG1C2
import W2423CG1C3
import W2423CMain
namespace W2423C
open WinCNF W223G1
theorem check_T : F.all (check T) = true := by
  simp only [F, List.all_append, chk0, chk1, chk2, chk3, chk4, chk5, chk6, chk7, chk8, chk9, chk10, chk11, chk12, chk13, chk14, chk15, chk16, chk17, chk18, chk19, chk20, chk21, chk22, chk23, chk24, chk25, chk26, chk27, chk28, chk29, chk30, chk31, Bool.and_self]
theorem refuted : WinG1.Refuted4 3 4 2 2 4 4 2 2 3 3 :=
  ⟨T, F, unsatF, blocksOK_T, check_T, by decide +kernel, by decide⟩
end W2423C
