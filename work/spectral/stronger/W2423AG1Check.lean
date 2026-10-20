import W2423AG1C0
import W2423AG1C1
import W2423AG1C2
import W2423AG1C3
import W2423AMain
namespace W2423A
open WinCNF W223G1
theorem check_T : F.all (check T) = true := by
  simp only [F, List.all_append, chk0, chk1, chk2, chk3, chk4, chk5, chk6, chk7, chk8, chk9, chk10, chk11, chk12, chk13, chk14, chk15, chk16, chk17, chk18, chk19, chk20, chk21, chk22, chk23, chk24, chk25, chk26, Bool.and_self]
theorem refuted : WinG1.Refuted4 0 3 2 2 4 4 2 2 3 3 :=
  ⟨T, F, unsatF, blocksOK_T, check_T, by decide +kernel, by decide⟩
end W2423A
