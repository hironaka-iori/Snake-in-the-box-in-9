import FastShare00.Main
import LocalWindowCnf.ParallelShare00
import FastRupLocalWindow
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.FastParallelShare00
theorem exact_cnf : FastShare00.F = ParallelShare00.cnf := by rfl
theorem unsat : Unsat ParallelShare00.cnf := by
  rw [← exact_cnf]
  exact unsat_of_fastRup FastShare00_unsat
#print axioms unsat
end Snake9.LocalWindow.FastParallelShare00
