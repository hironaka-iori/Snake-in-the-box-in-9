import DfsDecide
import DfsBankData
import DfsBankCert144v2_j24c0

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem keep144v2_26 : search2 (oriented 26)[143]! (banFrom (fun i => (oriented 26)[i]!) 143) 49 = false := by
  rw [show (oriented 26)[143]! = 487 from by decide +kernel,
    show banFrom (fun i => (oriented 26)[i]!) 143 = 13407807730150689878956755591619237842485394673111898617882861524192175671540499813671605316863775369428748834275968284194746494232364728302637205474508799 from by decide +kernel]
  exact keep144v2_24_lit
theorem keep144v2_28 : search2 (oriented 28)[143]! (banFrom (fun i => (oriented 28)[i]!) 143) 49 = false := by
  rw [show (oriented 28)[143]! = 487 from by decide +kernel,
    show banFrom (fun i => (oriented 28)[i]!) 143 = 13407807730150689878956755591619237842485394673111898617882861524192175671540499813671605316863775369428748834275968284194746494232364728302637205474508799 from by decide +kernel]
  exact keep144v2_24_lit
theorem keep144v2_30 : search2 (oriented 30)[143]! (banFrom (fun i => (oriented 30)[i]!) 143) 49 = false := by
  rw [show (oriented 30)[143]! = 487 from by decide +kernel,
    show banFrom (fun i => (oriented 30)[i]!) 143 = 13407807730150689878956755591619237842485394673111898617882861524192175671540499813671605316863775369428748834275968284194746494232364728302637205474508799 from by decide +kernel]
  exact keep144v2_24_lit

end Snake9.Dfs
