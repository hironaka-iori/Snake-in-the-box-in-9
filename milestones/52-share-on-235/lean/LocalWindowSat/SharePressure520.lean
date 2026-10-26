import LocalWindowSat.SharePressure520.Counters
import LocalWindowSat.SharePressure520.Totalizers
import LocalWindowSat.SharePressure520.Clauses0
import LocalWindowSat.SharePressure520.Clauses1
import LocalWindowSat.SharePressure520.Clauses2
import LocalWindowSat.SharePressure520.Clauses3
import LocalWindowSat.SharePressure520.Clauses4
import LocalWindowSat.SharePressure520.Clauses5
import LocalWindowSat.SharePressure520.Clauses6
import LocalWindowSat.SharePressure520.Clauses7
import LocalWindowSat.SharePressure520.Clauses8
import LocalWindowSat.SharePressure520.Clauses9
import LocalWindowSat.SharePressure520.Clauses10
import LocalWindowSat.SharePressure520.Clauses11
import LocalWindowSat.SharePressure520.Clauses12
import LocalWindowSat.SharePressure520.Clauses13
import LocalWindowSat.SharePressure520.Clauses14
import LocalWindowSat.SharePressure520.Clauses15
import LocalWindowSat.SharePressure520.Clauses16
import LocalWindowSat.SharePressure520.Clauses17
import LocalWindowSat.SharePressure520.Clauses18
import LocalWindowSat.SharePressure520.Clauses19
import LocalWindowSat.SharePressure520.Clauses20
import LocalWindowSat.SharePressure520.Clauses21
import LocalWindowSat.SharePressure520.Clauses22
import LocalWindowSat.SharePressure520.Clauses23
import LocalWindowSat.SharePressure520.Clauses24
import LocalWindowSat.SharePressure520.Clauses25
import LocalWindowSat.SharePressure520.Clauses26
import LocalWindowSat.SharePressure520.Clauses27
import LocalWindowSat.SharePressure520.Clauses28
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.SharePressure520
open Snake9.LocalWindow.Tags
theorem check : checkAllS meaning smeaning resolution ctrs tots window bounds cap tags raw = true := by
  have h29 : ckAllS meaning smeaning resolution ctrs tots window cap [] [] = true := rfl
  have h28 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses28_checked h29
  have h27 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses27_checked h28
  have h26 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses26_checked h27
  have h25 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses25_checked h26
  have h24 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses24_checked h25
  have h23 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses23_checked h24
  have h22 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses22_checked h23
  have h21 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses21_checked h22
  have h20 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses20_checked h21
  have h19 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses19_checked h20
  have h18 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses18_checked h19
  have h17 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses17_checked h18
  have h16 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses16_checked h17
  have h15 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses15_checked h16
  have h14 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses14_checked h15
  have h13 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses13_checked h14
  have h12 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses12_checked h13
  have h11 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses11_checked h12
  have h10 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses10_checked h11
  have h9 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses9_checked h10
  have h8 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses8_checked h9
  have h7 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses7_checked h8
  have h6 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses6_checked h7
  have h5 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses5_checked h6
  have h4 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses4_checked h5
  have h3 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses3_checked h4
  have h2 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses2_checked h3
  have h1 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses1_checked h2
  have h0 := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses0_checked h1
  have h : ckAllS meaning smeaning resolution ctrs tots window cap tags raw = true := h0
  simpa only [checkAllS, counters_checked, totalizers_checked, Bool.true_and] using h
theorem sat : ∀ S E : Nat → Bool, AxiomsS S E window (centresOf window bounds) resolution cap → ∃ τ, cnfTrue τ cnf = true :=
 fun S E h => ⟨tauS S E meaning smeaning resolution ctrs tots, soundS meaning smeaning resolution ctrs tots window bounds cap tags raw check S E h⟩
#print axioms sat
end Snake9.LocalWindow.SharePressure520
