import B112E057
import E112057Clauses00
import E112057Clauses01
import E112057Clauses02
import E112057Clauses03
import E112057Clauses04
import E112057Clauses05
import E112057Clauses06
import E112057Clauses07
import E112057Clauses08
import E112057Clauses09
import E112057Clauses10
import E112057Clauses11
import E112057Clauses12
import E112057Clauses13
import E112057Clauses14
import E112057Clauses15
import E112057Clauses16
import E112057Clauses17
import E112057Clauses18
import E112057Clauses19
import E112057Clauses20
import E112057Clauses21
import E112057Clauses22
import E112057Clauses23
import E112057Clauses24
import E112057Clauses25
import E112057Clauses26
import E112057Clauses27
import E112057Clauses28
import E112057Clauses29
import E112057Clauses30
import E112057Clauses31
import E112057Clauses32
import E112057Clauses33
import E112057Clauses34
import E112057Clauses35
import E112057Clauses36
import E112057Clauses37
import E112057Clauses38
import E112057Clauses39
import E112057Clauses40
import E112057Clauses41
import E112057Clauses42
import E112057Clauses43
import E112057Clauses44
import E112057Clauses45
import E112057Clauses46
import E112057Clauses47
import E112057Clauses48
import E112057Clauses49
import E112057Clauses50
import E112057Clauses51
import E112057Clauses52
import E112057Clauses53
import E112057Clauses54
import E112057Clauses55
import E112057Clauses56
import E112057Clauses57
import E112057Clauses58
import E112057Clauses59
import E112057Clauses60
import E112057Clauses61
import E112057Clauses62
import E112057Clauses63
namespace Snake9.Regrowth.E112057
noncomputable section
local instance completeDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem all_constraints (q : Snake 81) (h : Conditions q) :
    B112E057.Constraints (valuation q) :=
  ⟨block0 q h, block1 q h, block2 q h, block3 q h, block4 q h, block5 q h, block6 q h, block7 q h, block8 q h, block9 q h, block10 q h, block11 q h, block12 q h, block13 q h, block14 q h, block15 q h, block16 q h, block17 q h, block18 q h, block19 q h, block20 q h, block21 q h, block22 q h, block23 q h, block24 q h, block25 q h, block26 q h, block27 q h, block28 q h, block29 q h, block30 q h, block31 q h, block32 q h, block33 q h, block34 q h, block35 q h, block36 q h, block37 q h, block38 q h, block39 q h, block40 q h, block41 q h, block42 q h, block43 q h, block44 q h, block45 q h, block46 q h, block47 q h, block48 q h, block49 q h, block50 q h, block51 q h, block52 q h, block53 q h, block54 q h, block55 q h, block56 q h, block57 q h, block58 q h, block59 q h, block60 q h, block61 q h, block62 q h, block63 q h⟩

theorem region_exclusion (q : Snake 81) (h : Conditions q) : False :=
  B112E057.constraints_unsat (valuation q) (all_constraints q h)

/-- Fixing these first 112 vertices excludes 192 edges. -/
theorem no192 (p : Snake 192) (hp : Dfs.StartsWith p pre 112) : False := by
  have hc : Conditions (suffix p) := ⟨suffix_head p hp, suffix_covered p hp⟩
  exact B112E057.constraints_unsat (valuation (suffix p)) (all_constraints _ hc)

theorem no_long_prefix {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ Dfs.StartsWith p pre 112 := by
  intro hp
  apply no192 (takePrefix p hm)
  intro i hi h193
  exact hp i hi (by omega)

theorem no_long_suffix {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ Dfs.EndsWith p pre 112 := no_long_prefix hm (reverseSnake p)

#print axioms no192
#print axioms no_long_prefix
#print axioms no_long_suffix
#print axioms region_exclusion

end
end Snake9.Regrowth.E112057
