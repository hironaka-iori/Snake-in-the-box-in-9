import B112E146
import E112146Clauses00
import E112146Clauses01
import E112146Clauses02
import E112146Clauses03
import E112146Clauses04
import E112146Clauses05
import E112146Clauses06
import E112146Clauses07
import E112146Clauses08
import E112146Clauses09
import E112146Clauses10
import E112146Clauses11
import E112146Clauses12
import E112146Clauses13
import E112146Clauses14
import E112146Clauses15
import E112146Clauses16
import E112146Clauses17
import E112146Clauses18
import E112146Clauses19
import E112146Clauses20
import E112146Clauses21
import E112146Clauses22
import E112146Clauses23
import E112146Clauses24
import E112146Clauses25
namespace Snake9.Regrowth.E112146
noncomputable section
local instance completeDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem all_constraints (q : Snake 81) (h : Conditions q) :
    B112E146.Constraints (valuation q) :=
  ⟨block0 q h, block1 q h, block2 q h, block3 q h, block4 q h, block5 q h, block6 q h, block7 q h, block8 q h, block9 q h, block10 q h, block11 q h, block12 q h, block13 q h, block14 q h, block15 q h, block16 q h, block17 q h, block18 q h, block19 q h, block20 q h, block21 q h, block22 q h, block23 q h, block24 q h, block25 q h⟩

theorem region_exclusion (q : Snake 81) (h : Conditions q) : False :=
  B112E146.constraints_unsat (valuation q) (all_constraints q h)

/-- Fixing these first 112 vertices excludes 192 edges. -/
theorem no192 (p : Snake 192) (hp : Dfs.StartsWith p pre 112) : False := by
  have hc : Conditions (suffix p) := ⟨suffix_head p hp, suffix_covered p hp⟩
  exact B112E146.constraints_unsat (valuation (suffix p)) (all_constraints _ hc)

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
end Snake9.Regrowth.E112146
