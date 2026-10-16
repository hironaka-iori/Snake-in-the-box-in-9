import Dfs112FirstBoolean
import First112Clauses00
import First112Clauses01
import First112Clauses02
import First112Clauses03
import First112Clauses04
import First112Clauses05
import First112Clauses06
import First112Clauses07
import First112Clauses08
import First112Clauses09
import First112Clauses10
import First112Clauses11
import First112Clauses12
import First112Clauses13
import First112Clauses14
import First112Clauses15
import First112Clauses16
import First112Clauses17
import First112Clauses18
import First112Clauses19
import First112Clauses20
import First112Clauses21
import First112Clauses22
import First112Clauses23
import First112Clauses24
import First112Clauses25
import First112Clauses26
import First112Clauses27
import First112Clauses28
import First112Clauses29
import First112Clauses30
import First112Clauses31
import First112Clauses32
import First112Clauses33
import First112Clauses34
import First112Clauses35
import First112Clauses36
import First112Clauses37
import First112Clauses38
import First112Clauses39
import First112Clauses40
import First112Clauses41
import First112Clauses42
import First112Clauses43
import First112Clauses44
import First112Clauses45
import First112Clauses46
import First112Clauses47
import First112Clauses48
namespace Snake9.Regrowth.First112
noncomputable section
local instance completeDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem all_constraints (q : Snake 81) (h : Conditions q) :
    Dfs112FirstBoolean.Constraints (valuation q) :=
  ⟨block0 q h, block1 q h, block2 q h, block3 q h, block4 q h, block5 q h, block6 q h, block7 q h, block8 q h, block9 q h, block10 q h, block11 q h, block12 q h, block13 q h, block14 q h, block15 q h, block16 q h, block17 q h, block18 q h, block19 q h, block20 q h, block21 q h, block22 q h, block23 q h, block24 q h, block25 q h, block26 q h, block27 q h, block28 q h, block29 q h, block30 q h, block31 q h, block32 q h, block33 q h, block34 q h, block35 q h, block36 q h, block37 q h, block38 q h, block39 q h, block40 q h, block41 q h, block42 q h, block43 q h, block44 q h, block45 q h, block46 q h, block47 q h, block48 q h⟩

/-- Fixing the first 112 vertices of the first bank path excludes 192 edges. -/
theorem no192 (p : Snake 192) (hp : Dfs.StartsWith p pre 112) : False := by
  have hc : Conditions (suffix p) := ⟨suffix_head p hp, suffix_covered p hp⟩
  exact Dfs112FirstBoolean.constraints_unsat (valuation (suffix p)) (all_constraints _ hc)

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

end
end Snake9.Regrowth.First112
