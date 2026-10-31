import Std
import Lean
theorem deliberatelyFalse : False := by decide +kernel
#print axioms deliberatelyFalse
