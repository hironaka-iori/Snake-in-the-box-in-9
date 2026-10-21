"""Write a Lean witness module for a snake stored as JSON {"vertex_sequence": [...]}.

Modelled on the witness section of work/final_lean/Snake9.lean.  Check with
  LEAN_PATH=work/final_lean/.lake/build/lib/lean:<toolchain>/lib/lean \
  nice -n 19 lean <output>
"""
import json
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from lns import is_snake  # noqa: E402

src, out = sys.argv[1], sys.argv[2]
seq = json.load(open(src))["vertex_sequence"]
assert is_snake(seq)
m = len(seq) - 1
name = f"Witness{m}"
text = f"""import Snake9

/- Explicit {m}-edge snake in Q9 found by the large-neighbourhood search of
milestone 20. Both properties are checked by `decide`. -/
namespace Snake9.{name}
open Snake9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def values : Array Nat := #[{", ".join(map(str, seq))}]

def vertexAt (i : Fin {m + 1}) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct :
    ∀ i j : Fin {m + 1}, vertexAt i = vertexAt j → i = j := by decide

theorem induced :
    ∀ i j : Fin {m + 1}, i.val < j.val →
      (Adj (vertexAt i) (vertexAt j) ↔ i.val + 1 = j.val) := by decide

def witness : Snake {m} := ⟨vertexAt, distinct, induced⟩

theorem lower_bound : Nonempty (Snake {m}) := ⟨witness⟩

end Snake9.{name}

#print axioms Snake9.{name}.lower_bound
"""
open(out, "w").write(text)
print("wrote", out)
