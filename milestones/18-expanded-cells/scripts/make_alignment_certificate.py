"""Generate a finite cube-map certificate for the selected alignment."""
import json
from pathlib import Path
from align_bank import transform
HERE=Path(__file__).resolve().parents[1]

def main():
    r=json.loads((HERE/'data/aligned-seed.json').read_text())
    mapping=[transform(v,r['inner_coordinates'],r['inner_permutation'],r['inner_shift'],r['outer_shift']) for v in range(512)]
    inverse=[mapping.index(v) for v in range(512)]
    order=[r['inner_coordinates'][i] for i in r['inner_permutation']]+[i for i in range(9) if i not in r['inner_coordinates']]
    dest=[order.index(i) for i in range(9)]
    shift=r['inner_shift']+32*r['outer_shift']
    forward=' + '.join(f'(if n.testBit {i} then {1<<j} else 0)' for j,i in enumerate(order))
    backward=' + '.join(f'(if n.testBit {j} then {1<<i} else 0)' for j,i in enumerate(order))
    source='''import CubeLocal
import Mathlib.Tactic
namespace Snake9.ExpandedCells
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem edge_checks_sound (f : Vertex → Vertex)
    (h : ∀ v a, Adj (f v) (f (vxor v (unit a)))) {v w : Vertex}
    (ha : Adj v w) : Adj (f v) (f w) := by
  obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip v w).mp ha
  have hw : w = vxor v (unit ⟨k,hk⟩) := Fin.ext he
  rw [hw]
  exact h v ⟨k,hk⟩

def permute (n : Nat) : Nat := FORWARD
def inversePermute (n : Nat) : Nat := BACKWARD
def align (v : Vertex) : Vertex := ⟨(permute v.val ^^^ SHIFT) % 512, Nat.mod_lt _ (by decide)⟩
def undo (v : Vertex) : Vertex := ⟨inversePermute (v.val ^^^ SHIFT) % 512, Nat.mod_lt _ (by decide)⟩
def bitPerm (a : Coord) : Coord := ⟨(#[DEST])[a.val]! % 9, Nat.mod_lt _ (by decide)⟩
theorem undo_align : ∀ v, undo (align v) = v := by decide
#print axioms undo_align
theorem flip_rule : ∀ v a, align (vxor v (unit a)) = vxor (align v) (unit (bitPerm a)) := by decide
#print axioms flip_rule
theorem bitPerm_surjective : ∀ b, ∃ a, bitPerm a = b := by decide
theorem align_injective : Function.Injective align := by
  intro v w he
  have h := congrArg undo he
  simpa only [undo_align] using h
theorem align_adj (v w : Vertex) : Adj (align v) (align w) ↔ Adj v w := by
  constructor
  · intro h
    obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip _ _).mp h
    obtain ⟨a,ha⟩ := bitPerm_surjective ⟨k,hk⟩
    have hw : align w = vxor (align v) (unit (bitPerm a)) := by
      rw [ha]
      exact Fin.ext he
    have hw' : w = vxor v (unit a) := align_injective (hw.trans (flip_rule v a).symm)
    rw [hw']
    exact (adj_iff_coordinate_flip _ _).mpr ⟨a.val,a.isLt,rfl⟩
  · apply edge_checks_sound align
    intro u a
    rw [flip_rule]
    exact (adj_iff_coordinate_flip _ _).mpr ⟨(bitPerm a).val,(bitPerm a).isLt,rfl⟩
def alignSnake {m : Nat} (p : Snake m) : Snake m where
  vertex i := align (p.vertex i)
  distinct i j h := p.distinct i j (align_injective h)
  induced i j hij := (align_adj _ _).trans (p.induced i j hij)
#print axioms edge_checks_sound
#print axioms bitPerm_surjective
#print axioms align_injective
#print axioms align_adj
#print axioms alignSnake
end Snake9.ExpandedCells
'''.replace('FORWARD',forward).replace('BACKWARD',backward).replace('SHIFT',str(shift)).replace('DEST',','.join(map(str,dest)))
    (HERE/'lean').mkdir(exist_ok=True)
    (HERE/'logs').mkdir(exist_ok=True)
    (HERE/'lean/Alignment.lean').write_text(source,encoding='utf-8',newline='\n')
    print('Generated permutation and inverse on 512 vertices.')

if __name__=='__main__':main()
