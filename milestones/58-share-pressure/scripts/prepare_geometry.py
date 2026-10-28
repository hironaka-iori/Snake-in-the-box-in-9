"""Generate kernel-reduced geometric checks and arbitrary-snake consequences."""
from pathlib import Path
import json

HERE = Path(__file__).resolve().parents[1]
records = json.loads((HERE / 'data/forced-geometry.json').read_text())['patterns']
dest = HERE / 'lean/Geometry'
dest.mkdir(exist_ok=True)
modules = []
for i, row in enumerate(records):
    if row['share_lower'] == 0:
        continue
    ds = row['directions']
    path = [0]
    for d in ds:
        path.append(path[-1] ^ (1 << d))
    name = f'G{i:03d}'
    modules.append('Geometry.' + name)
    src = f'''import ForcedShareBridge

namespace Snake9.LocalWindow.ForcedShare58.{name}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def W : List Nat := {path}
def ds : List Nat := {ds}
def D : List Nat := {row['forced_absent']}
def C : List Nat := {row['centres']}

theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : {row['share_lower']} ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel

theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    {row['share_lower']} ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+3)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP

#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end Snake9.LocalWindow.ForcedShare58.{name}
'''
    (dest / (name + '.lean')).write_text(src, encoding='utf-8')
(HERE / 'lean/GeometryCatalogue.lean').write_text(
    '\n'.join('import ' + m for m in modules) + '\n', encoding='utf-8')
print('Generated', len(modules), 'geometric certificates')
