"""Generate direct cycle obstructions for every rejected eleven-direction word."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
words=json.loads((HERE/'data/rejected-words.json').read_text())
for begin in range(0,len(words),8):
    lines=['import GenericWindow','namespace Snake9.LocalWindow.FamilyCharge67',
        'open CriticalExtension60','set_option maxHeartbeats 0','set_option maxRecDepth 100000']
    for i,ds in enumerate(words[begin:begin+8],begin):
        W=[0]
        for d in ds:W.append(W[-1]^(1<<d))
        lines += [f'namespace Rejected{i:02d}',f'def W : List Nat := {W}',f'def ds : List Nat := {ds}',
          'theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩',
          'theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel',
          '''theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP''',
          '#print axioms canonical','#print axioms cycle','#print axioms impossible',f'end Rejected{i:02d}']
    lines.append('end Snake9.LocalWindow.FamilyCharge67')
    (HERE/f'lean/ValidityBatch{begin//8:02d}.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
