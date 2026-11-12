from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
accepted=json.loads((H/'data/Symmetry195-audit.json').read_text());assert accepted['status']=='PASS'
order=[]
for chunk in range(8):
 module=f'SymmetryEdges195_{chunk}';order.append(module)
 text=f'''import Symmetry195
namespace SymmetryEdges195_{chunk}
open Symmetry195
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem edges : ∀ v : Fin 32, ∀ k : Fin 8,
  Adj (partner ({32*chunk}+v.val))
    (partner (Nat.xor ({32*chunk}+v.val) (2^k.val))) ∧
  ¬ Adj (Nat.xor ({32*chunk}+v.val) (2^k.val)) (partner ({32*chunk}+v.val)) := by
  decide +kernel
#print axioms edges
end SymmetryEdges195_{chunk}
'''
 path=H/'lean'/(module+'.lean');assert not path.exists();path.write_text(text)
 plan=dict(new_module_order=[module],source_sha256={module:sha(path),'Symmetry195':sha(H/'lean/Symmetry195.lean')},
  input_pins={str(H/'scripts/native_resources.py'):sha(H/'scripts/native_resources.py')},lean_bin='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',
  search_paths=[str(H/'build')],checker_sha256=sha(H/'scripts/check_core.py'))
 (H/'data'/(module+'-execution.json')).write_text(json.dumps(plan,indent=2)+'\n')
(H/'data/edge-proof-order.json').write_text(json.dumps(order,indent=2)+'\n')
