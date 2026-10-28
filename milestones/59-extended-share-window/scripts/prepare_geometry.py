"""Batch finite kernel checks to avoid repeated imports for each window."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parents[1]
rows=json.loads((HERE/'data/geometry.json').read_text())['patterns']
positive=[(i,r) for i,r in enumerate(rows) if r['share_lower']>0]
modules=[]
record=json.loads((HERE/'logs/build-record.json').read_text())
completed={r['module']:r for r in record['records'] if r['exit_code']==0}
for start in range(0,len(positive),12):
    name=f'GeometryBatch{start//12:02d}';modules.append(name)
    target=HERE/'lean'/f'{name}.lean'
    if name in completed and target.exists() and hashlib.sha256(target.read_bytes()).hexdigest()==completed[name]['source_sha256']:
        continue
    src=['import MaskShareBridge','namespace Snake9.LocalWindow.ExtendedShare59',
         'open ForcedShare58','set_option maxHeartbeats 0','set_option maxRecDepth 100000']
    for i,r in positive[start:start+12]:
        n=f'G{i:03d}'
        src.append(f'''
namespace {n}
def W : List Nat := {r['vertices']}
def ds : List Nat := {r['directions']}
def D : List Nat := {r['forced_absent']}
def C : List Nat := {r['centres']}
def mask : Nat := {sum(1<<x for x in r['forced_absent'])}
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : {r['share_lower']} ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    {r['share_lower']} ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:={r['share_lower']}) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end {n}
''')
    src.append('end Snake9.LocalWindow.ExtendedShare59')
    (HERE/'lean'/f'{name}.lean').write_text('\n'.join(src)+'\n',encoding='utf-8')
(HERE/'lean/GeometryCatalogue.lean').write_text('\n'.join('import '+m for m in modules)+'\n')
print('Generated',len(positive),'certificates in',len(modules),'batches')
