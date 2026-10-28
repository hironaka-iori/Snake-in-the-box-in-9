from pathlib import Path
from fractions import Fraction
import json
HERE=Path(__file__).resolve().parents[1]
read=lambda p:json.loads((HERE/p).read_text())
rows=read('data/geometry.json')['patterns'];positive=[(i,r) for i,r in enumerate(rows) if r['lower']>0]
for begin in range(0,len(positive),8):
    src=['import GenericWindow','namespace Snake9.LocalWindow.FamilyShare61',
         'open ForcedShare58 ExtendedShare59 CriticalExtension60',
         'set_option maxHeartbeats 0','set_option maxRecDepth 100000']
    for i,r in positive[begin:begin+8]:
        offset=len(r['directions'])-5
        src.append(f'''
namespace G{i:03d}
def W : List Nat := {r['vertices']}
def ds : List Nat := {r['directions']}
def D : List Nat := {r['forced_absent']}
def C : List Nat := {r['centres']}
def mask : Nat := {sum(1<<x for x in r['forced_absent'])}
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : {r['lower']} ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    {r['lower']} ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+{offset})))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:={r['lower']}) (mask:=mask) (start:={offset})
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G{i:03d}
''')
    src.append('end Snake9.LocalWindow.FamilyShare61')
    (HERE/'lean'/f'GeometryBatch{begin//8:02d}.lean').write_text('\n'.join(src),encoding='utf-8')
rejected=sorted({tuple(r['directions']) for r in read('data/lift-11.json')['rejected']})
for begin in range(0,len(rejected),9):
    src=['import GenericWindow','namespace Snake9.LocalWindow.FamilyValidity61',
         'open CriticalExtension60','set_option maxHeartbeats 0','set_option maxRecDepth 100000']
    for i,ds in enumerate(rejected[begin:begin+9],begin):
        w=[0]
        for d in ds:w.append(w[-1]^(1<<d))
        src.append(f'''
namespace F{i:02d}
def W : List Nat := {w}
def ds : List Nat := {list(ds)}
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F{i:02d}
''')
    src.append('end Snake9.LocalWindow.FamilyValidity61')
    (HERE/'lean'/f'ValidityBatch{begin//9}.lean').write_text('\n'.join(src),encoding='utf-8')
for result in read('data/analyses.json'):
    n,kind=result['length'],result['mode'];data=read(f'data/lift-{n}.json');es=data['edges']
    triples=[(e['u'],e['v'],120*e['counts'][-1]+e['base_share'] if kind=='base' else e['weight']) for e in es]
    cycle=[triples[i] for i in result['cycle']];mu=Fraction(result['integer_mean']);p,d=mu.numerator,mu.denominator
    name=f'Potential{n}{kind.capitalize()}'
    src=f'''import FinitePotential
namespace Snake9.CriticalFamily61.{name}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def edges : List (Nat × Nat × Nat) := {triples}
def potential : List Nat := {result['potential']}
def cycle : List (Nat × Nat × Nat) := {cycle}
theorem checked : checkEdges {p} {d} potential edges=true := by decide +kernel
theorem every_closed_walk (n : Nat) (f w : Nat → Nat)
    (h : ∀ i<n, (f i,f (i+1),w i)∈edges) (hc : f n=f 0) :
    n*{p} ≤ {d}*(∑ i ∈ Finset.range n, w i) := by
  apply closed_bound {p} {d} n (fun x => potential.getD x 0) f w ?_ hc
  intro i hi
  exact edge_of_check checked (h i hi)
theorem attaining_cycle : (List.range cycle.length).all (fun i =>
    edges.contains (cycle.getD i (0,0,0)) &&
    decide ((cycle.getD i (0,0,0)).2.1=(cycle.getD ((i+1)%cycle.length) (0,0,0)).1))=true := by decide +kernel
theorem attainment : {d}*(cycle.map (fun e => e.2.2)).sum={p}*cycle.length := by decide +kernel
#print axioms checked
#print axioms every_closed_walk
#print axioms attaining_cycle
#print axioms attainment
end Snake9.CriticalFamily61.{name}
'''
    (HERE/'lean'/f'{name}.lean').write_text(src,encoding='utf-8')
print('Generated',len(positive),'share certificates,',len(rejected),'validity controls and four finite potentials')
