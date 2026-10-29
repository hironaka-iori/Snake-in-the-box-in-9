from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parents[1]
rows=json.loads((HERE/'data/choices.json').read_text())['rows']
positive=[r for r in rows if r['lower']>r['old']]
compact={r['edge']:r['cases'] for r in json.loads((HERE/'data/compact-certificates.json').read_text())['rows']}
if '--pilot' in sys.argv:positive=positive[:1]
opt=lambda v:'none' if v is None else 'some '+str(v)
for r in positive:
    i=r['edge'];clauses=[];checks=[]
    for j,b in enumerate(r['branches']):
        a,c=b['choices'];small=compact[i][j]
        assert small['choices']==b['choices']
        D=small['forced'];mask=small['mask']
        clauses.append(f'  | {opt(a)}, {opt(c)} => ({D}, {mask})')
        checks.append(f'theorem case{j:02d} : branchCheck W A B C {r["lower"]} ({opt(a)}) ({opt(c)}) (cert ({opt(a)}) ({opt(c)})).1 (cert ({opt(a)}) ({opt(c)})).2=true := by decide +kernel')
    clauses.append('  | _, _ => ([],0)')
    width=len(r['B'])+1
    def conj(names):
        return names[0] if len(names)==1 else '⟨'+names[0]+', '+conj(names[1:])+'⟩'
    proof=conj([conj([f'case{j:02d}' for j in range(k,k+width)]) for k in range(0,len(checks),width)])
    src=f'''import NeighbourChoice
namespace Snake9.LocalWindow.NeighbourChoice64.E{i:03d}
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := {r['vertices']}
def ds : List Nat := {r['directions']}
def A : List Nat := {r['A']}
def B : List Nat := {r['B']}
def C : List Nat := {r['centres']}
def cert : Option Nat → Option Nat → List Nat × Nat
'''+ '\n'.join(clauses)+f'''
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem supported : supportCheck W C=true := by decide +kernel
theorem pairA : pairCheck W A=true := by decide +kernel
theorem pairB : pairCheck W B=true := by decide +kernel
'''+ '\n'.join(checks)+f'''
theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    branchCheck W A B C {r['lower']} a b (cert a b).1 (cert a b).2))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact {proof}
theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    {r['lower']}≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  neighbour_in_snake (W:=W) (cs:=ds) (A:=A) (B:=B) (C:=C) (L:={r['lower']}) (start:=6)
    cert canonical (by decide) (by decide) rfl supported pairA pairB checked p P r hr hP
#print axioms canonical
#print axioms supported
#print axioms pairA
#print axioms pairB
#print axioms checked
#print axioms in_snake
end Snake9.LocalWindow.NeighbourChoice64.E{i:03d}
'''
    (HERE/f'lean/Edge{i:03d}.lean').write_text(src,encoding='utf-8')
print('Generated',len(positive),'local instances')
