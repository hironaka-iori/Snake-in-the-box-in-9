from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
source=H/'data/lower-dimensional-input.json';v=json.loads(source.read_bytes())['8']['vertices']
mask=25;base=70;cycle=[0,3,4]
def h(x):return (x&~mask)|sum(((x>>c)&1)<<cycle[(j+1)%3] for j,c in enumerate(cycle))
rows=[]
for phase in [1,2]:
    def image(x):
        if x&~mask!=base:return x
        return h(x) if phase==1 else h(h(x))
    w=list(map(image,v));assert len(w)==len(set(w))
    assert all((a^b).bit_count()==1 for a,b in zip(w,w[1:]))
    chords=[dict(indices=[i,j],original=[v[i],v[j]],image=[w[i],w[j]]) for i in range(len(v)) for j in range(i+2,len(v)) if (w[i]^w[j]).bit_count()==1]
    assert chords and all((r['original'][0]^r['original'][1]).bit_count()!=1 for r in chords)
    rows.append(dict(phase=phase,chords=chords,all_original_edges_preserved=True))
record=dict(mask=mask,base=base,cycle=cycle,rows=rows,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(H/'data/exceptional-obstruction.json').write_text(json.dumps(record,indent=2)+'\n')
for r in rows:print(r)
lean='''import CyclicSymmetry204
namespace RotationObstruction204
open CyclicSymmetry204 Phase
def seed : Array Nat := #['''+','.join(map(str,v))+''']
def rotate (x : Nat) : Nat :=
  (x &&& 230) + (if x.testBit 4 then 1 else 0) +
  (if x.testBit 0 then 8 else 0) + (if x.testBit 3 then 16 else 0)
def image (r : Phase) (x : Nat) : Nat := if x &&& 230 = 70 then rot rotate r x else x
def adjacent (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64 ∨ d=128
instance (x y : Nat) : Decidable (adjacent x y) := inferInstanceAs (Decidable (_ ∨ _))
'''
for r in rows:
    i,j=r['chords'][0]['indices'];phase='one' if r['phase']==1 else 'two'
    lean+=f'''theorem chord_{phase} : {i}+1<{j} ∧ ¬adjacent seed[{i}]! seed[{j}]! ∧
    adjacent (image {phase} seed[{i}]!) (image {phase} seed[{j}]!) := by decide +kernel
'''
lean+='''theorem everyNonzeroPhase (r : Phase) (nonzero : r ≠ zero) :
    ∃ i j : Fin 99, i.val+1<j.val ∧ ¬adjacent seed[i.val]! seed[j.val]! ∧
      adjacent (image r seed[i.val]!) (image r seed[j.val]!) := by
  cases r with
  | zero => exact False.elim (nonzero rfl)
'''
for r in rows:
    i,j=r['chords'][0]['indices'];phase='one' if r['phase']==1 else 'two'
    lean+=f'  | {phase} => exact ⟨⟨{i},by decide⟩,⟨{j},by decide⟩,chord_{phase}⟩\n'
lean+='''#print axioms chord_one
#print axioms chord_two
#print axioms everyNonzeroPhase
end RotationObstruction204
'''
(H/'lean/RotationObstruction204.lean').write_bytes(lean.encode('utf-8'))
