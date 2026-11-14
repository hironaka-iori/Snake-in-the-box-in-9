from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
d=json.loads((H/'data/parent-block-census.json').read_bytes())['new_lower_dimensional_shapes'][0]
def arr(v):return '#['+','.join(map(str,v))+']'
s='''import Std
namespace ParentExample203
set_option maxRecDepth 100000
def original : Array Nat := ORIGINAL
def transformed : Array Nat := TRANSFORMED
def blockMap (x : Nat) : Nat :=
  (if x.testBit 4 then 0 else 1)+(if x.testBit 2 then 0 else 2)+
  (if x.testBit 1 then 0 else 4)+(if x.testBit 3 then 8 else 0)+
  (if x.testBit 0 then 0 else 16)+(if x.testBit 5 then 32 else 0)+
  (if x.testBit 6 then 64 else 0)
def change (x : Nat) : Nat := if x &&& 104 = 40 then blockMap x else x
def Adj (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64
instance (x y : Nat) : Decidable (Adj x y) := inferInstanceAs (Decidable (_ ∨ _))
def distance (x y : Nat) : Nat :=
  (List.range 7).foldl (fun n c => n + if (Nat.xor x y).testBit c then 1 else 0) 0
theorem completeSnakes : ∀ i j : Fin 51,
    original[i.val]! < 128 ∧ transformed[i.val]! < 128 ∧
    (original[i.val]! = original[j.val]! ↔ i=j) ∧
    (transformed[i.val]! = transformed[j.val]! ↔ i=j) ∧
    (Adj original[i.val]! original[j.val]! ↔ i.val+1=j.val ∨ j.val+1=i.val) ∧
    (Adj transformed[i.val]! transformed[j.val]! ↔ i.val+1=j.val ∨ j.val+1=i.val) := by
  decide +kernel
theorem wholeImage : ∀ i : Fin 51, change original[i.val]! = transformed[i.val]! := by
  decide +kernel
theorem endpointsDifferent : distance original[0]! original[50]!=6 ∧
    distance transformed[0]! transformed[50]!=2 := by decide +kernel
#print axioms completeSnakes
#print axioms wholeImage
#print axioms endpointsDifferent
end ParentExample203
'''.replace('ORIGINAL',arr(d['original'])).replace('TRANSFORMED',arr(d['vertices'])).replace('[50]!=','[50]! =')
p=H/'lean/ParentExample203.lean';assert not p.exists();p.write_text(s,encoding='utf-8')
(H/'data/parent-example-source.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256((H/'data/parent-block-census.json').read_bytes()).hexdigest(),lean_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),definition='Two simultaneous complemented swaps (0,4),(1,2), selected exactly when remaining bits encode40; original endpoint distance6, image endpoint distance2.'),indent=2)+'\n')
print('PREPARED_PARENT_EXAMPLE')
