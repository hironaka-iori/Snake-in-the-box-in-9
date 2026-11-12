from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=H/'data/affine50-free-omit4.json';raw=source.read_bytes();d=json.loads(raw)
assert d['status']=='INFEASIBLE' and d['arguments']['free_ends'] and len(d['dynamic_cycle_cuts'])==3
case=d['affine_case'];perm=case['permutation'];shift=case['translation']
def g(v):return sum(((v>>i)&1)<<perm[i] for i in range(8))^shift
def orb(v):return min(v,g(v))
def neighbours(v):return {orb(v^(1<<k)) for k in range(8)}
ordered=[]
for values in d['dynamic_cycle_cuts']:
 selected=set(values);adj={v:sorted(neighbours(v)&selected) for v in selected};assert all(len(n)==2 for n in adj.values())
 order=[min(selected)];last=None
 while True:
  v=order[-1];w=next(w for w in adj[v] if w!=last)
  if w==order[0]:break
  assert w not in order;order.append(w);last=v
 assert len(order)==36 and set(order)==selected
 assert all(((order[j] in neighbours(v))==(j==i+1 or i==0 and j==35)) for i,v in enumerate(order) for j in range(i+1,36))
 ordered.append(order)
target=H/'data/cycle-cuts.json';assert not target.exists();target.write_text(json.dumps(dict(source_sha256=hashlib.sha256(raw).hexdigest(),ordered_cycles=ordered,permutation=perm,translation=shift),indent=2)+'\n')
terms=' + '.join(f'(x / {1<<i} % 2) * {1<<perm[i]}' for i in range(8))
text=f'''import CycleCut196
namespace CycleData196
def partner (x : Nat) : Nat := Nat.xor ({terms}) {shift}
def orbit (x : Nat) : Nat := min x (partner x)
def Adj (x y : Nat) : Prop := orbit (Nat.xor x 1)=y ∨ orbit (Nat.xor x 2)=y ∨ orbit (Nat.xor x 4)=y ∨ orbit (Nat.xor x 8)=y ∨ orbit (Nat.xor x 16)=y ∨ orbit (Nat.xor x 32)=y ∨ orbit (Nat.xor x 64)=y ∨ orbit (Nat.xor x 128)=y
instance (x y : Nat) : Decidable (Adj x y) := inferInstanceAs (Decidable (_ ∨ _))
def prev (i : Fin 36) : Fin 36 := ⟨(i.val+35)%36,by omega⟩
def next (i : Fin 36) : Fin 36 := ⟨(i.val+1)%36,by omega⟩
'''
for i,cycle in enumerate(ordered):text+=f'def values{i} : Array Nat := #[{", ".join(map(str,cycle))}]\ndef cycle{i} (i : Fin 36) : Nat := values{i}[i.val]!\n'
text+='end CycleData196\n';(H/'lean/CycleData196.lean').write_text(text)
for i in range(3):
 module=f'ConcreteCycle196_{i}'
 text=f'''import CycleData196
namespace {module}
open LayerJoining CycleData196
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem neighbours : ∀ i : Fin 36,
  cycle{i} (prev i) ≠ cycle{i} i ∧ cycle{i} (next i) ≠ cycle{i} i ∧
  cycle{i} (prev i) ≠ cycle{i} (next i) := by decide +kernel
theorem edges : ∀ i : Fin 36,
  Adj (cycle{i} (prev i)) (cycle{i} i) ∧ Adj (cycle{i} (next i)) (cycle{i} i) := by decide +kernel
theorem excluded {{m : Nat}} (p : InducedPath Nat Adj m) :
  ¬ (∀ i : Fin 36, ∃ j, p.vertex j=cycle{i} i) :=
  CycleCut196.noContainedDegreeTwo p cycle{i} prev next neighbours edges
#print axioms neighbours
#print axioms edges
#print axioms excluded
end {module}
'''
 (H/'lean'/(module+'.lean')).write_text(text)
print('Prepared three exact36-vertex cycle exclusions')
