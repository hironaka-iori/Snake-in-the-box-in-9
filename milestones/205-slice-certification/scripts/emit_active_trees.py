from pathlib import Path
import collections,hashlib,itertools,json
H=Path(__file__).resolve().parents[1];source=H/'data/lower-dimensional-input.json';seed=json.loads(source.read_bytes())['8']['vertices']
data='''import ActiveTree205
namespace HistoryData205
def seed : Array Nat := #['''+','.join(map(str,seed))+''']
def adjacent (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64 ∨ d=128
instance (x y : Nat) : Decidable (adjacent x y) := inferInstanceAs (Decidable (_ ∨ _))
end HistoryData205
'''
(H/'lean/HistoryData205.lean').write_bytes(data.encode('utf-8'));records=[];order=['ActiveTree205','HistoryData205']
for a,b in itertools.combinations(range(8),2):
    name=f'ActivePair205_{a}_{b}';code='import HistoryData205\nnamespace '+name+'\nopen HistoryData205 ActiveTree205\n'
    for parity in range(2):
        ns='Even' if parity==0 else 'Odd';mask=255^((1<<a)|(1<<b));active=lambda x:((x>>a)^(x>>b))&1==parity
        witness={}
        for i,x in enumerate(seed):
            if active(x):witness.setdefault(x&mask,i)
        words=[min(witness)];parents=[0];seen={words[0]:0};cursor=0
        while cursor<len(words):
            u=words[cursor]
            for c in range(8):
                w=u^(1<<c)
                if w in witness and w not in seen:seen[w]=len(words);words.append(w);parents.append(cursor)
            cursor+=1
        assert len(words)==len(witness);n=len(words);pos=[witness[w] for w in words];cover=[seen[x&mask] if active(x) else 0 for x in seed]
        code+='namespace '+ns+'\n'
        for field,values in [('words',words),('parents',parents),('positions',pos),('cover',cover)]:code+='def '+field+' : Array Nat := #['+','.join(map(str,values))+']\n'
        code+=f'''def active (x : Nat) : Bool := (Bool.xor (x.testBit {a}) (x.testBit {b})) == {'true' if parity else 'false'}
def base (x : Nat) : Nat := x &&& {mask}
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageCheck : (List.range 99).all (fun i => decide (active seed[i]! = true →
    cover[i]! < {n} ∧ words[cover[i]!]! = base seed[i]!)) = true := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true →
    cover[i.val]! < {n} ∧ words[cover[i.val]!]! = base seed[i.val]! := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp coverageCheck i.val (List.mem_range.mpr i.isLt))
theorem parentCheck : (List.range {n}).all (fun j => decide (positions[j]! < 99 ∧
    active seed[positions[j]!]! = true ∧ words[j]! = base seed[positions[j]!]! ∧
    (0<j → parents[j]! < j ∧ adjacent words[parents[j]!]! words[j]!))) = true := by decide +kernel
theorem parentFacts : ∀ j : Fin {n}, positions[j.val]! < 99 ∧
    active seed[positions[j.val]!]! = true ∧ words[j.val]! = base seed[positions[j.val]!]! ∧
    (0<j.val → parents[j.val]! < j.val ∧ adjacent words[parents[j.val]!]! words[j.val]!) := by
  intro j
  exact of_decide_eq_true (List.all_eq_true.mp parentCheck j.val (List.mem_range.mpr j.isLt))
theorem constantOnActive {{W : Type}} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) {n} Selected adjacent f
  · intro j hj
    have h := parentFacts ⟨j,hj⟩
    exact ⟨⟨positions[j]!,h.1⟩,h.2.1,h.2.2.1.symm⟩
  · intro x hx
    rcases hx with ⟨i,ha,hb⟩
    have h := coverage i ha
    exact ⟨cover[i.val]!,h.1,h.2.trans hb⟩
  · intro j hpos hj; exact ((parentFacts ⟨j,hj⟩).2.2.2 hpos).1
  · intro j hpos hj; exact ((parentFacts ⟨j,hj⟩).2.2.2 hpos).2
  · exact same
#print axioms coverage
#print axioms parentFacts
#print axioms constantOnActive
end {ns}
'''
        records.append(dict(coordinates=[a,b],parity=parity,vertices=n,module=name,namespace=ns,words=words,parents=parents,positions=pos,cover=cover))
    code+='end '+name+'\n';(H/'lean'/(name+'.lean')).write_bytes(code.encode('utf-8'));order.append(name)
out=dict(records=records,module_order=order,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All56 source-specific active graphs, with full selected-set coverage and explicit earlier-parent spanning trees. Lean acceptance is separate.')
(H/'data/active-trees.json').write_text(json.dumps(out,indent=2)+'\n');print('EMITTED',len(records),'active trees')
