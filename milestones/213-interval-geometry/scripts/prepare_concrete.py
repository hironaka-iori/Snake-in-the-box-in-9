"""Extract path-level conflict witnesses for the saved retained-(0,6) model."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];P=H.parent/'212-spare-support'
assert not (H/'data/ConcreteData213-audit.json').exists(), 'Initial draft generator: preserve the accepted split proof sources.'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
source=json.loads((P/'data/lower-dimensional-input.json').read_bytes())['8']['vertices']
m=json.loads((P/'data/case-22/model.json').read_bytes())
census=json.loads((P/'data/case-22/support-constraints.json').read_bytes())['families']
assert sha(P/'data/case-22/model.json')=='1a4d81c600d104347a501cfc9bf82db91a3aa04a6ebfd3ea20fcb1ca283aa95b'
base=[((v>>0)&1)+2*((v>>6)&1) for v in source];groups=[0]
for a,b in zip(base,base[1:]):groups.append(groups[-1]+(a==b))
assert len(source)==99 and base==m['z'] and groups==m['group'] and max(groups)==77
pairs=[];partners={};fam=[]
for f in census:
    C=f['clique'];O=f['outside'];partners.update({int(x):ys for x,ys in f['partners'].items()})
    part=[(x,y) for xs in [C,O] for x in xs for y in xs if x<y]
    part += [(x,y) for x in O for y in C if y not in f['partners'][str(x)]]
    pairs+=part;fam.append((C,O))
assert len(pairs)==1291 and len(set(pairs))==1291
certificates=[]
for x,y in pairs:
    i,j=next((i,j) for i,g in enumerate(groups) if g==x for j,h in enumerate(groups) if h==y and (base[i]^base[j])!=3)
    assert x!=y and x%2==y%2
    certificates.append([x,y,i,j])
record={'source_sha256':sha(P/'data/lower-dimensional-input.json'),'model_sha256':sha(P/'data/case-22/model.json'),'source':source,'base':base,'group':groups,'families':[{'chosen':C,'outside':O} for C,O in fam],'partners':partners,'certificates':certificates,'scope':'Every required same-parity inequality has original-index witnesses with nonopposite base corners. These witnesses are prepared for Lean checking against the literal source.'}
(H/'data/concrete-extraction.json').write_text(json.dumps(record,indent=2)+'\n')
natlist=lambda xs:'['+','.join(map(str,xs))+']'
text='''import IntervalGeometry213

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteGeometry213

open IndexedCriterion206 Square209

'''
text+='def source : List Nat := '+natlist(source)+'\n\n'
text+='''def base (v : Nat) : Nat :=
  (if v.testBit 0 then 1 else 0) + (if v.testBit 6 then 2 else 0)

'''
text+='def groups : List Nat := '+natlist(groups)+'\n\n'
text+='''
def baseRaw (i : Nat) : Square209.Vertex :=
  ((source[i]!).testBit 0, (source[i]!).testBit 6)

def z (i : Fin 99) : Square209.Vertex := baseRaw i.val
def group (i : Fin 99) : Nat := groups[i.val]!

'''
for p,(C,O) in enumerate(fam):text+=f'def chosen{p} : List Nat := '+natlist(C)+f'\ndef outside{p} : List Nat := '+natlist(O)+'\n'
text+='\ndef partners : Nat → List Nat\n'
for x,ys in sorted(partners.items()):text+=f'  | {x} => '+natlist(ys)+'\n'
text+='  | _ => []\n\n'
text+='''def withinPairs (xs : List Nat) : List (Nat × Nat) :=
  xs.flatMap (fun x => (xs.filter (fun y => decide (x < y))).map (fun y => (x,y)))

def familyPairs (C O : List Nat) : List (Nat × Nat) :=
  withinPairs C ++ withinPairs O ++
    O.flatMap (fun x => (C.filter (fun y => !(partners x).contains y)).map (fun y => (x,y)))

def requiredPairs : List (Nat × Nat) :=
  familyPairs chosen0 outside0 ++ familyPairs chosen1 outside1

'''
representatives=[groups.index(g) for g in range(78)]
alternates=[next((i for i,h in enumerate(groups) if h==g and base[i]!=base[representatives[g]]),representatives[g]) for g in range(78)]
text+='def firstIndex : List Nat := '+natlist(representatives)+'\n'
text+='def secondIndex : List Nat := '+natlist(alternates)+'\n\n'
text+='''def makeCertificate (xy : Nat × Nat) : Nat × Nat × Nat × Nat :=
  let x := xy.1
  let y := xy.2
  let a := firstIndex[x]!
  let b := firstIndex[y]!
  let i := if baseRaw a = opposite (baseRaw b) then secondIndex[x]! else a
  let j := if baseRaw i = opposite (baseRaw b) then secondIndex[y]! else b
  (x,y,i,j)

def certificates : List (Nat × Nat × Nat × Nat) := requiredPairs.map makeCertificate

'''
text+='''def validCertificate (c : Nat × Nat × Nat × Nat) : Bool :=
  let (x,y,i,j) := c
  decide (i < 99 ∧ j < 99 ∧ groups[i]! = x ∧ groups[j]! = y ∧
    x ≠ y ∧ x % 2 = y % 2 ∧ baseRaw i ≠ opposite (baseRaw j))

theorem extraction :
    source.length = 99 ∧ groups.length = 99 ∧
    groups.all (fun g => decide (g < 78)) = true := by
  decide +kernel

#print axioms extraction

theorem consecutive_groups_data :
    (List.range 98).all (fun i => decide
      (groups[i+1]! = groups[i]! ∨ groups[i+1]! = groups[i]!+1)) = true := by
  decide +kernel

#print axioms consecutive_groups_data

theorem source_group_recurrence :
    groups[0]! = 0 ∧ (List.range 98).all (fun i => decide
      (groups[i+1]! = groups[i]! +
        (if base (source[i+1]!) = base (source[i]!) then 1 else 0))) = true := by
  decide +kernel

#print axioms source_group_recurrence

theorem certificate_coverage :
    certificates.map (fun c => (c.1,c.2.1)) = requiredPairs ∧
    requiredPairs.length = 1291 := by
  constructor
  · simp [certificates, makeCertificate, List.map_map, Function.comp_def]
  · decide +kernel

#print axioms certificate_coverage

theorem certificate_validity : certificates.all validCertificate = true := by
  decide +kernel

#print axioms certificate_validity

end ConcreteGeometry213
'''
start_partners=text.index('def partners :')
start_facts=text.index('theorem extraction :')
end_facts=text.index('theorem certificate_coverage :')
data=text[:start_partners]+text[start_facts:end_facts]+'end ConcreteGeometry213\n'
geometry='import ConcreteData213\n\nset_option Elab.async false\nset_option maxRecDepth 10000\nset_option maxHeartbeats 20000000\n\nnamespace ConcreteGeometry213\nopen IndexedCriterion206 Square209\n\n'+text[start_partners:start_facts]+text[end_facts:]
(H/'lean/ConcreteData213.lean').write_text(data,encoding='utf-8',newline='\n')
(H/'lean/ConcreteGeometry213.lean').write_text(geometry,encoding='utf-8',newline='\n')
print('PREPARED_CONCRETE',len(certificates),'path-level conflict witnesses')
