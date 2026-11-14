from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];P=H.parent/'212-spare-support'
assert not (H/'data/ConcreteParity214-audit.json').exists()
m=json.loads((P/'data/case-22/model.json').read_bytes())
g=m['group'];z=m['z']
boundaries=[next(i for i in range(98) if g[i]==k and g[i+1]==k+1) for k in range(77)]
assert all(z[i]==z[i+1] for i in boundaries)
even=sum(1<<u for u in range(64) if u.bit_count()%2==0)
odd=sum(1<<u for u in range(64) if u.bit_count()%2==1)
record={'source_model':str(P/'data/case-22/model.json'),'source_sha256':hashlib.sha256((P/'data/case-22/model.json').read_bytes()).hexdigest(),'boundaries':boundaries,'even_mask':even,'odd_mask':odd,'scope':'Literal boundary witnesses and parity masks prepared for kernel checking.'}
(H/'data/parity-extraction.json').write_text(json.dumps(record,indent=2)+'\n')
source='''import ConcreteData213
import WordParity214

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace ConcreteParity214
open ConcreteGeometry213 WordParity214 IndexedCriterion206

def word (u : Nat) : List Bool := (List.range 6).map (fun k => u.testBit k)

def boundary : List Nat := BOUNDARIES

theorem boundary_certificate :
    (List.range 77).all (fun g => decide
      (boundary[g]! < 98 ∧ groups[boundary[g]!]! = g ∧
       groups[boundary[g]!+1]! = g+1 ∧
       baseRaw (boundary[g]!) = baseRaw (boundary[g]!+1))) = true := by
  decide +kernel

def pool (b : Bool) : List Nat :=
  (List.range 64).filter (fun u => parity (word u) == b)

def parityMask (b : Bool) : Nat := if b then ODDMASK else EVENMASK

theorem pool_lengths : (pool false).length = 32 ∧ (pool true).length = 32 := by
  decide +kernel

theorem mask_certificate :
    (List.range 64).all (fun u =>
      (parityMask false).testBit u == (parity (word u) == false) &&
      (parityMask true).testBit u == (parity (word u) == true)) = true := by
  decide +kernel

#print axioms boundary_certificate
#print axioms pool_lengths
#print axioms mask_certificate
end ConcreteParity214
'''.replace('BOUNDARIES',str(boundaries)).replace('ODDMASK',str(odd)).replace('EVENMASK',str(even))
(H/'lean/ConcreteParity214.lean').write_text(source,encoding='utf-8',newline='\n')
print('PREPARED_BOUNDARIES_AND_PARITY_MASKS')
