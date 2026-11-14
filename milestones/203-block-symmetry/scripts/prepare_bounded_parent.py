from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
source=(H/'lean/ParentExample203.lean').read_text(encoding='utf-8')
prefix=source.split('theorem completeSnakes')[0].replace('namespace ParentExample203','namespace ParentData203')
tail=source.split('theorem wholeImage',1)[1].split('#print axioms')[0]
data=prefix+'''def pairProperty (i j : Nat) : Prop :=
    (original[i]! = original[j]! ↔ i=j) ∧
    (transformed[i]! = transformed[j]! ↔ i=j) ∧
    (Adj original[i]! original[j]! ↔ i+1=j ∨ j+1=i) ∧
    (Adj transformed[i]! transformed[j]! ↔ i+1=j ∨ j+1=i)
instance (i j : Nat) : Decidable (pairProperty i j) := inferInstanceAs (Decidable (_ ∧ _))
theorem bounds : ∀ i : Fin 51, original[i.val]! < 128 ∧ transformed[i.val]! < 128 := by decide +kernel
theorem wholeImage'''+tail+'''#print axioms bounds
#print axioms wholeImage
#print axioms endpointsDifferent
end ParentData203
'''
files={'ParentData203':data}
for k in range(51):
    files['ParentRows203_'+str(k)]=f'''import ParentData203
namespace ParentRows203_{k}
open ParentData203
set_option maxRecDepth 100000
theorem rows : ∀ i : Fin 1, ∀ j : Fin 51, i.val+{k}<51 → pairProperty (i.val+{k}) j.val := by
  decide +kernel
#print axioms rows
end ParentRows203_{k}
'''
s='\n'.join('import ParentRows203_'+str(k) for k in range(51))+'''
namespace ParentComplete203
open ParentData203
theorem allPairs (i j : Fin 51) : pairProperty i.val j.val := by
  have hi := i.isLt
'''
for k in range(51):
    if k<50:s+=f'  by_cases h{k} : i.val = {k}\n  · '
    else:s+='  '
    indent='    ' if k<50 else '  '
    if k==50:s+='have h50 : i.val=50 := by omega\n  '
    s+=f'have h := ParentRows203_{k}.rows ⟨0,by omega⟩ j (by omega)\n'
    s+=indent+f'simpa only [Fin.val_mk,Nat.zero_add,h{k}] using h\n'
s+='#print axioms allPairs\nend ParentComplete203\n';files['ParentComplete203']=s
for name,code in files.items():
    p=H/'lean'/(name+'.lean')
    if p.exists():assert p.read_text(encoding='utf-8')==code,name
    else:p.write_bytes(code.encode('utf-8'))
record=H/'data/parent-bounded-source.json'
record.write_text(json.dumps(dict(width=1,source_sha256={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in files},scope='Complete51-by51 pair statement split into51one-row proofs; bounds,image and endpoint distances checked separately, with final aggregate.'),indent=2)+'\n')
print('PREPARED',len(files),'bounded modules')
