"""Compute two unsaturated families directly from the literal saved source."""
from pathlib import Path
H=Path(__file__).resolve().parents[1]
template=(H.parent/'209-slice-capacity/lean/ConcreteCapacity209.lean').read_text(encoding='utf-8')
prefix=template.split('/-- This order agrees',1)[0]
for module,a,b,counts,chosen,outside,k,q in [
 ('ConcreteSpare47',4,7,[19,7,1,5,1],[0,2],[1,3],31,2),
 ('ConcreteSpare06',0,6,[12,5,4,9,9],[3,2],[0,1],30,9)]:
 s=prefix.replace('namespace ConcreteCapacity209',f'namespace {module}')
 s=s.replace('Uncompiled source draft.','Literal finite-count source prepared for kernel checking.')
 s=s.replace('The fixed coordinates are 0 and 5',f'The fixed coordinates are {a} and {b}')
 s=s.replace('(if v.testBit 0 then 1 else 0) + (if v.testBit 5 then 2 else 0)',
             f'(if v.testBit {a} then 1 else 0) + (if v.testBit {b} then 2 else 0)')
 s+=f'''
def clique : List Nat := multi 0 ++ single 0 {chosen[0]} ++ single 0 {chosen[1]}
def outside : List Nat := single 0 {outside[0]} ++ single 0 {outside[1]}

theorem source_intervals :
    source.length = 99 ∧
    rawVisits.all (fun xs => decide (xs ≠ [] ∧ xs.Nodup)) = true := by
  decide +kernel

theorem even_counts : counts 0 = {str(counts).replace(' ', '')} := by
  decide +kernel

theorem even_partition :
    clique.length = {k} ∧ outside.length = {q} ∧
    (clique ++ outside).Nodup ∧
    (clique ++ outside).all (fun g => decide (g < rawVisits.length ∧ g % 2 = 0)) = true ∧
    (List.range rawVisits.length).all (fun g => decide (g % 2 = 0 → g ∈ clique ++ outside)) = true := by
  decide +kernel

#print axioms source_intervals
#print axioms even_counts
#print axioms even_partition
end {module}
'''
 (H/'lean'/f'{module}.lean').write_text(s,encoding='utf-8',newline='\n')
 print('PREPARED_SOURCE',module)
