"""Derive a 190-edge seed with endpoints 41 and 67 from the checked core witness."""
import ast
import json
from pathlib import Path
import re
import sys
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/19-coordinate-face-repair/scripts'))
from search_faces import sha

core=ROOT/'work/final_lean/Snake9.lean'
values=ast.literal_eval('['+re.search(r'def witnessValues : Array Nat := #\[(.*?)\]',core.read_text()).group(1)+']')
order=[0,1,3,2,6,4,5,7,8];shift=41
path=[sum(((v>>k)&1)<<j for j,k in enumerate(order))^shift for v in values[:191]]
assert path[0]==41 and path[-1]==67 and len(path)==len(set(path))==191
for j,v in enumerate(path):
    for i,w in enumerate(path[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
data={'edges':190,'path_vertices':path,'seed_vertices':path,'source_core_sha256_lf':sha(core),
      'output_bit_sources':order,'translation':shift,'scope':'Relabeled 190-edge prefix of the existing Lean-checked 191-edge witness; no record improvement.'}
(HERE/'data/paired-seed190.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
template=ROOT/'milestones/18-expanded-cells/lean/Alignment.lean'
s=template.read_text(encoding='utf-8').replace('namespace Snake9.ExpandedCells','namespace Snake9.PairedSeed').replace('end Snake9.ExpandedCells','end Snake9.PairedSeed')
forward=' + '.join(f'(if n.testBit {k} then {1<<j} else 0)' for j,k in enumerate(order))
backward=' + '.join(f'(if n.testBit {j} then {1<<k} else 0)' for j,k in enumerate(order))
s=re.sub(r'def permute .*',lambda _: 'def permute (n : Nat) : Nat := '+forward,s)
s=re.sub(r'def inversePermute .*',lambda _: 'def inversePermute (n : Nat) : Nat := '+backward,s)
s=s.replace('^^^ 7','^^^ 41')
s=re.sub(r'def bitPerm .*',lambda _: 'def bitPerm (a : Coord) : Coord := ⟨(#[ '+','.join(str(order.index(k)) for k in range(9))+'])[a.val]! % 9, Nat.mod_lt _ (by decide)⟩',s)
s=s.replace('end Snake9.PairedSeed','''def pairedWitness : Snake 190 := alignSnake (takePrefix witness (by decide))
theorem paired_start : pairedWitness.vertex 0 = 41 := by decide
theorem paired_end : pairedWitness.vertex (Fin.last 190) = 67 := by decide
theorem paired_exists : ∃ p : Snake 190, p.vertex 0 = 41 ∧ p.vertex (Fin.last 190) = 67 :=
  ⟨pairedWitness,paired_start,paired_end⟩
#print axioms paired_start
#print axioms paired_end
#print axioms paired_exists
end Snake9.PairedSeed''')
(HERE/'lean').mkdir(exist_ok=True);(HERE/'logs').mkdir(exist_ok=True);(HERE/'build').mkdir(exist_ok=True)
(HERE/'lean/PairedSeed.lean').write_text(s,encoding='utf-8',newline='\n')
print('Generated 190-edge witness with endpoints',path[0],path[-1])
