"""Split pending finite active-graph assertions into eight-position lemmas."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1]
records=json.loads((H/'data/active-trees.json').read_bytes())['records']
def finite(name,bound,expr):
 code=''
 for start in range(0,bound,8):
  width=min(8,bound-start)
  code+=f'theorem {name}Chunk{start} : ∀ i : Fin {width}, '+expr(f'({start}+i.val)')+' := by decide +kernel\n'
 code+=f'theorem {name} : ∀ i : Fin {bound}, '+expr('i.val')+' := by\n  intro i\n  have hi := i.isLt\n'
 for start in range(0,bound,8):
  width=min(8,bound-start);last=start+width==bound
  if not last:code+=f'  by_cases h{start} : i.val < {start+width}\n'
  indent='  ' if last else '  · '
  code+=indent+f'have hj : i.val-{start} < {width} := by omega\n'
  indent='  ' if last else '    '
  code+=indent+f'have he : {start}+(i.val-{start})=i.val := by omega\n'
  code+=indent+f'have h := {name}Chunk{start} ⟨i.val-{start},hj⟩\n'
  code+=indent+'simpa only [he] using h\n'
 return code
for record in records:
 name=record['module'];p=H/'lean'/(name+'.lean');assert not (H/'data'/(name+'-audit.json')).exists()
 text=p.read_text(encoding='utf-8')
 if 'set_option Elab.async false' not in text:text=text.replace('import HistoryData205\n','import HistoryData205\nset_option Elab.async false\nset_option maxRecDepth 100000\n')
 begin=text.index('theorem coverageCheck',text.index('namespace '+record['namespace']+'\n'));end=text.index('theorem constantOnActive',begin);n=record['vertices']
 coverage=lambda x:f'active seed[{x}]! = true → cover[{x}]! < {n} ∧ words[cover[{x}]!]! = base seed[{x}]!'
 parent=lambda x:f'positions[{x}]! < 99 ∧ active seed[positions[{x}]!]! = true ∧ words[{x}]! = base seed[positions[{x}]!]! ∧ (0<{x} → parents[{x}]! < {x} ∧ adjacent words[parents[{x}]!]! words[{x}]!)'
 text=text[:begin]+finite('coverage',99,coverage)+finite('parentFacts',n,parent)+text[end:]
 p.write_bytes(text.encode('utf-8'))
print('Prepared eight-position assertions for all 56 pending active graphs.')
