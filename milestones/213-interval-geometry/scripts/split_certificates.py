"""Split the unchanged full geometric certificate into bounded Lean modules."""
from pathlib import Path
import re
H=Path(__file__).resolve().parents[1]
p=H/'lean/ConcreteGeometry213.lean';s=p.read_text(encoding='utf-8')
assert not (H/'data/ConcreteGeometry213-audit.json').exists()
blocks=re.findall(r'private theorem valid_chunk_\d\d :[\s\S]*?  decide \+kernel\n',s)
tail=re.search(r'private theorem valid_tail :[\s\S]*?  decide \+kernel\n',s).group()
assert len(blocks)==41
header='import ConcreteRelations213\n\nset_option Elab.async false\nset_option maxRecDepth 10000\nset_option maxHeartbeats 20000000\n\nnamespace ConcreteGeometry213\nopen IndexedCriterion206 Square209\n\n'
coverage=s[s.index('private theorem map_certificate_pairs'):s.index('/- Slice the pair list')]
coverage=re.sub(r'\s*#eval do[^\n]*\n(?:  [^\n]*\n)*','\n',coverage)
(H/'lean/ConcreteCoverage213.lean').write_text(header+coverage+'\nend ConcreteGeometry213\n',encoding='utf-8')
names=[]
for batch in range(9):
    name=f'ConcreteChunk213_{batch:02d}';names.append(name)
    parts=blocks[batch*5:(batch+1)*5]
    if batch==8:parts.append(tail)
    body='\n'.join(x.replace('private theorem','theorem') for x in parts)
    reports='\n'.join('#print axioms '+re.search(r'theorem (\w+)',x).group(1) for x in parts)
    (H/'lean'/(name+'.lean')).write_text(header+body+'\n'+reports+'\nend ConcreteGeometry213\n',encoding='utf-8')
assembly=s[s.index('private theorem all_from_take_drop'):]
imports='import ConcreteCoverage213\n'+''.join('import '+n+'\n' for n in names)
assembly_header=imports+'\nset_option Elab.async false\nset_option maxRecDepth 10000\nset_option maxHeartbeats 20000000\n\nnamespace ConcreteGeometry213\nopen IndexedCriterion206 Square209\n\n'
p.write_text(assembly_header+assembly,encoding='utf-8')
print('SPLIT_FULL_CERTIFICATE',len(blocks),'chunks in',len(names),'modules')
