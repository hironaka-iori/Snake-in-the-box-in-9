"""Keep accepted prefix modules and split remaining calculations further."""
from pathlib import Path
import re
H=Path(__file__).resolve().parents[1]
assert not (H/'data/ConcreteGeometry213-audit.json').exists(), 'Preserve the accepted proof assembly.'
assembly=H/'lean/ConcreteGeometry213.lean';source=assembly.read_text(encoding='utf-8')
names=[]
for batch in [6,7,8]:
    old=f'ConcreteChunk213_{batch:02d}';p=H/'lean'/(old+'.lean')
    assert not (H/'data'/(old+'-audit.json')).exists()
    s=p.read_text(encoding='utf-8');header=s[:s.index('theorem valid_')]
    blocks=re.findall(r'theorem (valid_(?:chunk_\d\d|tail)) :([\s\S]*?  decide \+kernel\n)',s)
    assert len(blocks)==(5 if batch<8 else 2)
    replacements=[]
    for name,body in blocks:
        module='ConcretePart213_'+name.removeprefix('valid_');names.append(module);replacements.append(module)
        (H/'lean'/(module+'.lean')).write_text(header+'theorem '+name+' :'+body+'\n#print axioms '+name+'\nend ConcreteGeometry213\n',encoding='utf-8')
    source=source.replace('import '+old+'\n',''.join('import '+n+'\n' for n in replacements))
assembly.write_text(source,encoding='utf-8')
(H/'data/late-module-order.txt').write_text('\n'.join(names+['ConcreteGeometry213','ConcreteSupport213'])+'\n')
print('SPLIT_LATE',len(names),'modules')
