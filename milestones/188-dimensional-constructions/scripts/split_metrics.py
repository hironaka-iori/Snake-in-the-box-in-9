from pathlib import Path
import re,json,hashlib
H=Path('E:/Snake-in-a-box/milestones/188-dimensional-constructions')
p=H/'lean/CubeData8188.lean';s=p.read_text();start=s.index('theorem transitions_agree')
defs=s[:start]+'end Dimensional188.Witness8\n';p.write_text(defs,encoding='utf-8',newline='\n')
names=[]
for theorem in ['transitions_agree','minimum_crossings','displayed_cut_indices']:
    match=re.search(r'theorem '+theorem+r'\b.*?(?=\ntheorem |\n#print)',s,re.S);assert match
    module={'transitions_agree':'CubeTransitions8188','minimum_crossings':'CubeMinimum8188','displayed_cut_indices':'CubeCuts8188'}[theorem];names.append(module)
    text='import CubeData8188\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace Dimensional188.Witness8\n'+match[0]+'\n#print axioms '+theorem+'\nend Dimensional188.Witness8\n'
    (H/'lean'/(module+'.lean')).write_text(text,encoding='utf-8',newline='\n')
order=json.loads((H/'data/current-order.json').read_text());i=order.index('CubeData8188');order[i+1:i+1]=names
base=json.loads((H/'data/CubeData8188-execution.json').read_text());base['new_module_order']=order;base['source_sha256']={n:hashlib.sha256((H/'lean'/(n+'.lean')).read_bytes()).hexdigest() for n in order}
for n in order:
    if (H/'data'/(n+'-audit.json')).exists():continue
    (H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n');(H/'scripts/split_metrics.py').write_bytes(Path(__file__).read_bytes())
