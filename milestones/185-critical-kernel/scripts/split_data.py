from pathlib import Path
import re,json,hashlib
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns='Snake9.LocalWindow.ShareWindow185';end='\nend '+ns+'\n'
(H/'scripts/split_data.py').write_bytes(Path(__file__).read_bytes())
p=H/'lean/LocalWindowCnf/ShareWindow185.lean';raw=p.read_text()
(H/'data/unsplit-cnf.lean.txt').write_bytes(p.read_bytes())
chunks=re.findall(r'^def raw\d+ :.*$',raw,re.M);assert len(chunks)==98
prefix=raw[:raw.index(chunks[0])]
(H/'lean/Share185/Window.lean').write_text(prefix+end,newline='\n')
rawmods=[]
for i in range(0,98,8):
 name=f'Share185.RawGroup{i//8:02d}';rawmods.append(name)
 text='import Share185.Window\nset_option maxRecDepth 100000\nnamespace '+ns+'\n'+'\n'.join(chunks[i:i+8])+end
 (H/'lean'/(name.replace('.','/')+'.lean')).write_text(text,newline='\n')
tail=raw[raw.index('def raw :'):]
p.write_text(''.join('import '+n+'\n' for n in rawmods)+'set_option maxRecDepth 100000\nnamespace '+ns+'\n'+tail,newline='\n')
p=H/'lean/Share185/Data.lean';data=p.read_text();(H/'data/unsplit-data.lean.txt').write_bytes(p.read_bytes())
tags=re.findall(r'^def tags\d+ :.*$',data,re.M);assert len(tags)==98
prefix=data[:data.index(tags[0])]
(H/'lean/Share185/CoreData.lean').write_text(prefix+end,newline='\n')
tagmods=[]
for i in range(0,98,8):
 name=f'Share185.TagGroup{i//8:02d}';tagmods.append(name)
 text='import Share185.CoreData\nset_option maxRecDepth 100000\nnamespace '+ns+'\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'+'\n'.join(tags[i:i+8])+end
 (H/'lean'/(name.replace('.','/')+'.lean')).write_text(text,newline='\n')
tail=data[data.index('def tags :'):]
p.write_text(''.join('import '+n+'\n' for n in tagmods)+'set_option maxRecDepth 100000\nnamespace '+ns+'\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'+tail,newline='\n')
order=json.loads((H/'data/current-order.json').read_text())
i=order.index('LocalWindowCnf.ShareWindow185')
order=order[:i]+['Share185.Window']+rawmods+['LocalWindowCnf.ShareWindow185','Share185.CoreData']+tagmods+order[i+1:]
sources={n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order}
base=json.loads((H/'data/LocalWindowCnf.ShareWindow185-execution.json').read_text(encoding='utf-8-sig'))
base['new_module_order']=order;base['source_sha256']=sources
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 (H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
print('SPLIT_DATA',len(order),'current modules; raw clauses and tags unchanged.')

