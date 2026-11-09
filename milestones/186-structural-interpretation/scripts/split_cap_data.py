from pathlib import Path
import sys,re,json
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation')
sys.path.insert(0,str(H/'scripts'));from replan import replan,read
p=H/'lean/Share186/CapData.lean';s=p.read_text();lines=s.splitlines()
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
end='end Snake9.LocalWindow.ShareWindow185\n'
data=[l for l in lines if re.match(r'def (base|extra)(Lits|Pairs)\d+ ',l)]
names=[]
for i in range(0,len(data),16):
 n=f'Share186.CapConstants{i//16:02d}';names.append(n)
 (H/'lean'/(n.replace('.','/')+'.lean')).write_text('import Share185.DirectData\n'+head+'\n'.join(data[i:i+16])+'\n'+end,encoding='utf-8',newline='\n')
aggregate=[l for l in lines if l.startswith('def cap')]
p.write_text(''.join('import '+n+'\n' for n in names)+head+'\n'.join(aggregate)+'\n'+end,encoding='utf-8',newline='\n')
joins=[]
for i in [70,71]:
 n=f'Share186.CapJoin{i}';joins.append(n)
 decl=next(l for l in lines if l.startswith(f'theorem cap{i}_data'))
 (H/'lean'/(n.replace('.','/')+'.lean')).write_text('import Share186.CapData\n'+head+decl+f'\n#print axioms cap{i}_data\n'+end,encoding='utf-8',newline='\n')
p=H/'lean/Share186/CapTotals.lean';s=p.read_text();p.write_text(''.join('import '+n+'\n' for n in joins)+s,encoding='utf-8',newline='\n')
order=read(H/'data/current-order.json');ix=order.index('Share186.CapData');order[ix:ix]=names
ix=order.index('Share186.CapTotals');order[ix:ix]=joins
replan(order)
(H/'scripts/split_cap_data.py').write_bytes(Path(__file__).read_bytes())
print('cap data split; planned',len(order))
