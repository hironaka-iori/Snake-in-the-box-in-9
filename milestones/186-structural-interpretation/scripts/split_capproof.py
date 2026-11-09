from pathlib import Path
import sys,re
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation');sys.path.insert(0,str(H/'scripts'));from replan import replan,read
p=H/'lean/Share186/CapTotals.lean';s=p.read_text();imports='\n'.join(re.findall(r'^import .*$',s,re.M))+'\n'
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n';end='end Snake9.LocalWindow.ShareWindow185\n'
body=s[s.index('theorem capBase_pos'):s.index('#print axioms total70_ok')]
parts=re.split(r'(?=^theorem )',body,flags=re.M);names=[]
for proof in filter(str.strip,parts):
 theorem=re.match(r'theorem (\w+)',proof).group(1);n=f'Share186.CapProof{len(names):02d}'
 src=imports+''.join('import '+x+'\n' for x in names)+head+proof+'\n#print axioms '+theorem+'\n'+end
 q=H/'lean'/(n.replace('.','/')+'.lean');assert not q.exists();q.write_text(src,encoding='utf-8',newline='\n');names.append(n)
p.write_text(''.join('import '+n+'\n' for n in names)+head+'#print axioms total70_ok\n#print axioms total71_ok\n'+end,encoding='utf-8',newline='\n')
order=read(H/'data/current-order.json');ix=order.index('Share186.CapTotals');order[ix:ix]=names;replan(order)
(H/'scripts/split_capproof.py').write_bytes(Path(__file__).read_bytes());print('split',len(names),'cap proofs')
