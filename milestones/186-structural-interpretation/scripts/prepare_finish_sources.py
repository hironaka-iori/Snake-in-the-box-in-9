from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation');P=H.parent/'185-critical-kernel'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
end='end Snake9.LocalWindow.ShareWindow185\n'
def put(n,s):
 p=H/'lean'/(n.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
s=''.join(f'import Share186.Total{i:02d}\n' for i in range(70))+'import Share186.CapTotals\n'+head
s+='theorem tots_rows : tots = ['+', '.join(f'tots.getD {i} dfltTot' for i in range(72))+'] := by rfl\n'
s+='theorem totals_ok : tots.all (totOK meaningDirect smeaningDirect window (centresK window bounds)) = true := by\n'
s+='  conv_lhs => rw [tots_rows]\n  simp only [List.all_cons,List.all_nil,'+','.join(f'total{i}_ok' for i in range(72))+',Bool.and_self]\n#print axioms totals_ok\n'+end
put('Share186.Totals',s)
put('Share185.Structure','import Share186.Counts\nimport Share186.Totals\n')
order=['Share186.Totals','Share185.Structure']
for i in range(98):
 n=f'Share185.Shard{i:02d}';put(n,(P/'lean'/(n.replace('.','/')+'.lean')).read_text());order.append(n)
put('Share185.Compose',(P/'lean/Share185/Compose.lean').read_text());order.append('Share185.Compose')
base=read(H/'data/Share186.CapTotals-execution.json')
base['new_module_order']+=order
base['source_sha256'].update({n:hashlib.sha256((H/'lean'/(n.replace('.','/')+'.lean')).read_bytes()).hexdigest() for n in order})
for n in order:(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/remaining-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/prepare_finish_sources.py').write_bytes(Path(__file__).read_bytes())
print('prepared',len(order),'additional modules; not yet checked')
