from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
end='end Snake9.LocalWindow.ShareWindow185\n'
def put(n,s):
 p=H/'lean'/(n.replace('.','/')+'.lean');p.write_text(s,encoding='utf-8',newline='\n')
put('Share186.SortLemma','import Share186.EndpointData\n'+head+'''theorem pw_append (a b : List Nat) :
 pw (a ++ b) = (a.all (fun x => b.all (fun y => decide (x < y))) && pw a && pw b) := by
 induction a with
 | nil => simp [pw]
 | cons x xs ih =>
   simp only [List.cons_append,pw,List.all_append,ih,List.all_cons,
     Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
#print axioms pw_append
'''+end)
sorts=['Share186.SortLemma']
for i in range(18):
 n=f'Share186.Sort{i:02d}';sorts.append(n)
 s='import Share186.EndpointData\n'+head
 s+=f'theorem ep_sort{i} : pw epVerts{i} = true := by decide +kernel\n#print axioms ep_sort{i}\n'
 if i<17:
  tail=' ++ '.join('epVerts'+str(j) for j in range(i+1,18))
  s+=f'theorem ep_cross{i} : epVerts{i}.all (fun x => ({tail}).all (fun y => decide (x < y))) = true := by decide +kernel\n#print axioms ep_cross{i}\n'
 put(n,s+end)
s=''.join('import '+n+'\n' for n in sorts)+head
s+='theorem ep_sorted : pw epVerts = true := by\n  simp only [epVerts,List.append_assoc,pw_append,'+','.join('ep_sort'+str(i) for i in range(18))+','+','.join('ep_cross'+str(i) for i in range(17))+',Bool.and_self]\n#print axioms ep_sorted\n'+end
put('Share186.EndpointSorted',s)
old=read(H/'data/current-order.json');caps=read(H/'data/cap-order.json')
ix=old.index('Share186.EndpointSorted');order=old[:ix]+sorts+old[ix:]+caps
base=read(H/'data/Share186.CapTotals-execution.json')
base['new_module_order']=order
base['source_sha256']={n:hashlib.sha256((H/'lean'/(n.replace('.','/')+'.lean')).read_bytes()).hexdigest() for n in order}
for n in order:
 if not (H/'data'/(n+'-audit.json')).exists():
  (H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/prepare_sort.py').write_bytes(Path(__file__).read_bytes())
print('prepared',len(order),'modules')
