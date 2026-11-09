from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n';end='end Snake9.LocalWindow.ShareWindow185\n'
params='meaningDirect smeaningDirect resolution ctrs tots window cap'
names=['Share186.ClauseAppend','Share186.Clause37Left','Share186.Clause37Right']
s='import Share185.DirectData\n'+head+'''theorem ckAllS_append_true (M : MT) (X : MS) (r : Nat) (cs : List Ctr)
    (ts : List Tot) (w : List Nat) (k : Nat)
    (a b : List TagS) (c d : List (List Nat)) (hlen : a.length = c.length)
    (ha : ckAllS M X r cs ts w k a c = true)
    (hb : ckAllS M X r cs ts w k b d = true) :
    ckAllS M X r cs ts w k (a ++ b) (c ++ d) = true := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => exact hb
    | cons x xs => simp at hlen
  | cons x xs ih =>
    cases c with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons,Nat.succ.injEq] at hlen
      simp only [ckAllS,Bool.and_eq_true] at ha
      simp only [List.cons_append,ckAllS,ha.1,ih ys hlen ha.2,Bool.and_self]
#print axioms ckAllS_append_true
'''+end
(H/'lean/Share186/ClauseAppend.lean').write_text(s,encoding='utf-8',newline='\n')
for part,op in [('Left','take'),('Right','drop')]:
 s='import Share185.DirectData\n'+head+f'theorem clause37{part} : ckAllS {params} (tags37.{op} 64) (raw37.{op} 64) = true := by decide +kernel\n#print axioms clause37{part}\n'+end
 (H/f'lean/Share186/Clause37{part}.lean').write_text(s,encoding='utf-8',newline='\n')
s=''.join('import '+n+'\n' for n in names)+head+f'''theorem shard37 : ckAllS {params} tags37 raw37 = true := by
  have hlen : (tags37.take 64).length = (raw37.take 64).length := by decide +kernel
  have h := ckAllS_append_true {params} (tags37.take 64) (tags37.drop 64)
    (raw37.take 64) (raw37.drop 64) hlen clause37Left clause37Right
  simpa only [List.take_append_drop] using h
#print axioms shard37
'''+end
(H/'lean/Share185/Shard37.lean').write_text(s,encoding='utf-8',newline='\n')
order=read(H/'data/current-order.json');ix=order.index('Share185.Shard37');order[ix:ix]=names
base=read(H/'data/Share185.Shard37-execution.json');base['new_module_order']=order
base['source_sha256']={n:hashlib.sha256((H/'lean'/(n.replace('.','/')+'.lean')).read_bytes()).hexdigest() for n in order}
for n in order:
 if not (H/'data'/(n+'-audit.json')).exists():(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/split_shard37.py').write_bytes(Path(__file__).read_bytes())
print('prepared two halves and append proof')
