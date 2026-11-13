from pathlib import Path
import shutil
H=Path(__file__).resolve().parents[1]
for folder in (H/'logs').glob('EndpointData198-*'):
 if folder.is_dir() and not (folder/'execution.json').exists():shutil.copyfile(H/'data/EndpointData198-execution.json',folder/'execution.json')
p=H/'lean/EndpointData198.lean';s=p.read_text()
for start,finish,replacement in [
 ('theorem neighbourClosed','def Adj','def neighbour (v : Fin 128) (k : Fin 8) : Fin 128 :=\n ⟨rawNeighbour v.val k.val % 128, Nat.mod_lt _ (by decide)⟩\n'),
 ('theorem generatorClosed','def directionTable','def generator (k : Fin 6) (v : Fin 128) : Fin 128 :=\n ⟨rawGenerator k.val v.val % 128, Nat.mod_lt _ (by decide)⟩\n'),
 ('theorem directionClosed','def words','def direction (k : Fin 6) (d : Fin 8) : Fin 8 :=\n ⟨rawDirection k.val d.val % 8, Nat.mod_lt _ (by decide)⟩\n\n')]:
 a=s.index(start);b=s.index(finish,a);s=s[:a]+replacement+s[b:]
s=s[:s.index('theorem normalized')]+'''theorem cover {P : Fin 128 → Prop}
 (h : ∀ b : Fin 8, ∀ i : Fin 16, P ⟨16*b.val+i.val,by omega⟩)
 (v : Fin 128) : P v := by
 have he : 16*(v.val/16)+v.val%16=v.val := by omega
 have hv := h ⟨v.val/16,by omega⟩ ⟨v.val%16,by omega⟩
 simpa only [Fin.val_mk,he] using hv

#print axioms cover
end EndpointData198
'''
p.write_text(s,encoding='utf-8',newline='\n')
cases=''' intro b i
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
'''
options='set_option maxRecDepth 10000\nset_option maxHeartbeats 0\n'
for k in range(6):
 prop=f'generator ⟨{k},by decide⟩ (neighbour v d) = neighbour (generator ⟨{k},by decide⟩ v) (direction ⟨{k},by decide⟩ d)'
 for b in range(8):
  name=f'EndpointChunk198_{k}_{b}'
  s=f'import EndpointData198\nnamespace {name}\nopen EndpointData198\n'+options+f'\ntheorem step : ∀ i : Fin 16, ∀ d : Fin 8,\n let v : Fin 128 := ⟨{16*b}+i.val,by omega⟩\n {prop} := by decide +kernel\n\n#print axioms step\nend {name}\n'
  (H/f'lean/{name}.lean').write_text(s,encoding='utf-8',newline='\n')
 name=f'EndpointStep198_{k}'
 s=''.join(f'import EndpointChunk198_{k}_{b}\n' for b in range(8))+f'namespace {name}\nopen EndpointData198\n\ntheorem step (v : Fin 128) (d : Fin 8) :\n {prop} := by\n refine cover (P:=fun v => {prop}) ?_ v\n'+cases
 s+=''.join(f' · exact EndpointChunk198_{k}_{b}.step i d\n' for b in range(8))+f'\n#print axioms step\nend {name}\n'
 (H/f'lean/{name}.lean').write_text(s,encoding='utf-8',newline='\n')
props=[('involution','∀ k : Fin 6, ∀ i : Fin 16,','(k : Fin 6) (v : Fin 128)','generator k (generator k v)=v','k i'),('normalized','∀ i : Fin 16,','(v : Fin 128)','(evaluate (word v) v).val=10 ∨ (evaluate (word v) v).val=2 ∨ (evaluate (word v) v).val=0','i')]
for b in range(8):
 name=f'EndpointVertex198_{b}';s=f'import EndpointData198\nnamespace {name}\nopen EndpointData198\n'+options+'\n'
 for theorem,params,_,prop,_ in props:s+=f'theorem {theorem} : {params}\n let v : Fin 128 := ⟨{16*b}+i.val,by omega⟩\n {prop} := by decide +kernel\n\n'
 s+=f'#print axioms involution\n#print axioms normalized\nend {name}\n'
 (H/f'lean/{name}.lean').write_text(s,encoding='utf-8',newline='\n')
s=''.join(f'import EndpointVertex198_{b}\n' for b in range(8))+'namespace EndpointData198\n\n'
for name,_,params,prop,args in props:
 s+=f'theorem {name} {params} :\n {prop} := by\n refine cover (P:=fun v => {prop}) ?_ v\n'+cases
 s+=''.join(f' · exact EndpointVertex198_{b}.{name} {args}\n' for b in range(8))+'\n'
s+='#print axioms involution\n#print axioms normalized\nend EndpointData198\n'
(H/'lean/EndpointFacts198.lean').write_text(s,encoding='utf-8',newline='\n')
p=H/'lean/EndpointTransport198.lean';p.write_text('import EndpointFacts198\n'+p.read_text(),encoding='utf-8',newline='\n')
p=H/'scripts/prepare_proof.py';s=p.read_text();a=s.index('dependencies=[]');b=s.index('for dep in dependencies:',a)
s=s[:a]+'''dependencies=[]
if module.startswith('PairRows198_'): dependencies=['PairData198']
if module=='EndpointData198': dependencies=['CliqueFacts198']
if module.startswith(('EndpointChunk198_','EndpointVertex198_')): dependencies=['CliqueFacts198','EndpointData198']
if module.startswith('EndpointStep198_'):
    k=int(module.rsplit('_',1)[1]);dependencies=['CliqueFacts198','EndpointData198']+[f'EndpointChunk198_{k}_{b}' for b in range(8)]
if module=='EndpointFacts198':dependencies=['CliqueFacts198','EndpointData198']+[f'EndpointVertex198_{b}' for b in range(8)]
if module=='EndpointTransport198': dependencies=['CliqueFacts198','EndpointData198','EndpointFacts198']+[f'EndpointStep198_{i}' for i in range(6)]
'''+s[b:]
p.write_text(s,encoding='utf-8',newline='\n')
print('Split endpoint identities into128-edge blocks.')
