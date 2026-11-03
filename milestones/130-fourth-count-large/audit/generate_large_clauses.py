"""Generate a certificate for the 717 added fourth-count counter clauses."""
from pathlib import Path
import ast,hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
datafile=H/'data/large-counter.json';data=json.loads(datafile.read_text())
prepfile=H/'data/preparation.json';prep=json.loads(prepfile.read_text())
assert sha(datafile)==prep['counter_sha256']
assert data['counter_index']==9 and data['selected_upper']==17 and data['absent_lower']==4
assert len(data['literals'])==21 and len(data['clauses'])==len(data['tags'])==717
vertices=data['corner_lists'][3]
assert data['literals']==[v+1 for v in vertices] and len(set(vertices))==21
registers={int(k):v for k,v in data['registers'].items()}
assert set(registers)==set(range(8706,9063))
assert all(v[0]=='r' and v[1]==9 for v in registers.values())
meaning={v+1:['p',v] for v in range(512)}|registers
assert {abs(x) for c in data['clauses'] for x in c}<=set(meaning)
assert all(t[0] in {'first','zero','mono','step','over'} and t[1]==9 for t in data['tags'])
templatefile=R/'milestones/128-coupled-pair/audit/generate_pair_clauses.py'
template=next(ast.literal_eval(n.value) for n in ast.parse(templatefile.read_text()).body
              if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='source' for t in n.targets))
source=template.replace('PairLower128','LargeLower130').replace('PairClauses128','LargeClauses130')
source=source.replace('⟨LITERALS,34,.ends⟩','⟨LITERALS,17,.ends⟩').replace('List.replicate 8','List.replicate 9')
source=source.replace('counter.k = 34','counter.k = 17').replace('actual_pair_clauses','actual_large_clauses')
source=source.replace('    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])\n','')
source=source.replace('([0,1,2,0,3,2,4] : List Nat).getD j 0) :\n    cnfTrue',
                      '([0,1,2,0,3,2,4] : List Nat).getD j 0)\n    (hfourth : 4 ≤ coreAlpha p (r+4)) :\n    cnfTrue')
source=source.replace('actual_counter_good p P r hr hshape hP','actual_counter_good p P r hr hP hfourth')
normalized='''
theorem actual_normalized_clauses {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hfourth : 4 ≤ coreAlpha p (r+4)) :
    ∃ P : CPerm,
      (∀ j, j < 7 → P.fwd (dir p (r+j)) =
        ([0,1,2,0,3,2,4] : List Nat).getD j 0) ∧
      cnfTrue (tau (sel p (amap P (vx p r))) (frameE p P (vx p r))
        meaning counters) (raw.map (·.map decodeLit)) = true := by
  obtain ⟨P,hP,_⟩ := LargeLower130.actual_normalized_bound p r hr hshape hfourth
  exact ⟨P,hP,actual_large_clauses p P r hr hP hfourth⟩

#print axioms actual_normalized_clauses
'''
source=source.replace('end Snake9.LargeClauses130',normalized+'end Snake9.LargeClauses130')
def tree(r,s):
 if r+s>9062:
  m=meaning.get(r)
  return '.z' if m is None else '(.'+' '.join(map(str,m))+')'
 left,right=tree(r,2*s),tree(r+s,2*s)
 return '.z' if left==right=='.z' else f'(.n {left} {right})'
def natlist(xs):return '['+','.join(map(str,xs))+']'
source=source.replace('MEANING',tree(0,1)).replace('LITERALS',natlist([2*x for x in data['literals']]))
source=source.replace('VERTICES',natlist(vertices))
source=source.replace('RAW',',\n'.join('  '+natlist([2*abs(x)+(x<0) for x in c]) for c in data['clauses']))
source=source.replace('TAGS',',\n'.join('  (.'+' '.join(map(str,t))+')' for t in data['tags']))
parts=[];count=(len(data['clauses'])+63)//64
for i in range(count):
 ts='['+','.join('(.'+' '.join(map(str,t))+')' for t in data['tags'][64*i:64*(i+1)])+']'
 rs='['+','.join(natlist([2*abs(x)+(x<0) for x in c]) for c in data['clauses'][64*i:64*(i+1)])+']'
 parts.append(f'private def ts{i} : List Tag := {ts}\nprivate def rs{i} : List (List Nat) := {rs}\nprivate theorem checked{i} : ckAll meaning counters [] ts{i} rs{i} = true := by decide +kernel\n')
source=source.replace('GROUPS','\n'.join(parts)).replace('__T_JOIN__',' ++ '.join('ts'+str(i) for i in range(count)))
source=source.replace('__R_JOIN__',' ++ '.join('rs'+str(i) for i in range(count)))
chain=f'checked{count-1}'
for i in reversed(range(count-1)):chain=f'(checked_append meaning counters [] checked{i} {chain})'
source=source.replace('__PROOF_CHAIN__',chain)
source=re.sub(r'(?m)^(private )?def ',lambda m:(m.group(1) or '')+'noncomputable def ',source)
path=H/'lean/LargeClauses130.lean';assert not path.exists()
path.write_text(source,encoding='utf-8',newline='\n')
record=dict(status='GENERATED_NOT_YET_LEAN_CHECKED',source=path.relative_to(H).as_posix(),source_sha256=sha(path),
 generator_sha256=sha(Path(__file__)),template_sha256=sha(templatefile),counter_data_sha256=sha(datafile),
 preparation_sha256=sha(prepfile),clauses=717,counter_index=9,first_new_variable=8706,last_new_variable=9062,
 checked_groups=count,scope='Only the 717 added clauses. No satisfaction of the preceding 104529 clauses or any refutation is claimed.')
(H/'audit/concrete-large-generation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
