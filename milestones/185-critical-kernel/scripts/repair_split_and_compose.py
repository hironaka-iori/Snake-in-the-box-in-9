from pathlib import Path
import re,json,hashlib
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/'scripts/repair_split_and_compose.py').write_bytes(Path(__file__).read_bytes())
order=json.loads((H/'data/current-order.json').read_text())
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 p=H/'lean'/(name.replace('.','/')+'.lean')
 s=p.read_text()
 if name.startswith('Share185Proof'):
  s=re.sub(r'/--.*?-/', '', s, flags=re.S)
  p.write_text(s,newline='\n')
# Use checked clause consequences directly; no append-checker lemma is assumed.
name='Share185.Compose';p=H/'lean/Share185/Compose.lean'
(H/'data/initial-compose.lean.txt').write_bytes(p.read_bytes())
n=98
s='import Share185.Structure\n'+''.join(f'import Share185.Shard{i:02d}\n' for i in range(n))
s+='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
s+='namespace Snake9.LocalWindow.ShareWindow185\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
s+='theorem input_true (S E : Nat → Bool)\n    (ax : AxiomsS S E window (centresOf window bounds) resolution cap) :\n    cnfTrue (tauS S E meaning smeaning resolution ctrs tots) cnf = true := by\n  rw [centresK_eq] at ax\n'
for i in range(n):
 s+=f'  have h{i} : raw{i}.all (fun cl => clauseTrue\n      (tauS S E meaning smeaning resolution ctrs tots) (cl.map decodeLit)) = true :=\n    List.all_eq_true.mpr (sound_allS shard{i} counts_ok totals_ok ax)\n'
s+='  simp only [cnf, cnfTrue, List.all_map, raw, List.all_append, Bool.and_eq_true,\n    List.all_nil, and_true, and_assoc]\n'
s+='  exact ⟨'+', '.join('h'+str(i) for i in range(n))+'⟩\n'
s+='theorem refuted_of_unsat (h : Unsat cnf) : RefutedShare window bounds resolution cap :=\n  refutedShare_of_sat (fun S E ax => ⟨_, input_true S E ax⟩) h\n'
s+='#print axioms input_true\n#print axioms refuted_of_unsat\nend Snake9.LocalWindow.ShareWindow185\n'
p.write_text(s,newline='\n')
sources={n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order}
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 p=H/'data'/(name+'-execution.json');j=json.loads(p.read_text());j['source_sha256']=sources
 p.write_text(json.dumps(j,indent=2)+'\n')
print('REPAIRED_DOCUMENT_COMMENTS_AND_COMPOSITION')

