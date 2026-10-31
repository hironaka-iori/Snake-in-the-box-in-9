"""Independent check of the generated Lean raw CNF against original certificate.
This is a format/provenance check, NOT a kernel proof of the large replay.
"""
from pathlib import Path
import json,gzip,re,hashlib
H=Path(__file__).resolve().parent
with gzip.open(H.parent/'branch241-review/loop_k1_cap21_r4_all8/checked_unsat.json.gz','rt') as f:d=json.load(f)
p=H/'lrat_replay/LocalWindowCnf/PointwiseScore22.lean';text=p.read_text(encoding='utf-8')
raw=[]
for body in re.findall(r'\[([^\[\]]*)\]',text):
 if 'nat_lit' not in body:continue
 ns=list(map(int,re.findall(r'nat_lit\s+(\d+)',body)))
 assert not re.sub(r'nat_lit\s+\d+|[\s,]','',body)
 raw.append([-(n//2) if n%2 else n//2 for n in ns])
assert raw==d['clauses']
manifest=json.loads((H/'full_replay_manifest.json').read_text(encoding='utf-8'));assert len(raw)==manifest['original_clause_count']
files=list((H/'lrat_replay').rglob('*.lean'))
for p in files:
 t=p.read_text(encoding='utf-8');assert not re.search(r'^\s*(axiom\s|.*:=\s*(?:by\s+)?sorry\b)',t,re.M),p
 assert not re.search(r'\b(?:native_decide|ofReduceBool)\b',re.sub(r'/\-.*?\-/','',t,flags=re.S)),p
result={'status':'PASS, Python source-format/provenance only; full Lean replay still UNREPLAYED','exact_original_CNF_clause_order_and_literals':len(raw),'original_proof_steps':len(d['proof']),'original_hints':sum(len(x['hints']) for x in d['proof']),'raw_source_sha256':hashlib.sha256(text.encode()).hexdigest(),'generated_Lean_files_scanned_no_new_axiom_placeholder_or_native_oracle':len(files)}
(H/'prepared_source_independent_check.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
