"""Replay the saved 2,329,967-hint proof; no new solver run."""
from pathlib import Path
import hashlib, importlib.util, json, time
H=Path(__file__).resolve().parents[1]
R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=H/'data/replay-short.json'
assert not record.exists()
src=H/'scripts/certify_short.py'
meta=json.loads((H/'data/native-short.json').read_text())
assert meta['status']=='NATIVE_REPLAY_PENDING_HINT_LIMIT'
assert meta['hints']==2329967 and meta['hints']<=3000000
assert sha(src)==meta['script_sha256']
for rel,digest in meta['source_files_sha256'].items():assert sha(R/rel)==digest,rel
w=H/'work/certificate-short'
assert sha(w/'trimmed.lrat')==meta['trim_sha256']
assert sha(w/'input.cnf')==meta['input_sha256']
assert sha(w/'core-ids.json')==meta['core_ids_sha256']
# Preserve the original implementation and alter only its resource guard.
original=src.read_text()
assert original.count("assert hints <= 2000000, 'Hint limit exceeded during replay'")==1
revised=original.replace("assert hints <= 2000000, 'Hint limit exceeded during replay'", "assert hints <= 3000000, 'Hint limit exceeded during replay'")
exact=w/'replay-implementation.exact.py';assert not exact.exists();exact.write_text(revised,encoding='utf-8')
spec=importlib.util.spec_from_file_location('replay138',exact)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
_,clauses=module.formula(w/'input.cnf')
ids=json.loads((w/'core-ids.json').read_text())
out=module.replay(w/'trimmed.lrat',clauses,ids,meta['lemmas'],meta['hints'])
out.update(script_sha256=sha(Path(__file__)),replay_implementation_sha256=sha(exact),native_record_sha256=sha(H/'data/native-short.json'),trim_sha256=sha(w/'trimmed.lrat'),input_sha256=sha(w/'input.cnf'),core_ids_sha256=sha(w/'core-ids.json'),hint_limit=3000000,reason='The complete saved proof is only329967 hints above the initial guard. Replay that same proof under a bounded3million-hint guard; preserve original result and do not repeat SAT search.',scope='Complete independent Python replay of the finite CNF contradiction. Lean replay and actual-snake semantics remain pending.')
record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
