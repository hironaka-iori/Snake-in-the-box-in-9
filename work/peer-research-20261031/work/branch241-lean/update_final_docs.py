from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent;p=H/'LRAT_INTEGRATION.md';s=p.read_text(encoding='utf-8')
s=s.replace('with per-module logs, source/olean hashes and a resumable progress file.','with per-module logs, source/olean hashes, exact imported-olean hashes, compiler executable hash/version and a resumable progress file. --plan never invokes the compiler and can use a stored toolchain identity.')
s=s.replace('First compile one module and inspect the output:','First inspect the compiler-free plan, then compile one module and inspect its output:\n\n    python build_replay.py --plan --reuse --max-modules 1')
s=s.replace('Full source files include axiom printouts only in the dedicated smoke; add #print axioms for the final theorem after successful full compilation and retain its log.','PeerLratFinalAudit is generated reproducibly at the end of the build order and prints axioms for that exact final theorem. The driver rejects errors, sorry and nonstandard axioms, and only records ALL_COMPILED_AUDIT_PASSED after this final audit succeeds.')
s=s.replace('A single-process host with8GB available memory and2GB free disk is a reasonable first trial budget, not a guaranteed bound or a measured requirement. Exact generated source sizes are provided by the manifest.','No memory, disk or CPU budget is inferred from unmeasured full compilation. Exact generated source sizes are provided by the manifest; the current76-module source tree is54,693,944bytes. Measure the first check group in the actual target environment before scheduling a full replay.')
p.write_text(s,encoding='utf-8')
g=H/'generate_full_replay.py';t=g.read_text(encoding='utf-8');needle="(H/'full_replay_manifest.json').write_text(json.dumps(manifest,indent=2))"
replacement="manifest['module_source_sha256']={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in files.items()}\nmanifest['build_driver_sha256']=hashlib.sha256((H/'build_replay.py').read_bytes()).hexdigest()\n"+needle
assert needle in t;t=t.replace(needle,replacement);g.write_text(t,encoding='utf-8')
p=H/'full_replay_manifest.json';m=json.loads(p.read_text(encoding='utf-8'));m['build_driver_sha256']=hashlib.sha256((H/'build_replay.py').read_bytes()).hexdigest();p.write_text(json.dumps(m,indent=2),encoding='utf-8')
