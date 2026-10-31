from pathlib import Path
import json,re,hashlib
H=Path(__file__).resolve().parent;ROOT=H/'lrat_replay';P=H/'generate_full_replay.py';s=P.read_text(encoding='utf-8')
# Reproducibly emit a final module whose log must audit the exact final theorem.
needle="files={str(p.relative_to(OUT))"
addition="(OUT/'PeerLratFinalAudit.lean').write_text('import LocalWindowUnsat.PointwiseScore22\\n#print axioms Snake9.LocalWindow.PointwiseScore22.unsat\\n',encoding='utf-8')\n"
if addition not in s:
 assert needle in s;s=s.replace(needle,addition+needle)
 P.write_text(s,encoding='utf-8')
(ROOT/'PeerLratFinalAudit.lean').write_text('import LocalWindowUnsat.PointwiseScore22\n#print axioms Snake9.LocalWindow.PointwiseScore22.unsat\n',encoding='utf-8')
files={str(p.relative_to(ROOT)).replace('\\','/')[:-5].replace('/','.'):p for p in ROOT.rglob('*.lean')};pending=set(files);order=[]
while pending:
 ready=sorted(x for x in pending if all(im not in pending for im in re.findall(r'^import (\S+)',files[x].read_text(encoding='utf-8'),re.M)))
 assert ready;order+=ready;pending.difference_update(ready)
p=H/'full_replay_manifest.json';m=json.loads(p.read_text(encoding='utf-8'));m.update(build_order=order,generated_modules=len(files),generated_source_bytes=sum(p.stat().st_size for p in files.values()),module_source_sha256={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in files.items()});p.write_text(json.dumps(m,indent=2),encoding='utf-8')
print({'modules':len(files),'source_bytes':m['generated_source_bytes'],'last_module':order[-1]})
