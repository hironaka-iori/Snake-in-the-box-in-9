"""Generate the compact refutation with an explicit exit-code and hash record."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];OUT=HERE/'cases'/f'case{int(sys.argv[1])}'
meta=json.loads((OUT/'data/case.json').read_text());slug=meta['slug']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
cnf=OUT/f'certificates/{slug}.cnf';lrat=OUT/f'certificates/{slug}.lrat';log=OUT/'logs/lrat-generate.log'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();start=time.monotonic()
try:
 with log.open('w') as out:r=subprocess.run([str(BIN/'cadical.exe'),'-q','--lrat','--no-binary',str(cnf),str(lrat)],stdout=out,stderr=subprocess.STDOUT,timeout=300)
 code=r.returncode
except subprocess.TimeoutExpired:code='TIMEOUT'
report=dict(status='COMPACT_LRAT_GENERATED' if code==20 else 'INCOMPLETE',exit_code=code,cnf_sha256=sha(cnf),seconds=time.monotonic()-start,scope='Generated proof only; simulation and Lean replay are still required.')
if code==20:
 assert 's UNSATISFIABLE' in log.read_text();report['lrat_sha256']=sha(lrat)
(OUT/'data/lrat-generation.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
if code!=20:sys.exit(1)
