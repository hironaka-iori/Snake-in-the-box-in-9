"""Check the generic box and six-way coverage checker against Lean4.19."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
name=sys.argv[1];assert name in ['Boxes','CoverTree']
for sub in ['build','data','logs']:(HERE/sub).mkdir(exist_ok=True)
deps={}
if name=='CoverTree':
    path=HERE/'data/Boxes-audit.json';r=json.loads(path.read_text());assert r['status'] in ['PASS_GENERIC_COVER_MODULE','PASS_LEAN_MODULE']
    for sub,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:assert sha(HERE/sub/('Boxes'+ext))==r[key]
    deps['Boxes']=sha(path)
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
src=HERE/'lean'/(name+'.lean');obj=HERE/'build'/(name+'.olean');log=HERE/'logs'/(name+'.log')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=str(HERE/'build')
if log.exists() and 'error:' in log.read_text():
    saved=HERE/'logs'/(name+'-failure-'+sha(log)[:12]+'.log');saved.write_bytes(log.read_bytes())
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=240)
r=dict(module=name,exit_code=result.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),dependencies=deps)
(HERE/'logs'/(name+'-record.json')).write_text(json.dumps(r,indent=2)+'\n')
if result.returncode:print(log.read_text());raise SystemExit(result.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==src.read_text().count('#print axioms')
rows=[]
for theorem,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    rows.append(dict(theorem=theorem,axioms=values))
r.update(status='PASS_GENERIC_COVER_MODULE',olean_sha256=sha(obj),theorem_audits=rows,
    scope='Generic box-prefix and diagram-cover checker correctness only; concrete diagram data and rejection witnesses need separate checked certificates.')
(HERE/'data'/(name+'-audit.json')).write_text(json.dumps(r,indent=2)+'\n')
print(name,'PASS',len(rows),'audits',round(r['seconds'],3),'seconds')
