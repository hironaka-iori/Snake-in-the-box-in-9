"""Check concrete pilot data and kernel decision certificates sequentially."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
module=sys.argv[1]
dependencies={'GraphData':['CoverTree'],'Case000Data':['GraphData','BoxWitness'],
    'Case000Checks':['Case000Data','CoverageAssembly']}[module]
pins={}
for dep in dependencies:
    rp=HERE/'data'/(dep+'-audit.json');r=read(rp);assert r['exit_code']==0 and r['status'].startswith('PASS_')
    for sub,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:assert sha(HERE/sub/(dep+ext))==r[key]
    pins[dep]=sha(rp)
paths=read(HERE/'data/BoxWitness-audit.json')['paths']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
src=HERE/'lean'/(module+'.lean');obj=HERE/'build'/(module+'.olean');log=HERE/'logs'/(module+'.log')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
if log.exists():
    saved=HERE/'logs'/(module+'-previous-'+sha(log)[:12]+'.log');saved.write_bytes(log.read_bytes())
start=time.monotonic();timed_out=False
with log.open('w',encoding='utf-8') as out:
    try:
        p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],
            cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=900)
        exit_code=p.returncode
    except subprocess.TimeoutExpired:
        timed_out=True;exit_code=124
r=dict(module=module,exit_code=exit_code,timed_out=timed_out,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),paths=paths,dependencies=pins)
(HERE/'logs'/(module+'-record.json')).write_text(json.dumps(r,indent=2)+'\n')
if exit_code:print(log.read_text()[-16000:]);raise SystemExit(exit_code)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==src.read_text().count('#print axioms')
rows=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    rows.append(dict(theorem=name,axioms=values))
r.update(status='PASS_PILOT_DATA' if module.endswith('Data') else 'PASS_PILOT_KERNEL_CERTIFICATE',olean_sha256=sha(obj),theorem_audits=rows,
    scope='Pilot direction0/history0 only. Data compilation is separate from Boolean validation; complete791-block coverage and recorded-array identification remain open.')
(HERE/'data'/(module+'-audit.json')).write_text(json.dumps(r,indent=2)+'\n')
print(module,r['status'],len(rows),'audits',round(r['seconds'],3),'seconds',flush=True)
