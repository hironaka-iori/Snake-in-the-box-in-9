"""Check the conditional actual-snake-to-saved-row assembly."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
numeric=read(HERE/'data/NumericRetention-audit.json')
enum=read(HERE/'data/enumeration-audit.json')
assert numeric['exit_code']==enum['exit_code']==0
for name,r in [('NumericRetention',numeric),('RetainedEnumeration',enum)]:
    assert sha(HERE/'lean'/(name+'.lean'))==r['source_sha256']
    assert sha(HERE/'logs'/(name+'.log'))==r['log_sha256']
    assert sha(HERE/'build'/(name+'.olean'))==r.get('olean_sha256',r.get('object_sha256'))
module='ArrayAssembly';src=HERE/'lean'/(module+'.lean');obj=HERE/'build'/(module+'.olean')
log=HERE/'logs'/(module+'.log')
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(numeric['paths'])
if log.exists() and 'error:' in log.read_text():
    old=HERE/'logs'/(module+'-failure-'+sha(log)[:12]+'.log')
    old.write_bytes(log.read_bytes())
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    run=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(obj.with_suffix('.fresh.olean')),str(src)],
        cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=240)
record=dict(module=module,exit_code=run.returncode,seconds=time.monotonic()-start,source_sha256=sha(src),log_sha256=sha(log),
    paths=numeric['paths'],dependencies={name:sha(HERE/'data'/name) for name in ['NumericRetention-audit.json','enumeration-audit.json']})
(HERE/'logs/ArrayAssembly-record.json').write_text(json.dumps(record,indent=2)+'\n')
if run.returncode:print(log.read_text());raise SystemExit(run.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj)
text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
audits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
assert len(audits)==src.read_text().count('#print axioms')==2
rows=[]
for name,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    rows.append(dict(theorem=name,axioms=values))
record.update(status='PASS_CONDITIONAL_SAVED_WALK',olean_sha256=sha(obj),theorem_audits=rows,
    scope='Actual edge and entire state-walk indexing under two reference-catalogue premises, finite retention coverage, and endpoint-column equalities. Concrete finite-data premises and all edge-weight/potential obligations remain separate.')
(HERE/'data/ArrayAssembly-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],len(rows),'audits',round(record['seconds'],3),'seconds')
