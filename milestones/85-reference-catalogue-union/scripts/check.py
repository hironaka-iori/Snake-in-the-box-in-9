"""Check one reference-union module against the pinned window environment."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=ROOT/'milestones/79-retained-edge-guards';summary=read(old/'data/proof-summary.json')
for row in summary['receipts']:
    receipt=old/row['receipt'];assert sha(receipt)==row['sha256'];r=read(receipt)
    for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(old/folder/(row['module']+ext))==r[key]
name=sys.argv[1];assert re.fullmatch(r'[A-Za-z0-9_/]+',name)
source=HERE/'lean'/(name+'.lean');text=source.read_text()
deps=[]
for line in text.splitlines():
    if line.startswith('import '):deps += [n.replace('.','/') for n in line.split()[1:] if (HERE/'lean'/(n.replace('.','/')+'.lean')).exists()]
for dep in deps:
    r=read(HERE/'data'/f'{dep}-audit.json');assert r['status']=='PASS_LEAN_MODULE'
    for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
        assert sha(HERE/folder/(dep+ext))==r[key]
origin=read(HERE/'data/reference-union.json')
if name in origin['upstream']:assert sha(source)==origin['upstream'][name]['sha256']
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
paths=[str(HERE/'build')]+read(old/'data/IntervalGuards-audit.json')['paths']
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
obj=HERE/'build'/(name+'.olean');log=HERE/'logs'/(name+'.log')
obj.parent.mkdir(parents=True,exist_ok=True);log.parent.mkdir(parents=True,exist_ok=True)
start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
    p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),
      '-o',str(obj.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,
      stdout=out,stderr=subprocess.STDOUT,timeout=240)
r=dict(module=name,exit_code=p.returncode,seconds=time.monotonic()-start,source_sha256=sha(source),
    log_sha256=sha(log),paths=paths,inherited_summary_sha256=sha(old/'data/proof-summary.json'),
    dependencies={n:sha(HERE/'data'/f'{n}-audit.json') for n in deps})
record=HERE/'logs'/(name+'-record.json');record.write_text(json.dumps(r,indent=2)+'\n')
if p.returncode:print(log.read_text()[-10000:]);raise SystemExit(p.returncode)
os.replace(obj.with_suffix('.fresh.olean'),obj);output=log.read_text()
assert 'error:' not in output and 'sorryAx' not in output
assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
audits=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
audits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
assert len(audits)==text.count('#print axioms')
checked=[]
for theorem,axs in audits:
    values=re.findall(r'[A-Za-z][\w.]*',axs);assert set(values)<={'propext','Classical.choice','Quot.sound'}
    checked.append(dict(theorem=theorem,axioms=values))
r.update(status='PASS_LEAN_MODULE',olean_sha256=sha(obj),theorem_audits=checked,
    scope='Concrete reference-union data and conditional retention bridge. Closed catalogue refutation imports remain separate.')
(HERE/'data'/(name+'-audit.json')).write_text(json.dumps(r,indent=2)+'\n')
print(name,'PASS',round(r['seconds'],3),'seconds;',len(checked),'audits',flush=True)
