"""Compile both share theorems together and audit the conditional arithmetic."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OUT=HERE/'share-proof'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
audit=read(OUT/'data/proof-audit.json');assert audit['status']=='PASS_LOCAL_SHARE_THEOREM'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
merged=HERE/'build/combined';merged.mkdir(exist_ok=True)
roots=[OUT,HERE.parent/'critical-charge/share-proof'];origins={}
for root in roots:
 for obj in (root/'build/semantic').rglob('*.olean'):
  if obj.name.endswith('.fresh.olean'):continue
  rel=obj.relative_to(root/'build/semantic');dest=merged/rel
  if str(rel) in origins:
   left=origins[str(rel)]/'lean'/rel.with_suffix('.lean');right=root/'lean'/rel.with_suffix('.lean')
   assert sha(left)==sha(right),f'Conflicting shared module: {rel}'
   continue
  origins[str(rel)]=root;dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():shutil.copyfile(obj,dest)
  elif sha(dest)!=sha(obj):
   tmp=dest.with_suffix('.fresh.olean');shutil.copyfile(obj,tmp);os.replace(tmp,dest)
paths=[merged,HERE/'build',OUT/'build/semantic',HERE.parent/'critical-charge/share-proof/build/semantic']
paths += [Path((ROOT/p).read_text().strip()) for p in ['milestones/32-seven-count-four-screen/build/proofs-latest.txt','milestones/49-six-direction-pair-catalogue/build/latest.txt','milestones/28-direct-share-certificates/build/latest.txt']]
paths += [ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy']]
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
source=HERE/'lean/CombinedShares.lean';dest=HERE/'build/CombinedShares.olean';log=HERE/'logs/CombinedShares.log';start=time.monotonic()
with log.open('w',encoding='utf-8') as out:
 r=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(dest.with_suffix('.fresh.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT,timeout=120)
assert r.returncode==0,log.read_text()
os.replace(dest.with_suffix('.fresh.olean'),dest)
texts=[log.read_text(),(HERE/'logs/CountFreeTarget.log').read_text()]
checks=[]
for txt in texts:
 assert 'error:' not in txt and 'sorryAx' not in txt
 for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",txt,re.S):
  assert set(re.findall(r'[A-Za-z][\w.]*',axs))<={'propext','Classical.choice','Quot.sound'}
  checks.append(dict(theorem=name,axioms=axs))
assert len(checks)==4
out=dict(status='PASS_COMBINED_IMPORTS_AND_ARITHMETIC',seconds=time.monotonic()-start,checks=checks,source_sha256={n:sha(HERE/f'lean/{n}.lean') for n in ['CombinedShares','CountFreeTarget']},share12_audit_sha256=sha(OUT/'data/proof-audit.json'),share120_audit_sha256=sha(HERE.parent/'critical-charge/share-proof/data/proof-audit.json'),scope='The new count-free share-12 theorem and old share-120 theorem import together. The bound 234 is checked only under the stated weight inequalities; nine stronger share proofs and global assembly remain pending.')
(HERE/'data/integration-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(checks),'axiom audits')
