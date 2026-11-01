"""Check completed share proof records, source mapping, and printed axiom scope."""
from pathlib import Path
import ast,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[3];OUT=HERE
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
records={}
for name in ['semantic-record.json','composition-record.json','completion-record.json']:
 f=OUT/'logs'/name
 if not f.exists():continue
 meta=read(f)
 for row in meta['records']:
  source=OUT/'lean'/(row['module']+'.lean')
  if row['exit_code']==0 and source.exists() and sha(source)==row['source_sha256'] and (Path(meta['build'])/(row['module']+'.olean')).exists():records[row['module']]=row
sources={p.relative_to(OUT/'lean').with_suffix('').as_posix():p for p in (OUT/'lean').rglob('*.lean')}
assert 'Share7305/Geometry' in records,'Arbitrary-snake wrapper is not yet checked'
for name,source in sources.items():
 assert name in records,name
 for line in source.read_text().splitlines():
  if line.startswith('import '):
   dep=line.split()[1].replace('.','/')
   if dep in sources:assert dep in records,(name,dep)
 assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text()),name
 log=OUT/'logs'/(name.replace('/','-')+'.log');txt=log.read_text() if log.exists() else ''
 assert 'error:' not in txt and 'sorryAx' not in txt and 'failed to delete' not in txt,name
 for dep,h in records[name].get('dependencies',{}).items():assert sha(sources[dep])==h,(name,dep)
checks=[]
for name,source in sources.items():
 n=len(re.findall(r'^#print axioms ',source.read_text(),re.M))
 if not n:continue
 txt=(OUT/'logs'/(name.replace('/','-')+'.log')).read_text()
 rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",txt,re.S)+[(x,'') for x in re.findall(r"'([^']+)' does not depend on any axioms",txt)]
 assert len(rows)==n,(name,n,rows)
 for theorem,axs in rows:
  assert set(re.findall(r'[A-Za-z][\w.]*',axs))<={'propext','Classical.choice','Quot.sound'}
  checks.append(dict(theorem=theorem,axioms=axs))
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat as gen
m=read(OUT/'data/share7305.json');native=read(Path('E:/Snake-in-a-box/milestones/72-four-count-proof-closure/critical-current/data/general5-cap11-certificate.json'))
e=TaggedShare(native['directions'],native['bounds'],11)
for cc in native.get('cycle_cuts',[]):
 assert gen.is_cycle_set(cc);e.add([-e.var[v] for v in cc],('old',('cut',)))
cnf=lambda p:[list(map(int,l.split()))[:-1] for l in p.read_text().splitlines() if l and l[0] not in 'pc']
assert e.clauses==cnf(Path('E:/Snake-in-a-box/milestones/72-four-count-proof-closure/critical-current/build/general5-cap11.cnf'))
rename={int(k):v for k,v in m['original_to_new'].items()};lit=lambda x:(1 if x>0 else -1)*rename[abs(x)]
core=[[lit(x) for x in e.clauses[i-1]] for i in m['source_original_clause_ids']]
assert core==cnf(OUT/'certificates/share7305.cnf')
source=(OUT/'lean/LocalWindowCnf/ShareWindow7305.lean').read_text()
chunks=[ast.literal_eval(x) for x in re.findall(r'^def raw\d+ : List \(List Nat\) := (.+)$',source,re.M)]
assert [c for chunk in chunks for c in chunk]==[[gen.code(x) for x in c] for c in core]
assert read(OUT/'data/export.json')['simulated']
out=dict(status='PASS_LOCAL_SHARE_THEOREM',modules=len(sources),theorem_audits=checks,source_sha256={k:sha(v) for k,v in sources.items()},directions=native['directions'],bounds=native['bounds'],share_lower=12,scope='Lean-checked coreShare sum for arbitrary matching snakes, with coordinate normalization. Existing imported local-window support reused. Full global graph interpretation and new global numerical bounds are not established.')
(OUT/'data/proof-audit.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['theorem_audits','source_sha256']},'audits',len(checks),flush=True)
