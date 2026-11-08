"""Prepare exact streamed-cap semantics; prior proof inputs remain immutable."""
from pathlib import Path
from types import SimpleNamespace
import gzip, hashlib, json, sys, re, copy
sys.dont_write_bytecode = True
R=Path('E:/Snake-in-a-box'); H=R/'milestones/185-critical-kernel'
P=R/'milestones/183-critical-floor15'; OLD=R/'milestones/180-share14-certificates'
G=R/'milestones/147-countfree-clause-semantics'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,text):
 p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),p
 p.write_text(text,encoding='utf-8',newline='\n')
def js(p,obj):save(p,json.dumps(obj,indent=2)+'\n')
for d in ['lean','scripts','data','build','logs','certificates']:(H/d).mkdir(exist_ok=True)
save(H/'scripts/prepare.py',Path(__file__).read_text())
for name in ['check_core.py','native_resources.py']:
 save(H/'scripts'/name,(R/'milestones/184-single-critical-floor/scripts'/name).read_text())
s=(G/'lean/LocalWindowTagsShare.lean').read_text()
s=s.replace('namespace Snake9.LocalWindow.Tags','namespace Snake9.LocalWindow.Tags185\nopen Snake9.LocalWindow.Tags')
s=s.replace('end Snake9.LocalWindow.Tags','end Snake9.LocalWindow.Tags185')
old='t.lits.map (uQT X) == capL cens spec';assert s.count(old)==1
s=s.replace(old,'(t.lits.map (uQT X)).isPerm (capL cens spec)')
old='rw [this, hm]\n    exact capL_le cens spec hs';assert s.count(old)==1
s=s.replace(old,'rw [this, (List.isPerm_iff.mp hm).countP_eq]\n    exact capL_le cens spec hs')
s+='\n#print axioms Snake9.LocalWindow.Tags185.cap_total\n#print axioms Snake9.LocalWindow.Tags185.soundS\n#print axioms Snake9.LocalWindow.Tags185.refutedShare_of_check\n'
save(H/'lean/LocalWindowTagsShare185.lean',s)
s=(G/'lean/LocalWindowTagsSharePacked.lean').read_text().replace('import LocalWindowTagsShare','import LocalWindowTagsShare185')
s=s.replace('namespace Snake9.LocalWindow.Tags','namespace Snake9.LocalWindow.Tags185\nopen Snake9.LocalWindow.Tags')
s=s.replace('end Snake9.LocalWindow.Tags','end Snake9.LocalWindow.Tags185')
save(H/'lean/LocalWindowTagsSharePacked185.lean',s)
meta=read(P/'data/012034-floor15.json');cnfpath=P/'cache/012034-floor15/input.cnf'
assert sha(cnfpath)==meta['cnf_sha256']
oldmeta=read(OLD/'data/012034.json');semfile=OLD/'certificates/012034.meanings.json.gz'
assert sha(semfile)==oldmeta['artifacts'][semfile.name]
sem=json.loads(gzip.decompress(semfile.read_bytes()))
deltafile=P/'certificates/012034-floor15.delta.json.gz'
assert sha(deltafile)==meta['artifacts'][deltafile.name]
delta=json.loads(gzip.decompress(deltafile.read_bytes()));assert delta['path_clauses']==[]
meaning={int(k):v for k,v in sem['meaning'].items()}
smeaning={int(k):v for k,v in sem['smeaning'].items()}
tots=copy.deepcopy(sem['tots']);tags=copy.deepcopy(sem['tags'][:-1])
assert len(tots)==71 and sem['tags'][-1]==['shareCap',70]
spec=copy.deepcopy(tots[70][1][1])
for centre in spec:
 for item in centre:
  assert item[1]==14;item[1]=15
tots.append([delta['new_cap_bits'],['cap',spec]])
new={int(k):v for k,v in delta['new_meanings'].items()}
for k,v in new.items():
 if v[0]=='u':smeaning[k]=v[:3]
 else:
  assert v[0]=='cap15';smeaning[k]=['t',71,*v[1:]]
def cnf(p):
 with Path(p).open() as f:
  return [list(map(int,line.split()))[:-1] for line in f if line and not line.startswith(('p','c'))]
clauses=cnf(cnfpath)
for cl in clauses[oldmeta['clauses']-1:]:
 v=new[abs(cl[0])]
 if v[0]=='u':tags.append(['shareCl',2*v[3],2*v[3]+1])
 elif len(cl)==1:
  assert cl==[-delta['new_cap_output']];tags.append(['shareCap',71])
 else:tags.append(['totUp',71])
assert len(tags)==len(clauses)
corefile=P/'cache/012034-floor15-core.cnf';coremeta=read(P/'data/012034-floor15-core.json')
assert sha(corefile)==coremeta['cnf_sha256']
mapping=json.loads(gzip.decompress((P/'certificates/012034-floor15-core.mapping.json.gz').read_bytes()))
variablefile=P/'certificates/012034-floor15-dense.variables.json.gz'
densevars=json.loads(gzip.decompress(variablefile.read_bytes()))['dense_to_original']
e=SimpleNamespace(clauses=clauses,tags=tags,meaning=meaning,smeaning=smeaning,ctrs=sem['ctrs'],tots=tots,window=[0,1,3,7,6,14,30])
meta['bounds']=[[0,21]]*5;OUT=H
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
import tagged_share
import gen_lean_sat as gen
template=R/'milestones/72-four-count-proof-closure/critical-current/scripts/prepare_lean.py'
s=template.read_text();s=s[s.index('core=cnf(corefile)'):]
s=s.replace('indices=[lookup[tuple(sorted(c))] for c in core];tags=[e.tags[i] for i in indices]',
 "indices=[i-1 for i in mapping['original_input_ids']]\nassert [e.clauses[i] for i in indices]==core\ntags=[e.tags[i] for i in indices]")
s=s.replace('active={abs(x) for c in core for x in c};needed=set(active)',
 "active=set(densevars);needed=set(active)\nassert {abs(x) for c in core for x in c}<=active")
s=s.replace('ShareWindow12','ShareWindow185').replace('Share12','Share185').replace('share12','share185')
s=s.replace('cap : Nat := 11','cap : Nat := 14').replace('import LocalWindowTagsSharePacked','import LocalWindowTagsSharePacked185')
s=s.replace('open Snake9.LocalWindow.Tags\\n','open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\\n')
for d in ['lean/LocalWindowCnf','lean/Share185']:(H/d).mkdir(exist_ok=True)
save(H/'scripts/generated_semantics.py',s)
def write(name,s):save(H/'lean'/name,s)
original=cnfpath
exec(compile(s,str(H/'scripts/generated_semantics.py'),'exec'),globals())
assert (H/'certificates/share185.cnf').read_bytes()==(P/'cache/012034-floor15-dense.cnf').read_bytes()
count=read(H/'data/share185.json')['shards'];namespace='Snake9.LocalWindow.ShareWindow185'
imports='import Share185.Structure\n'+''.join(f'import Share185.Shard{i:02d}\n' for i in range(count))
compose=imports+'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+namespace+'\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
compose+='theorem clauses_ok : ckAllS meaning smeaning resolution ctrs tots window cap tags raw = true := by\n'
compose+='  unfold tags raw\n  simp only [ckAllS_append]\n'
compose+='  simp only ['+', '.join(f'shard{i}' for i in range(count))+', Bool.true_and, ckAllS]\n'
compose+='theorem input_true (S E : Nat → Bool) (ax : AxiomsS S E window (centresOf window bounds) resolution cap) :\n  cnfTrue (tauS S E meaning smeaning resolution ctrs tots) cnf = true := by\n'
compose+='  exact soundS meaning smeaning resolution ctrs tots window bounds cap tags raw\n    (by simp only [checkAllS, counts_ok, totals_ok, clauses_ok, Bool.and_self]) S E ax\n'
compose+='theorem refuted_of_unsat (h : Unsat cnf) : RefutedShare window bounds resolution cap :=\n  refutedShare_of_sat (fun S E ax => ⟨_, input_true S E ax⟩) h\n'
compose+='#print axioms clauses_ok\n#print axioms input_true\n#print axioms refuted_of_unsat\nend '+namespace+'\n'
save(H/'lean/Share185/Compose.lean',compose)
files=sorted((H/'lean').rglob('*.lean'))
sources={p.relative_to(H/'lean').with_suffix('').as_posix().replace('/','.'):sha(p) for p in files}
pins={}
for name in ['LocalWindowModel','LocalWindowShareModel','LocalWindowTags','LocalWindowTagsPacked']:
 receipt=G/'data'/(name+'-audit.json');j=read(receipt)
 assert j['status']=='PASS' and j['exit_code']==0
 for key,dig in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(j[key])==j[dig]
 pins[str(receipt)]=sha(receipt)
 for p,d in j['dependencies'].items():assert sha(p)==d,p;pins[p]=d
 pins[j['source']]=j['source_sha256'];pins[j['object']]=j['olean_sha256']
for p in [Path(__file__),template,cnfpath,corefile,semfile,deltafile,variablefile,H/'scripts/generated_semantics.py',H/'scripts/native_resources.py']:pins[str(p)]=sha(p)
order=['LocalWindowTagsShare185','LocalWindowTagsSharePacked185','LocalWindowCnf.ShareWindow185','Share185.Data','Share185.Structure']+[f'Share185.Shard{i:02d}' for i in range(count)]+['Share185.Compose']
plan=dict(new_module_order=order,source_sha256=sources,input_pins=pins,
 lean_bin='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',
 search_paths=[str(H/'build'),str(G/'build')],checker_sha256=sha(H/'scripts/check_core.py'))
for name in order:js(H/'data'/(name+'-execution.json'),plan)
js(H/'data/preparation.json',dict(status='EXACT_DENSE_CORE_SEMANTICS_PREPARED',modules=len(order),shards=count,
 input_clauses=len(core),dense_cnf_sha256=sha(H/'certificates/share185.cnf'),semantic_variables=nv,
 mathematical_change='Cap input ordering generalized from equality to permutation, with count preservation.',
 kernel_refutation_complete=False))
print('PREPARED',len(order),'modules;',count,'clause batches; exact dense core preserved.',flush=True)

