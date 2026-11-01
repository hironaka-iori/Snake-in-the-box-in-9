"""Generate a real share-core semantic check; all generated results remain pending until compiled."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[3];OUT=HERE
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat as gen
for d in ['lean/LocalWindowCnf','lean/Share7306','data','certificates','logs','build']:(OUT/d).mkdir(parents=True,exist_ok=True)
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,s):(OUT/'lean'/name).write_text(s,encoding='utf-8',newline='\n')
def cnf(p):return [list(map(int,s.split()))[:-1] for s in p.read_text().splitlines() if s and not s.startswith(('p','c'))]
meta=read(Path('E:/Snake-in-a-box/milestones/72-four-count-proof-closure/critical-current/data/general6-cap15-certificate.json'));assert meta['status']=='NATIVE_DRAT_VERIFIED'
original=Path('E:/Snake-in-a-box/milestones/72-four-count-proof-closure/critical-current/build/general6-cap15.cnf');corefile=Path('E:/Snake-in-a-box/milestones/72-four-count-proof-closure/critical-current/build/general6-cap15.core.cnf')
assert sha(original)==meta['cnf_sha256'] and sha(corefile)==meta['core_sha256']
e=TaggedShare(meta['directions'],meta['bounds'],15)
prior={'cycle_cuts':meta.get('cycle_cuts',[])}
for cc in prior['cycle_cuts']:
 assert gen.is_cycle_set(cc);e.add([-e.var[v] for v in cc],('old',('cut',)))
assert e.clauses==cnf(original)
core=cnf(corefile);lookup={tuple(sorted(c)):i for i,c in enumerate(e.clauses)}
indices=[lookup[tuple(sorted(c))] for c in core];tags=[e.tags[i] for i in indices]
# Use the original clause order within each clause so the tagged checker can read it.
core=[e.clauses[i] for i in indices]
active={abs(x) for c in core for x in c};needed=set(active)
for lits,*_ in e.ctrs:needed.update(abs(x) for x in lits)
for lits,*_ in e.tots:needed.update(abs(x) for x in lits)
order=sorted(active)+sorted(needed-active);rename={x:i+1 for i,x in enumerate(order)};nv=len(order)
rl=lambda x:(1 if x>0 else -1)*rename[abs(x)];code=lambda x:gen.code(rl(x))
compact=[[rl(x) for x in c] for c in core]
(OUT/'certificates/share7306.cnf').write_text(f'p cnf {len(active)} {len(core)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in compact),newline='\n')
raw=[[code(x) for x in c] for c in core];chunks=[raw[i:i+128] for i in range(0,len(raw),128)];tagchunks=[tags[i:i+128] for i in range(0,len(tags),128)]
HEADER='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
NS='Snake9.LocalWindow.ShareWindow7306'
body='import LocalWindowShareModel\n'+HEADER+'namespace '+NS+'\n'
body+=f'def window : List Nat := {e.window}\ndef bounds : List (Nat × Nat) := '+str([tuple(x) for x in meta['bounds']])+'\ndef resolution : Nat := 12\ndef cap : Nat := 15\n'
for i,chunk in enumerate(chunks):body+=f'def raw{i} : List (List Nat) := '+str(chunk)+'\n'
body+='def raw : List (List Nat) := '+' ++ '.join(f'raw{i}' for i in range(len(chunks)))+' ++ []\ndef cnf : List (List Int) := raw.map (·.map decodeLit)\nend '+NS+'\n'
write('LocalWindowCnf/ShareWindow7306.lean',body)
def leaves(r,s):
 if r+s>nv:return [r]
 return leaves(r,2*s)+leaves(r+s,2*s)
old={rename[k]:v for k,v in e.meaning.items() if k in rename};new={rename[k]:v for k,v in e.smeaning.items() if k in rename}
def leaf48(k):
 m=old.get(k)
 if m is None:return 0
 if m[0]=='p':return 1+4*m[1]
 if m[0]=='e':return 2+4*m[1]
 _,c,i,j=m;assert c<256 and i<65536 and j<(1<<22)
 return 3+4*(c+(i<<8)+(j<<24))
def leaf64(k):
 m=new.get(k)
 if m is None:return 0
 if m[0]=='sq':return 1+4*(m[1]+(m[2]<<16)+(m[3]<<24))
 if m[0]=='u':return 3+4*(m[1]+(m[2]<<16))
 _,i,lo,hi,c=m;assert i<1024 and lo<65536 and hi<65536 and c<(1<<20)
 return 2+4*(i+(lo<<10)+(hi<<26)+(c<<42))
def stream(xs,bits):
 out=0
 for x in reversed(xs):assert 0<=x<1<<bits;out=(out<<bits)|x
 return out
ms=stream([leaf48(k) for k in leaves(0,1)],48);xs=stream([leaf64(k) for k in leaves(0,1)],64)
body='import LocalWindowTagsPacked\nimport LocalWindowTagsSharePacked\nimport LocalWindowCnf.ShareWindow7306\n'+HEADER+'namespace '+NS+'\nopen Snake9.LocalWindow.Tags\n'
body+=f'noncomputable def meaning : MT := (mtB {nv} 64 0 1 (nat_lit 0x{ms:x})).1\nnoncomputable def smeaning : MS := (mtB64 {nv} 64 0 1 (nat_lit 0x{xs:x})).1\n'
ct=[]
for lits,k,kind in e.ctrs:
 kt='.ends' if kind[0]=='ends' else f'(.{kind[0]} {kind[1]})'
 ct.append('⟨'+str([code(x) for x in lits])+f', {k}, {kt}⟩')
body+='def ctrs : List Ctr := ['+','.join(ct)+']\n'
tt=[]
for lits,kind in e.tots:
 kt=f'(.{kind[0]} {kind[1]})' if kind[0]!='cap' else '(.cap '+str(kind[1])+')'
 tt.append('⟨'+str([code(x) for x in lits])+', '+kt+'⟩')
body+='def tots : List Tot := ['+','.join(tt)+']\n'
def tag(t):
 if t[0]=='old':return '(.old '+gen.lean_tag(t[1])+')'
 return gen.lean_tag(t)
for i,chunk in enumerate(tagchunks):body+=f'def tags{i} : List TagS := ['+','.join(map(tag,chunk))+']\n'
body+='def tags : List TagS := '+' ++ '.join(f'tags{i}' for i in range(len(chunks)))+' ++ []\nend '+NS+'\n'
write('Share7306/Data.lean',body)
head='import Share7306.Data\n'+HEADER+'namespace '+NS+'\nopen Snake9.LocalWindow.Tags\n'
write('Share7306/Structure.lean',head+'theorem counts_ok : ctrs.all (ctrOK meaning (centresK window bounds)) = true := by decide +kernel\ntheorem totals_ok : tots.all (totOK meaning smeaning window (centresK window bounds)) = true := by decide +kernel\n#print axioms counts_ok\n#print axioms totals_ok\nend '+NS+'\n')
for i in range(len(chunks)):
 write(f'Share7306/Shard{i:02d}.lean',head+f'theorem shard{i} : ckAllS meaning smeaning resolution ctrs tots window cap tags{i} raw{i} = true := by decide +kernel\n#print axioms shard{i}\nend '+NS+'\n')
report=dict(module='LocalWindowCnf.ShareWindow7306',core_ids=list(range(1,len(core)+1)),source_original_clause_ids=[i+1 for i in indices],original_to_new=rename,active_variables=len(active),semantic_variables=nv,clauses=len(core),shards=len(chunks),source_core_sha256=sha(corefile),source_full_sha256=sha(original),scope='Generated uncompiled share-clause interpretation; not a theorem until Lean checks succeed.')
(OUT/'data/share7306.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items() if k not in ['core_ids','source_original_clause_ids','original_to_new']},flush=True)
