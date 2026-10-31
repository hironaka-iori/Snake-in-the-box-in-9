"""Offline full-CNF Lean replay preparation using the repository's generator.
Generates source and runs Python-format simulation only. It never invokes Lean.
"""
from pathlib import Path
import gzip,json,sys,hashlib,types,re,time
H=Path(__file__).resolve().parent;REPO=H.parent/'branch241-audit/repo';SRC=REPO/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py';OUT=H/'lrat_replay';INPUT=H/'lrat_input';META=INPUT/'meta'
for p in (OUT,INPUT,META,OUT/'LocalWindowCnf'):p.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(H.parent/'branch241-review'))
from rup_check import check
start=time.perf_counter()
with gzip.open(H.parent/'branch241-review/loop_k1_cap21_r4_all8/checked_unsat.json.gz','rt',encoding='utf-8') as f:d=json.load(f)
verified=check(d['clauses'],d['proof']);n=len(d['clauses']);name='pointwise';mod='PointwiseScore22'
assert max(abs(l) for c in d['clauses'] for l in c)<5000
maxlit=max(len(p['clause']) for p in d['proof']);maxhint=max(len(p['hints']) for p in d['proof']);assert maxlit<2048 and maxhint<4095
with (INPUT/(name+'.cnf')).open('w',encoding='ascii') as f:
 f.write(f'p cnf 4007 {n}\n')
 for c in d['clauses']:f.write(' '.join(map(str,c))+' 0\n')
with (INPUT/(name+'.lrat')).open('w',encoding='ascii') as f:
 for i,p in enumerate(d['proof']):f.write(f'{n+i+1} '+' '.join(map(str,p['clause']))+' 0 '+' '.join(map(str,p['hints']))+' 0\n')
(META/(name+'.json')).write_text(json.dumps({'module':mod,'core_ids':list(range(1,n+1))}),encoding='utf-8')
# Preserve original CNF clause order exactly. Chunk only the Lean syntax.
chunks=[];parts=['import LocalWindowModel\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.'+mod+'\n']
for k,a in enumerate(range(0,n,1024)):
 chunk='rawChunk'+str(k);chunks.append(chunk)
 code=lambda l:2*abs(l)+(l<0)
 rows=['['+', '.join('nat_lit '+str(code(l)) for l in c)+']' for c in d['clauses'][a:a+1024]]
 parts.append('noncomputable def '+chunk+' : List (List Nat) := [\n'+',\n'.join(rows)+']\n')
parts.append('noncomputable def raw : List (List Nat) := ['+', '.join(chunks)+'].flatten\nnoncomputable def cnf : List (List Int) := raw.map (List.map decodeLit)\nend Snake9.LocalWindow.'+mod+'\n')
(OUT/'LocalWindowCnf'/f'{mod}.lean').write_text('\n'.join(parts),encoding='utf-8')
# Reuse the audited project planner and soundness composition. The sole layout
# adapter allows packed proof lists in multiple files, rather than one huge module.
source=SRC.read_text(encoding='utf-8');needle='    if PACKED:   # one module'
assert source.count(needle)==1
adapted=source.replace(needle,'    if PACKED and MERGE_PACKED:   # one module')
adapted=adapted.replace("with open(p, 'w') as f:","with open(p, 'w', encoding='utf-8') as f:").replace('open(p).read()',"open(p, encoding='utf-8', errors='replace').read()")
M=types.ModuleType('project_replay_adapter');M.__file__=str(SRC);exec(compile(adapted,str(SRC),'exec'),M.__dict__)
M.W=18;M.M=(1<<18)-1;M.FAST=True;M.OFF=5000;M.SPLIT=True;M.FLAG=1<<17;M.LIT_FUEL=2048;M.HINT_FUEL=4095
M.BASE_NS='Snake9.LratO5k';M.CHECKER_IMPORT='import PeerLratFast2_5000W18';M.CHECKER_OPEN='open Snake9.PeerLratFast5000W18\nopen Snake9.PeerLratFast2_5000W18\nopen Snake9.LratO5k (Tree TreeTrue andB)';M.F2F='PeerLratFast2F_5000W18'
M.DATA_DEF='noncomputable def';M.PACKED=16384;M.GROUPED=True;M.MERGE_PACKED=False
(OUT/'LocalWindowUnsat'/mod).mkdir(parents=True,exist_ok=True)
stats=M.export(name,str(INPUT),12000,4,4,True,str(OUT),data=str(META))
for p in (OUT/'LocalWindowUnsat').rglob('*.lean'):
 t=p.read_text(encoding='utf-8');t=t.replace('Kernel-checked LRAT','Prepared LRAT (NOT yet kernel-replayed)')
 p.write_text('/- Full certificate source is UNREPLAYED. Python simulation is not kernel compilation. -/\n'+t,encoding='utf-8')
(OUT/'PeerLratFinalAudit.lean').write_text('import LocalWindowUnsat.PointwiseScore22\n#print axioms Snake9.LocalWindow.PointwiseScore22.unsat\n',encoding='utf-8')
files={str(p.relative_to(OUT)).replace('\\','/')[:-5].replace('/','.'):p for p in OUT.rglob('*.lean')}
order=[];pending=set(files)
while pending:
 ready=sorted(x for x in pending if all(im not in pending for im in re.findall(r'^import (\S+)',files[x].read_text(encoding='utf-8'),re.M)))
 if not ready:raise RuntimeError(('dependency cycle',pending))
 order.extend(ready);pending.difference_update(ready)
manifest={'status':'FULL CERTIFICATE UNREPLAYED: generated, independently Python checked and format-simulated; no Lean compiler invoked','theorem_if_compiled':'Snake9.LocalWindow.PointwiseScore22.unsat : Unsat cnf','geometry_bridge_status':'NOT proved in Lean; exact propositional CNF theorem only','all_original_clauses_retained':True,'original_clause_count':n,'original_clause_order_preserved':True,'max_variables':4007,'word_bits':18,'literal_offset':5000,'literal_fuel':2048,'max_lemma_literals':maxlit,'max_hints_per_step':maxhint,'Python_RUP':verified,'project_generator_sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'generator_adapter':'OFF5000,W18,flag131072,fuel2048; packed data kept in separate modules','CNF_sha256':hashlib.sha256(json.dumps(d['clauses'],separators=(',',':')).encode()).hexdigest(),'stats':stats,'generated_source_bytes':sum(p.stat().st_size for p in files.values()),'generated_modules':len(files),'build_order':order,'preparation_seconds':time.perf_counter()-start}
manifest['module_source_sha256']={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in files.items()}
manifest['build_driver_sha256']=hashlib.sha256((H/'build_replay.py').read_bytes()).hexdigest()
(H/'full_replay_manifest.json').write_text(json.dumps(manifest,indent=2));print(json.dumps({k:v for k,v in manifest.items() if k!='build_order'},indent=2))

