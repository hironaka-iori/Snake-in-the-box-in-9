"""Prepare project-derived Std-only checker variants and a tiny kernel smoke test.
No Lean execution is performed. Full-certificate replay is a separate operation.
"""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;SRC=H.parent/'branch241-audit/repo/work/final_lean';OUT=H/'lrat_replay';OUT.mkdir(exist_ok=True)
BASE='PeerLratFast5000W18';SPLIT='PeerLratFast2_5000W18';FORCE='PeerLratFast2F_5000W18'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def variant(text,kind):
 text=text.replace('LratFast2F_O5k17',FORCE).replace('LratFast2_O5k17',SPLIT).replace('LratFastO5k17',BASE)
 text=text.replace('131071','262143').replace('65536','131072')
 text=re.sub(r'\b17\b','18',text)
 if kind==BASE:text=text.replace('litsL 255','litsL 2048')
 return '/- UNCOMPILED generated adapter: source proof retained; W=18, OFF=5000, literal fuel=2048. -/\n'+text
files=['LocalWindowModel.lean','LratCheckO5k.lean','ProofPack.lean','NatPack.lean']
provenance={}
for name in files:
 p=SRC/name;(OUT/name).write_text(p.read_text(encoding='utf-8'),encoding='utf-8');provenance[name]=digest(p)
for old,new in [('LratFastO5k17',BASE),('LratFast2_O5k17',SPLIT),('LratFast2F_O5k17',FORCE)]:
 p=SRC/(old+'.lean');(OUT/(new+'.lean')).write_text(variant(p.read_text(encoding='utf-8'),new),encoding='utf-8');provenance[old+'.lean']=digest(p)
W=18;FLAG=1<<17
words=[3,0,FLAG+1,FLAG+2,0];packed=sum(x<<(W*i) for i,x in enumerate(words))
smoke=f'''import {SPLIT}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PeerLratSmoke
open Snake9.LocalWindow
open Snake9.LratO5k (Tree TreeTrue andB unsat_of_raw)
open Snake9.{BASE}
open Snake9.{SPLIT}
def raw : List (List Nat) := [[2], [3]]
def cnf := raw.map (List.map decodeLit)
noncomputable def start : Tree := loadRaw (perf 2 0) raw [1,2]
noncomputable def proof : List Nat := [nat_lit {packed}]
theorem checked : andB (check2 start (perf 2 0) proof) (hasEmpty (replay start proof) 3) = true := by
  decide +kernel
theorem unsat : Unsat cnf := by
  apply unsat_of_raw
  intro t h
  have hs : TreeTrue t start := start_true (raw := raw) (h := 2) (slots := [1,2]) t h
  exact final_false2 (s := start) (ps := proof) (h := 2) t checked hs
#print axioms checked
#print axioms unsat
end PeerLratSmoke
'''
(OUT/'PeerLratSmoke.lean').write_text(smoke,encoding='utf-8')
parts=['import Std\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
for name in ['LocalWindowModel.lean','LratCheckO5k.lean',BASE+'.lean',SPLIT+'.lean','PeerLratSmoke.lean']:
 text=(OUT/name).read_text(encoding='utf-8');parts.append(re.sub(r'^import .*\n','',text,flags=re.M))
standalone=H/'PeerLratSmokeStandalone.lean';standalone.write_text('\n\n'.join(parts),encoding='utf-8')
manifest={'status':'UNCOMPILED; no kernel execution by generator','source_hashes':provenance,'standalone_smoke_bytes':standalone.stat().st_size,'word_bits':W,'literal_offset':5000,'literal_fuel':2048,'hint_fuel':4095,'source_root':str(SRC),'standalone_sha256':digest(standalone)}
(H/'lrat_preparation.json').write_text(json.dumps(manifest,indent=2));print(json.dumps(manifest,indent=2))
