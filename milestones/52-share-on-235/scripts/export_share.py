"""Export a share core with packed meanings and a kernel LRAT replay."""
from pathlib import Path
import gzip,json,sys,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import lrat_share as lg
NAME='supported0_95';MOD='SharePressure520';prefix=HERE/'certificates'/NAME
meta=json.loads((HERE/f'data/{NAME}.json').read_text())
with gzip.open(prefix.with_suffix('.meanings.json.gz'),'rt') as f:info=json.load(f)
full=[list(map(int,l.split()))[:-1] for l in prefix.with_suffix('.full.cnf').read_text().splitlines() if l and not l.startswith(('c','p'))]
ids=[j-1 for j in meta['source_original_clause_ids']];core=[full[j] for j in ids]
old={int(k):v for k,v in info['meaning'].items()};share={int(k):v for k,v in info['smeaning'].items()};used=sorted({abs(v) for c in core for v in c})
needed=set(used)|{abs(v) for ls,k,kind in info['ctrs'] for v in ls}|{abs(v) for ls,kind in info['tots'] for v in ls}
order=used+sorted(needed-set(used));rename={v:i+1 for i,v in enumerate(order)};inv={v:k for k,v in rename.items()};nv=len(order)
def lit(v):return (1 if v>0 else -1)*rename[abs(v)]
def code(v):return 2*v if v>0 else -2*v+1
compact=[[lit(v) for v in c] for c in core]
prefix.with_suffix('.cnf').write_text(f'p cnf {len(used)} {len(core)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in compact))
def leaves(r,s):return leaves(r,2*s)+leaves(r+s,2*s) if r+s<=nv else [r]
def stream(xs,bits):
 value=0
 for x in reversed(xs):assert 0<=x<1<<bits;value=(value<<bits)|x
 return value
def leaf48(x):
 m=old.get(inv.get(x))
 if m is None:return 0
 if m[0]=='p':return 1+4*m[1]
 if m[0]=='e':return 2+4*m[1]
 return 3+4*(m[1]+(m[2]<<8)+(m[3]<<24))
def leaf64(x):
 m=share.get(inv.get(x))
 if m is None:return 0
 if m[0]=='sq':return 1+4*(m[1]+(m[2]<<16)+(m[3]<<24))
 if m[0]=='u':return 3+4*(m[1]+(m[2]<<16))
 return 2+4*(m[1]+(m[2]<<10)+(m[3]<<26)+(m[4]<<42))
def tag48(t):
 c=i=j=0
 if t[0]=='old':
  t=t[1];k=['window','deg2','degPos','endSel','lowEnd','endLow','cut','first','zero','mono','step','over'].index(t[0])
  if len(t)>1:c=t[1]
  if len(t)>2:
   if t[0]=='zero':j=t[2]
   else:i=t[2]
  if len(t)>3:j=t[3]
 else:
  k=['emptyE','totUp','totDown','shareCl','shareCap'].index(t[0])+12
  if t[0]=='shareCl':i,j=t[1:]
  elif len(t)>1:c=t[1]
 assert c<256 and i<65536 and j<65536
 return k+(c<<5)+(i<<13)+(j<<29)
def packed_lits(ls):
 vals=[code(lit(v)) for v in ls];return f'natsOf {len(vals)} (nat_lit 0x{stream(vals,24):x})'
for folder in ['LocalWindowCnf','LocalWindowSat']:(HERE/'lean'/folder).mkdir(exist_ok=True)
header='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
ns='Snake9.LocalWindow.'+MOD
raw='[\n'+',\n'.join('['+','.join(str(code(v)) for v in c)+']' for c in compact)+'\n]'
cnf=f'import LocalWindowShareModel\n{header}namespace {ns}\ndef window : List Nat := {meta["window"]}\ndef bounds : List (Nat × Nat) := ['+','.join(f'({lo},{hi})' for lo,hi in meta['bounds'])+']\ndef resolution : Nat := 12\ndef cap : Nat := 95\ndef raw : List (List Nat) := '+raw+f'\ndef cnf : List (List Int) := raw.map (·.map decodeLit)\nend {ns}\n'
(HERE/f'lean/LocalWindowCnf/{MOD}.lean').write_text(cnf)
ctrs=[]
for ls,k,kind in info['ctrs']:
 kindtext='.ends' if kind[0]=='ends' else f'.{kind[0]} {kind[1]}'
 ctrs.append(f'⟨{packed_lits(ls)}, {k}, {kindtext}⟩')
tots=[]
for ls,kind in info['tots']:
 if kind[0]=='cap':kindtext='.cap ['+','.join('['+','.join(f'({a},{b})' for a,b in row)+']' for row in kind[1])+']'
 else:kindtext=f'.{kind[0]} {kind[1]}'
 tots.append(f'⟨{packed_lits(ls)}, {kindtext}⟩')
tags=[tag48(info['tags'][i]) for i in ids];chunks=[len(tags[j:j+64])+(stream(tags[j:j+64],48)<<8) for j in range(0,len(tags),64)]
src=f'import LocalWindowTagsShare\nimport LocalWindowTagsPacked\nimport LocalWindowTagsSharePacked\nimport LocalWindowCnf.{MOD}\n{header}namespace {ns}\nopen Snake9.LocalWindow.Tags\n'
src+=f'noncomputable def meaning : MT := (mtB {nv} 64 0 1 (nat_lit 0x{stream([leaf48(x) for x in leaves(0,1)],48):x})).1\n'
src+=f'noncomputable def smeaning : MS := (mtB64 {nv} 64 0 1 (nat_lit 0x{stream([leaf64(x) for x in leaves(0,1)],64):x})).1\n'
src+='noncomputable def ctrs : List Ctr := [\n'+',\n'.join(ctrs)+']\nnoncomputable def tots : List Tot := [\n'+',\n'.join(tots)+']\n'
src+='noncomputable def tags : List TagS := tagsOfSL ['+','.join(f'(nat_lit 0x{x:x})' for x in chunks)+']\n'
src+='theorem check : checkAllS meaning smeaning resolution ctrs tots window bounds cap tags raw = true := by decide +kernel\n'
src+='theorem sat : ∀ S E : Nat → Bool, AxiomsS S E window (centresOf window bounds) resolution cap → ∃ τ, cnfTrue τ cnf = true :=\n fun S E h => ⟨tauS S E meaning smeaning resolution ctrs tots, soundS meaning smeaning resolution ctrs tots window bounds cap tags raw check S E h⟩\n#print axioms sat\n'+f'end {ns}\n'
(HERE/f'lean/LocalWindowSat/{MOD}.lean').write_text(src)
meta.update(module='LocalWindowCnf.'+MOD,core_ids=list(range(1,len(core)+1)),active_variables=len(used),semantic_variables=nv,original_to_new=rename)
(HERE/f'data/{NAME}.json').write_text(json.dumps(meta,indent=2)+'\n')
if '--semantics-only' in sys.argv:
 print('Retained',nv,'meanings; active core and literal numbering unchanged.',flush=True)
 sys.exit(0)
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
with (HERE/f'logs/{NAME}-lrat-cadical.txt').open('w') as f:r=subprocess.run([str(exe),'-q','--lrat','--no-binary',str(prefix.with_suffix('.cnf')),str(prefix.with_suffix('.lrat'))],stdout=f,stderr=subprocess.STDOUT,timeout=240)
assert r.returncode==20
slots=lg.plan(meta['core_ids'],lg.read_lrat(str(prefix.with_suffix('.lrat'))))[3];bits=next(b for b in range(14,16) if slots<1<<b);off=6000;assert len(used)<off
cmd=[sys.executable,'-X','utf8',str(HERE/'scripts/lrat_share.py'),'--work',str(HERE/'certificates'),'--data',str(HERE/'data'),'--out',str(HERE/'lean'),'--fast','--check','--noncomputable-data','--wbits',str(bits),'--off',str(off),NAME]
with (HERE/f'logs/{NAME}-export.txt').open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=240)
assert r.returncode==0
wrapper=f'''import LocalWindowSat.{MOD}
import LocalWindowUnsat.{MOD}
import Mathlib.Tactic
namespace {ns}
theorem refuted_share : RefutedShare window bounds resolution cap :=
  Tags.refutedShare_of_sat sat unsat
theorem positive_share (S E : Nat → Bool) (h : Axioms S E window (centresOf window bounds)) :
    96 ≤ shareSum 12 S (centresOf window bounds) := by
  by_contra! hn
  exact refuted_share S E ⟨h,by simpa [resolution,cap] using (show shareSum 12 S (centresOf window bounds) ≤ 95 by omega)⟩
#print axioms refuted_share
#print axioms positive_share
end {ns}
'''
(HERE/'lean/SharePressure.lean').write_text(wrapper)
print('Core',len(core),'active variables',len(used),'slots',slots,'bits',bits,flush=True)
print((HERE/f'logs/{NAME}-export.txt').read_text()[:800],flush=True)
