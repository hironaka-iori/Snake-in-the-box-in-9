"""Export the extracted core; its clauses do not use the joint-count hypothesis."""
import collections,json,subprocess,sys
from pathlib import Path
from tagged_pair import TaggedPairShare
import gen_lean_sat as gen
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
m=json.loads((HERE/'data/pairshare.json').read_text());e=TaggedPairShare(m['dirs'],m['bounds'],11)
assert not m['cycle_cuts']
rename={int(k):v for k,v in m['original_to_new'].items()}
lit=lambda x:(1 if x>0 else -1)*rename[abs(x)]
tags=[e.tags[i-1] for i in m['source_original_clause_ids']]
assert all(t[0]!='old' or t[1][0] in ('window','deg2') for t in tags)
clauses=[[lit(x) for x in e.clauses[i-1]] for i in m['source_original_clause_ids']]
core=[list(map(int,l.split()))[:-1] for l in (HERE/'certificates/pairshare.cnf').read_text().splitlines() if l and not l.startswith(('c','p'))]
assert clauses==core
for d in ('LocalWindowCnf','LocalWindowSat'):(HERE/'lean'/d).mkdir(exist_ok=True)
src='import LocalWindowModel\nset_option maxRecDepth 100000\nnamespace Snake9.LocalWindow.PairShareCert\n'
src+=f'def window : List Nat := {e.window}\ndef bounds : List (Nat × Nat) := '+str([tuple(x) for x in m['bounds']])+'\n'
src+='def raw : List (List Nat) := [\n'+',\n'.join(str([gen.code(x) for x in c]) for c in core)+']\n'
src+='def cnf : List (List Int) := raw.map (·.map decodeLit)\nend Snake9.LocalWindow.PairShareCert\n'
(HERE/'lean/LocalWindowCnf/PairShareCert.lean').write_text(src,encoding='utf-8')
m['module']='LocalWindowCnf.PairShareCert'
(HERE/'data/pairshare.json').write_text(json.dumps(m,indent=2)+'\n')
def stree():
 meaning={rename[k]:v for k,v in e.smeaning.items()}
 def build(r,s):
  if r+s>len(rename):
   v=meaning.get(r)
   return '.z' if v is None else '(.'+v[0]+' '+' '.join(map(str,v[1:]))+')'
  return f'(.n {build(r,2*s)} {build(r+s,2*s)})'
 return build(0,1)
def tot(t):
 ls,k=t
 kind=f'(.{k[0]} {k[1]})'
 return '⟨'+str([gen.code(lit(x)) for x in ls])+', '+kind+'⟩'
def tag(t):return '(.old '+gen.lean_tag(t[1])+')' if t[0]=='old' else gen.lean_tag(t)
src='''import JointShareTags
import LocalWindowCnf.PairShareCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.PairShareCert
open Tags
'''
src+='def meaning : MT := '+gen.lean_tree_terms({rename[k]:v for k,v in e.meaning.items()},len(rename))+'\n'
src+='def shareMeaning : MS := '+stree()+'\n'
src+='def tots : List Tot := [\n'+',\n'.join(tot(t) for t in e.tots)+']\n'
src+='def tags : List TagS := [\n'+',\n'.join(tag(t) for t in tags)+']\n'
for name,j in [('centreA',1),('centreB',6)]:
 src+=f'def {name} : Centre := ⟨{e.window[j]}, {m["dirs"][j-1]}, {m["dirs"][j]}, 0, 21⟩\n'
src+='''def shareCentres : List Centre := [centreA,centreB]
theorem tot_check : tots.all (totOK meaning shareMeaning window shareCentres) = true := by decide +kernel
theorem clause_check : ckAllS meaning shareMeaning 12 [] tots window 11 tags raw = true := by decide +kernel
theorem sat (S E : Nat → Bool) (ax : Axioms S E window (centresOf window bounds))
    (hs : shareSum 12 S shareCentres ≤ 11) : ∃ τ, cnfTrue τ cnf = true := by
  have hv : JointTags.Valid S E meaning [] := by
    apply JointTags.valid_of_all
    intro ct hc
    simp at hc
  exact ⟨tauS S E meaning shareMeaning 12 [] tots,
    PairShare.sound meaning shareMeaning 12 [] tots window (centresOf window bounds)
      shareCentres 11 tags raw clause_check tot_check S E hv ax hs⟩
#print axioms sat
end Snake9.LocalWindow.PairShareCert
'''
(HERE/'lean/LocalWindowSat/PairShareCert.lean').write_text(src,encoding='utf-8')
cmd=[sys.executable,'-X','utf8',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py','--work',HERE/'certificates','--data',HERE/'data','--out',HERE/'lean','--fast','--check','--noncomputable-data','--off','2400','pairshare']
p=subprocess.run(list(map(str,cmd)),capture_output=True,text=True,encoding='utf-8');(HERE/'logs/export.txt').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stderr
print(p.stdout)
print('Core families:',collections.Counter(str(t) for t in tags))
