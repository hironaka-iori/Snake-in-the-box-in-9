"""Build a typed initial tree from the preserved144 literal database."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
old=R/'milestones/144-countfree-share18/experiments/lean/LiteralData144.lean'
s=old.read_text()
s=s.replace('import LratFast144','import InputTree145\nimport LiteralData144\nimport LocalWindowCnf.ShareWindow144')
s=s.replace('namespace Snake9.LiteralData144','namespace Snake9.InputData145').replace('end Snake9.LiteralData144','end Snake9.InputData145')
s=s.replace('open Snake9.Lrat144 (Tree rawMask)\nopen Snake9.LratFast144 (perf)','open Snake9.InputTree145 (InputTree)')
s=s.replace(': Tree :=',': InputTree :=').replace('Tree.nil','InputTree.empty').replace('Tree.node','InputTree.node').replace('(perf ','(InputTree.tautology ')
s=re.sub(r'\(rawMask (\[[^\]]*\])\)',r'\1',s)
s=s.replace('noncomputable def start : InputTree :=','def tree : InputTree :=')
s=s.replace('noncomputable def part','def part')
addition='''
theorem clauses_eq : tree.clauses = Snake9.LocalWindow.ShareWindow144.raw := by
  rfl

noncomputable def start : Snake9.Lrat144.Tree := tree.build

theorem materialized_eq : start = Snake9.LiteralData144.start := by
  rfl

theorem start_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :
    Snake9.Lrat144.TreeTrue τ start :=
  tree.start_true τ clauses_eq h

#print axioms clauses_eq
#print axioms materialized_eq
#print axioms start_true
'''
s=s.replace('end Snake9.InputData145',addition+'\nend Snake9.InputData145')
target=H/'lean/InputData145.lean';assert not target.exists();target.write_text(s,encoding='utf-8',newline='\n')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
j=dict(status='PREPARED_CONCRETE_INITIAL_TRUTH_BRIDGE_LEAN_PENDING',clauses=13224,
 source_files_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),old,H/'lean/InputTree145.lean']},source_sha256=sha(target),
 scope='Checks the preserved144 initial database. This is infrastructure for selected012301 proof; no share or global theorem yet.')
(H/'data/initial-bridge-preparation.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({k:j[k] for k in ['status','clauses','source_sha256']}))
