"""Materialize the same initial clauses for a bounded, unconnected replay benchmark."""
from pathlib import Path
import hashlib,importlib.util,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
gp=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
sp=importlib.util.spec_from_file_location('literal144',gp);lr=importlib.util.module_from_spec(sp);sp.loader.exec_module(lr)
meta=json.loads((H/'data/share144.json').read_text());raw=lr.read_cnf_core(str(H/'certificates/share144.cnf'),meta['core_ids'])
assert len(raw)==13224
offset=0;defs=[];node_rows=[]
def tree(depth,base):
 global offset
 if depth==0:return 'Tree.nil'
 if offset==len(raw):return f'(perf {depth} {base})'
 key=base+(1<<(depth-1));clause=raw[offset];offset+=1
 encoded=[2*abs(v)+(v<0) for v in clause]
 node_rows.append((key,clause))
 left=tree(depth-1,base);right=tree(depth-1,key)
 expr=f'(Tree.node {key} (rawMask {encoded}) {left} {right})'
 if depth==7:
  name=f'part{len(defs)}';defs.append(f'noncomputable def {name} : Tree := {expr}')
  return name
 return expr
start=tree(14,0);assert offset==len(raw)
assert [k for k,_ in node_rows]==lr.preorder_keys(14)[:len(raw)]
data=H/'experiments/lean/LiteralData144.lean';assert not data.exists()
s='''import LratFast144
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.LiteralData144
open Snake9.Lrat144 (Tree rawMask)
open Snake9.LratFast144 (perf)
'''+ '\n'.join(defs)+f'\nnoncomputable def start : Tree := {start}\nend Snake9.LiteralData144\n'
data.write_text(s,encoding='utf-8',newline='\n')
for old,new in [('RawInitSmall144','LiteralSmall144'),('RawInitProbe144','LiteralProbe144')]:
 s=(H/f'experiments/lean/{old}.lean').read_text()
 s=s.replace('import RawInit144\nimport LocalWindowCnf.ShareWindow144','import LiteralData144')
 s=s.replace(f'namespace Snake9.{old}',f'namespace Snake9.{new}').replace(f'end Snake9.{old}',f'end Snake9.{new}').replace(f'axioms Snake9.{old}',f'axioms Snake9.{new}')
 s=s.replace('open Snake9.LocalWindow.ShareWindow144 (raw)\nnoncomputable def start := (Snake9.RawInit144.rawPre 14 0 raw).1','open Snake9.LiteralData144 (start)')
 p=H/f'experiments/lean/{new}.lean';assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
j=dict(status='PREPARED_LITERAL_DATABASE_BENCHMARK',clauses=len(raw),subtree_definitions=len(defs),preorder_clause_mapping_checked=True,
 initial_tree_validity_proof_complete=False,scope='This benchmark has no checked link from satisfiability of the original CNF to truth of the materialized initial tree. Passing a prefix checks only that prefix from this concrete tree.',
 source_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),data,H/'experiments/lean/LiteralSmall144.lean',H/'experiments/lean/LiteralProbe144.lean',H/'experiments/lean/RawInitSmall144.lean',H/'experiments/lean/RawInitProbe144.lean']})
(H/'experiments/data/literal-preparation.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['status','clauses','subtree_definitions']}))
