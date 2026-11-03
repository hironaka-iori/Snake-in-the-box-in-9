"""Audit the completed original-clause/tree connection and its bounded prefix."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[];pins={str(Path(__file__).relative_to(R)):sha(__file__)}
for name,count in [('RawChunksAssoc146',2),('AssemblyAssoc146',1),('PrefixAssoc146',1)]:
    rp=H/'data'/(name+'-audit.json');j=read(rp)
    assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    assert len(j['axioms'])==count and all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in j['axioms'])
    assert sha(j['source'])==j['source_sha256'] and sha(j['object'])==j['olean_sha256']
    assert sha(j['log'])==j['log_sha256']
    d=Path(j['log']).parent
    assert sha(d/'source.lean.txt')==j['source_sha256'] and sha(d/'checker.py.txt')==j['checker_sha256']
    for p,h in j['dependencies'].items():assert sha(p)==h
    rows.append(dict(module=name,receipt=rp.relative_to(H).as_posix(),receipt_sha256=sha(rp),seconds=j['seconds'],axioms=j['axioms']))
    pins[rp.relative_to(R).as_posix()]=sha(rp)
old=R/'milestones/145-countfree-012301/lean/ChunkTruthAssemblyFixed145.lean'
new=H/'lean/AssemblyAssoc146.lean'
old_body=old.read_text().split('  exact (Snake9.Lrat144.TreeTrue.node',1)[1].replace('end Snake9.ChunkData145','end Snake9.AssemblyAssoc146')
new_body=new.read_text().split('  exact (Snake9.Lrat144.TreeTrue.node',1)[1]
assert old_body==new_body
prefix=R/'milestones/144-countfree-share18/experiments/lean/LiteralProbe144.lean'
params=R/'milestones/144-countfree-share18/experiments/data/raw-init-probe.json'
q=read(params);assert q['hints']==6006 and q['deductions']==1055
assert len(re.findall(r'nat_lit 0x',prefix.read_text()))==1055
for p in [old,new,prefix,params,R/'milestones/145-countfree-012301/data/chunked-bridge-completion.json']:
    pins[p.relative_to(R).as_posix()]=sha(p)
j=dict(status='PASS_ORIGINAL_CNF_TO_INITIAL_TREE_AND_CHECKED_PREFIX',checked_modules=3,axiom_reports=4,
    original_core_clauses=13224,raw_chunks=104,tree_parts=104,existing_prefix_deductions=1055,existing_prefix_references=6006,
    original_constructor_body_preserved=True,initial_tree_truth_bridge_complete=True,
    full_share18_replay_complete=False,actual_share18_theorem_complete=False,actual_share16_theorem_complete=False,
    receipts=rows,source_files_sha256=pins,
    statement='For every assignment satisfying the original144 core CNF, the preserved materialized initial tree is true, and the1055-deduction prefix preserves truth.',
    improvement='One conjunction extraction normalizes append association; this replaces104 separate whole-list membership extractions. Timings are bounded measurements on this machine, not a general complexity result.',
    scope='The initial-database and bounded-prefix gap is closed. The full contradiction replay and actual-snake interpretation remain required; no new global bound.')
p=H/'data/bridge-completion.json';assert not p.exists();p.write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['status','checked_modules','axiom_reports','initial_tree_truth_bridge_complete']}))
