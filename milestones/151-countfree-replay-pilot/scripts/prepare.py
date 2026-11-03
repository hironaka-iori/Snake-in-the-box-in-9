"""Check the exact prepared012032 pilot in a separate milestone directory."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/150-actual-pair-share';Q=R/'milestones/147-countfree-clause-semantics'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists(),p
    p.write_text(s,encoding='utf-8',newline='\n')
def change(s,a,b):
    assert s.count(a)==1,(a,s.count(a));return s.replace(a,b)
oldplan=P/'replay/data/pilot-source-plan.json'
review=P/'audit/transport-review.json'
assert sha(review)=='e705a688230c84116ec26e25a6fad5f2ad0bab89e09f5f7a832adf14e3c97eec'
plan=read(oldplan);assert plan['module_count']==38 and plan['status']=='SOURCE_PREPARED_UNCHECKED'
pins={str(oldplan):sha(oldplan),str(review):sha(review)}
for a in plan['artifacts']:
    p=P/'replay'/a['path'];assert sha(p)==a['sha256']
    out=H/a['path'];out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists()
    out.write_bytes(p.read_bytes());assert sha(out)==a['sha256'];pins[str(p)]=a['sha256']
plan.update(checking_milestone=151,exact_source_copies=True,
    prepared_source_plan=str(oldplan),prepared_source_plan_sha256=sha(oldplan))
write(H/'data/pilot-source-plan.json',json.dumps(plan,indent=2)+'\n')
s=(Q/'scripts/check_replay.py').read_text(encoding='utf-8')
s=change(s,"P=Path(__file__).resolve().parents[1];H=P/'replay';R=P.parents[1]",
    "H=Path(__file__).resolve().parents[1];R=H.parents[1]\nP=R/'milestones/150-actual-pair-share';Q=R/'milestones/147-countfree-clause-semantics'")
s=change(s,"env['LEAN_PATH']=str(build)+';'+str(P/'build')",
    "env['LEAN_PATH']=';'.join(map(str,[build,P/'build',Q/'build']))")
s=change(s,"    if not rp.exists():rp=P/'data'/(name+'-audit.json')",
    "    if not rp.exists():rp=P/'data'/(name+'-audit.json')\n    if not rp.exists():rp=Q/'data'/(name+'-audit.json')")
s=change(s,"    for p,d in q['dependencies'].items():\n        assert sha(p)==d,p;deps[p]=d",
    "    for p,d in q['dependencies'].items():\n        if p in deps:assert deps[p]==d,p\n        else:\n            assert sha(p)==d,p;deps[p]=d")
s=change(s,"assert p.is_relative_to(build.resolve()) or p.is_relative_to((P/'build').resolve()) or p.is_relative_to((B.parent/'lib/lean').resolve()),p",
    "assert any(p.is_relative_to(root.resolve()) for root in [build,P/'build',Q/'build',B.parent/'lib/lean']),p")
s=s.replace("['LratCheck147Replay','LratFast147Replay','InputTree147Replay','ReplayTools147']",
            "['LratCheck150Replay','LratFast150Replay','InputTree150Replay','ReplayTools150']")
s=change(s,"All project models are freshly checked from saved sources.",
    "The38 pilot modules are freshly checked. The exact concrete input from150 and generic local models from147 are reused with pinned source/object/log/dependency receipts. Each dependency is hashed once in preflight and again after compilation.")
s=change(s,"paths=[str(build),str(P/'build')]","paths=[str(build),str(P/'build'),str(Q/'build')]")
write(H/'scripts/check_replay.py',s)
s=(Q/'scripts/run_replay.py').read_text(encoding='utf-8')
s=change(s,"P=Path(__file__).resolve().parents[1];H=P/'replay';R=P.parents[1]",
    "H=Path(__file__).resolve().parents[1];R=H.parents[1]")
s=s.replace("P/'scripts/check_replay.py'","H/'scripts/check_replay.py'")
s=s.replace('15-bit checker','14-bit checker')
write(H/'scripts/run_replay.py',s)
s=(P/'scripts/serialize_semantics.py').read_text(encoding='utf-8')
s=s.replace('run_semantics.py','run_replay.py').replace('semantic-batch.lock','replay-batch.lock')
s=s.replace('150','151')
write(H/'scripts/serialize_replay.py',s)
for p in [Q/'scripts/check_replay.py',Q/'scripts/run_replay.py',P/'scripts/serialize_semantics.py',Path(__file__)]:pins[str(p)]=sha(p)
record=dict(status='PREPARED_EXACT_38_MODULE_012032_PILOT',
    source_files_sha256=pins,generated_sha256={str(p):sha(p) for p in [H/'scripts/check_replay.py',H/'scripts/run_replay.py',H/'scripts/serialize_replay.py',H/'data/pilot-source-plan.json']},
    module_count=38,mathematical_source_bytes_unchanged=True,
    initial_core_clauses=13655,initial_chunks=107,prefix_deductions=2169,prefix_references=6151,
    limits='One compiler. Generic modules1 thread/8192KiB stack, concrete modules2 threads/65536KiB. Per-module180s, own-process3GiB, free-memory floor768MiB; launch requires1.5GiB free and zero other Lean processes.',
    selection='Hold the existing147 coordinator between checks, run this bounded pilot, then resume that same coordinator. No new full replay is launched.')
write(H/'data/preparation.json',json.dumps(record,indent=2)+'\n')
print(record['status'])
