"""Pin160 prefix-only sources and prior evidence; no transport execution."""
from pathlib import Path
import ast
import hashlib
import json

H=Path(__file__).resolve().parents[1];R=H.parents[1]


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()


def main():
    assert __debug__
    (H/'data').mkdir(parents=True,exist_ok=True)
    inputs=[
      'milestones/144-countfree-share18/data/share144.json',
      'milestones/144-countfree-share18/data/proof-plan-base.json',
      'milestones/144-countfree-share18/data/alternative-review.json',
      'milestones/144-countfree-share18/data/export-review.json',
      'milestones/144-countfree-share18/certificates/share144.cnf',
      'milestones/144-countfree-share18/certificates/share144.lrat',
      'milestones/144-countfree-share18/work/certificate-alternative/input.cnf',
      'milestones/144-countfree-share18/work/certificate-alternative/core-ids.json',
      'milestones/144-countfree-share18/scripts/prepare_raw_init_probe.py',
      'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py',
      'milestones/144-countfree-share18/experiments/lean/LiteralData144.lean',
      'milestones/144-countfree-share18/experiments/lean/LiteralProbe144.lean',
      'milestones/144-countfree-share18/experiments/data/raw-init-probe.json',
      'milestones/144-countfree-share18/experiments/data/LiteralProbe144-audit.json',
      'milestones/146-initial-tree-and-paper/data/bridge-completion.json',
      'milestones/146-initial-tree-and-paper/lean/PrefixAssoc146.lean',
      'milestones/146-initial-tree-and-paper/data/PrefixAssoc146-audit.json',
      'milestones/144-countfree-share18/lean/LratFast144.lean',
      'milestones/153-pair-conditioned-share17/replay/prepare_replay.py',
      'milestones/153-pair-conditioned-share17/replay/transport_replay.py',
      'milestones/155-share17-replay/scripts/emit_full_v2.py',
      'milestones/159-share18-proof-continuation/scripts/run_semantics.py',
      'milestones/159-share18-proof-continuation/scripts/run_semantics_final.py']
    for name,origin in [('native_resources.py','milestones/155-share17-replay/scripts/native_resources.py'),
                        ('native_guard.py','milestones/157-weaker-share-floor/scripts/native_guard.py')]:
        source=R/origin;target=H/'scripts'/name
        if target.exists():assert target.read_bytes()==source.read_bytes()
        else:target.write_bytes(source.read_bytes())
        inputs.append(origin)
    input_pins={p:sha(R/p) for p in inputs}
    assert input_pins['milestones/144-countfree-share18/certificates/share144.lrat']=='74ab1a039d1476e03cfed0500f95f5f27d5935589942c227ff39315d5bd139d9'
    assert input_pins['milestones/144-countfree-share18/experiments/lean/LiteralProbe144.lean']=='b411f3aa2e18f05e4f802fcdd03af0eef27a9f5493592022b0677d6b7aa519e8'
    # Pin accepted prefix dependencies without changing the historical receipts.
    for rel in ['milestones/144-countfree-share18/experiments/data/LiteralProbe144-audit.json',
                'milestones/146-initial-tree-and-paper/data/PrefixAssoc146-audit.json']:
        receipt=json.loads((R/rel).read_text())
        assert receipt['status']=='PASS' and receipt['exit_code']==0
        for field,digest_field in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
            path=Path(receipt[field]);assert sha(path)==receipt[digest_field]
            input_pins[str(path)]=receipt[digest_field]
    scripts=['prefix_transport.py','run_prefix.py','prepare_sources.py','native_resources.py','native_guard.py']
    for name in scripts:ast.parse((H/'scripts'/name).read_text(encoding='utf-8'),filename=name)
    plan=dict(status='SOURCE_PREPARED_NOT_EXECUTED',
        source_pins={(H/'scripts'/n).relative_to(R).as_posix():sha(H/'scripts'/n) for n in scripts},
        input_pins=input_pins,
        prefix=dict(deductions=1055,references=6006,compare_every_packed_row=True),
        allocation=dict(whole_proof_metadata_scan=True,deductions=145215,references=14710881,
                        slots=14114,height=14,word_width=14,offset=8192),
        scope='Two streaming allocation passes; unit propagation only for accepted1055-row prefix; materialized checkpoint and three uncompiled Lean sources.',
        limits=dict(owned_private_bytes=1024**3,startup_free_bytes=1536*1024**2,
                    runtime_free_bytes=768*1024**2,seconds=180,source_bytes=8*1024**2),
        gate='Both159 semantic batches terminal with no batch locks or active modules; require final progress terminal when present and pin both progress hashes at launch; no Lean or graph process; one160 transport worker.',
        copied_helpers_byte_identical=True,Python_syntax_checked=True,
        native_snapshot_run=False,proof_or_allocator_executed=False,Lean_invoked=False,
        full_replay_sources_generated=False,new_global_bound=False)
    target=H/'data/source-plan.json';payload=(json.dumps(plan,indent=2)+'\n').encode()
    if target.exists():assert target.read_bytes()==payload,'Existing source plan must remain unchanged'
    else:target.write_bytes(payload)
    print(json.dumps(dict(status=plan['status'],source_plan_sha256=sha(target),input_pins=len(input_pins),scripts=len(scripts))))


if __name__=='__main__':main()
