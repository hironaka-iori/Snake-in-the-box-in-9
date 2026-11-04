"""Bind the emitted checkpoint to accepted initial-tree and prefix receipts."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def write(p,b):
    if isinstance(b,str):b=b.encode('utf-8')
    p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)
run=H/'data/prefix1055';native=read(run/'prefix-transport.json')
assert native['status']=='PASS_EXACT_ACCEPTED_PREFIX_TRANSPORT_CHECKPOINT_SOURCE_ONLY'
assert native['prefix_deductions']==native['packed_rows_equal']==1055 and native['prefix_references']==6006
assert native['live_checkpoint_entries_match_prefix_database'] and native['dead_entries_replaced_by_tautologies']
assert not native['Lean_checkpoint_checked']
sourceplan=read(H/'data/source-plan.json');pins={}
def pin(p,d=None):
    p=Path(p);p=p if p.is_absolute() else R/p;actual=sha(p)
    assert d is None or actual==d,str(p);pins[str(p)]=actual
for mapping in [sourceplan['source_pins'],sourceplan['input_pins']]:
    for p,d in mapping.items():pin(p,d)
for p in [run/'prefix-transport.json',run/'run-status.json',H/'data/source-plan.json']:pin(p)
pin(run/native['checkpoint_file'],native['checkpoint_sha256'])
sources={}
for item in native['artifacts']:
    src=run/item['path'];pin(src,item['sha256']);write(H/'lean'/(item['module']+'.lean'),src.read_bytes());sources[item['module']]=item['sha256']
receipts=[('milestones/146-initial-tree-and-paper','PrefixAssoc146'),
          ('milestones/146-initial-tree-and-paper','AssemblyAssoc146'),
          ('milestones/146-initial-tree-and-paper','RawChunksAssoc146'),
          ('milestones/144-countfree-share18/experiments','LiteralData144'),
          ('milestones/144-countfree-share18/experiments','LiteralProbe144')]
for directory,module in receipts:
    base=R/directory;rp=base/'data'/(module+'-audit.json');q=read(rp)
    assert q['status']=='PASS' and q['exit_code']==0
    pin(rp);pin(q['source'],q['source_sha256']);pin(q['object'],q['olean_sha256']);pin(q['log'],q['log_sha256'])
    for p,d in q['dependencies'].items():pin(p,d)
extpath=R/'milestones/155-share17-replay/data/final-composition-plan.json';ext=read(extpath);pin(extpath)
for p,d in ext['external_pins'].items():pin(p,d)
P=R/'milestones/159-share18-proof-continuation'
checker=(P/'scripts/check_semantic.py').read_text().replace('data/semantic-execution.json','data/checkpoint-execution.json')
driver=(P/'scripts/run_semantics.py').read_text().replace('data/semantic-execution.json','data/checkpoint-execution.json').replace('semantic-batch.lock','checkpoint-batch.lock').replace("'semantic-batch-'","'checkpoint-batch-'").replace('semantic-progress.json','checkpoint-progress.json').replace('scripts/check_semantic.py','scripts/check_checkpoint.py').replace('PASS_COMPLETE_SEMANTIC_MODULES','PASS_COMPLETE_CHECKPOINT_MODULES').replace('PASS_BOUNDED_SEMANTIC_PREFIX','PASS_BOUNDED_CHECKPOINT_PREFIX')
write(H/'scripts/check_checkpoint.py',checker);write(H/'scripts/run_checkpoint.py',driver)
for p in [P/'scripts/check_semantic.py',P/'scripts/run_semantics.py',H/'scripts/native_resources.py']:pin(p)
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin');pin(B/'lean.exe')
search=[H/'build',P/'build',R/'milestones/147-countfree-clause-semantics/build',R/'milestones/146-initial-tree-and-paper/build-independent',R/'milestones/145-countfree-012301/build-independent',R/'milestones/144-countfree-share18/experiments/build',R/'milestones/144-countfree-share18/build-base']
plan=dict(status='PREPARED_CHECKPOINT_KERNEL_CHECK_PENDING',module_order=native['module_order'],new_module_order=native['module_order'],
    source_sha256=sources,input_pins=pins,lean_bin=str(B),search_paths=list(map(str,search))+ext['external_library_search_paths'],
    checker_sha256=sha(H/'scripts/check_checkpoint.py'),driver_sha256=sha(H/'scripts/run_checkpoint.py'),
    scope='The retained-entry checkpoint after the accepted1055-deduction prefix; no additional replay deductions or final contradiction.')
write(H/'data/checkpoint-execution.json',json.dumps(plan,indent=2)+'\n');write(H/'.gitattributes','* -text\n')
print('PREPARED_THREE_CHECKPOINT_MODULES')
