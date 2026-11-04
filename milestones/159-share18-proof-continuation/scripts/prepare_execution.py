"""Bind unchanged144 semantics to checked147 foundations and one native checker."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
OLD=R/'milestones/144-countfree-share18';P=R/'milestones/147-countfree-clause-semantics'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def write(p,b):
    if isinstance(b,str):b=b.encode('utf-8')
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)
manifest=H/'data/semantic-source-plan.json';m=read(manifest)
order=['LocalWindowCnf.ShareWindow144','Share144.Data','Share144.Structure']+['Share144.Shard'+str(i).zfill(2) for i in range(104)]+['Share144.Compose','Share144.Sat']
assert len(order)==109 and m['module_order']==order
pins={str(manifest):sha(manifest)};sources={}
def pin(p,expected=None):
    p=Path(p);p=p if p.is_absolute() else R/p;d=sha(p)
    assert expected is None or d==expected,str(p)
    assert str(p) not in pins or pins[str(p)]==d
    pins[str(p)]=d
for name in order:
    rel=Path(name.replace('.','/')+'.lean');old=OLD/'lean'/rel;src=H/'lean'/rel
    assert src.read_bytes()==old.read_bytes(),name
    pin(old);sources[name]=sha(src)
foundations=['LocalWindowModel','LocalWindowTags','LocalWindowTagsPacked','LocalWindowShareModel','LocalWindowTagsShare','LocalWindowTagsSharePacked']
for name in foundations:
    rp=P/'data'/(name+'-audit.json');q=read(rp)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
    pin(rp);pin(q['source'],q['source_sha256']);pin(q['object'],q['olean_sha256']);pin(q['log'],q['log_sha256'])
    for p,d in q['dependencies'].items():pin(p,d)
cnf=OLD/'data/LocalWindowCnf.ShareWindow144-audit.json';q=read(cnf)
assert q['status']=='PASS_WINDOW_REPLAY_MODULE' and q['exit_code']==0
pin(cnf);pin(OLD/'lean/LocalWindowCnf/ShareWindow144.lean',q['source_sha256'])
obj=OLD/'build-base/LocalWindowCnf/ShareWindow144.olean';pin(obj,q['olean_sha256'])
cnf_log=Path(q['log']);cnf_log=cnf_log if cnf_log.is_absolute() else OLD/cnf_log
pin(cnf_log,q['log_sha256'])
for p,d in q['dependencies'].items():pin(p,d)
target=H/'build/LocalWindowCnf/ShareWindow144.olean';target.parent.mkdir(parents=True,exist_ok=True);write(target,obj.read_bytes());pin(target,q['olean_sha256'])
helper=R/'milestones/155-share17-replay/scripts/native_resources.py'
write(H/'scripts/native_resources.py',helper.read_bytes());pin(helper);pin(H/'scripts/native_resources.py')
B=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
pin(B/'lean.exe')
mathlib=B.parent.parent/'mathlib'
for p in [mathlib/'lean-toolchain',mathlib/'lake-manifest.json']:pin(p)
plan=dict(status='PREPARED_SEMANTIC_CONTINUATION_UNCHECKED',module_order=order,new_module_order=order[1:],
    reused_CNF_receipt=str(cnf),reused_CNF_receipt_sha256=sha(cnf),source_sha256=sources,input_pins=pins,
    lean_bin=str(B),search_paths=[str(H/'build'),str(P/'build'),str(mathlib/'.lake/build/lib/lean')],
    checker_sha256=sha(H/'scripts/check_semantic.py'),driver_sha256=sha(H/'scripts/run_semantics.py'),
    scope='Universal012034 share18 CNF interpretation only. Complete contradiction replay and actual-snake transfer remain separate.',
    resource_limits=dict(startup_free_bytes=2*1024**3,runtime_free_bytes=768*1024**2,owned_private_bytes=3*1024**3))
write(H/'data/semantic-execution.json',json.dumps(plan,indent=2)+'\n');write(H/'.gitattributes','* -text\n')
print('PREPARED_SEMANTIC_CONTINUATION',len(order),'modules,1reused,108pending')
