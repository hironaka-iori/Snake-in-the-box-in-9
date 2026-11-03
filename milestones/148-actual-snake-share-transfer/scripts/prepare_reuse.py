"""Reuse the pinned historical data object after the bounded rebuild failed."""
from pathlib import Path
import hashlib,json,shutil
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
oldplan=H/'data/transfer-plan.json';plan=read(oldplan)
supportpath=R/'milestones/73-countfree-share-catalogue/adapter/data/support.json';support=read(supportpath)
record=next(x for x in support['modules'] if x['module']=='WindowAutomatonData')
source=H/'lean/WindowAutomatonData.lean';oldobject=Path(record['olean_path']);oldlog=Path(record['inherited_log_path'])
assert sha(source)==record['source_sha256'] and sha(oldobject)==record['olean_sha256'] and sha(oldlog)==record['inherited_log_sha256']
defs=read(H/'data/WindowAutomatonDefs-audit.json')
olddefs=next(x for x in support['modules'] if x['module']=='WindowAutomatonDefs')
assert defs['status']=='PASS' and sha(defs['object'])==defs['olean_sha256']==olddefs['olean_sha256']
assert sha(defs['source'])==defs['source_sha256']==olddefs['source_sha256']
historical=R/'milestones/73-countfree-share-catalogue/adapter/logs/build-record.json'
h=read(historical)[0];assert h['module']=='CanonicalShareAdapter' and h['exit_code']==0 and h['support_record_sha256']==sha(supportpath)
obj=H/'build/WindowAutomatonData.olean';assert not obj.exists();shutil.copyfile(oldobject,obj);assert sha(obj)==record['olean_sha256']
reused=dict(status='PASS_PINNED_HISTORICAL_DATA_OBJECT_REUSE',module='WindowAutomatonData',
    source=str(source),source_sha256=sha(source),object=str(obj),object_sha256=sha(obj),
    original_object=str(oldobject),original_log=str(oldlog),fresh_compilation=False,
    dependency_defs_source_and_object_identical=True,
    source_files_sha256={str(p):sha(p) for p in [Path(__file__),source,obj,oldobject,oldlog,supportpath,historical,H/'data/WindowAutomatonDefs-audit.json',Path(defs['source']),Path(defs['object'])]},
    limitation='Reuses the source/object/log combination recorded by the successful historical adapter build. The attempted fresh data rebuild exceeded3GiB; no fresh data-module compilation is claimed.')
rp=H/'data/reused-data-object.json';assert not rp.exists();rp.write_text(json.dumps(reused,indent=2)+'\n',encoding='utf-8',newline='\n')
probe=H/'lean/DataDependencyAudit148.lean';assert not probe.exists()
probe.write_text('import WindowAutomatonData\n#print axioms Snake9.WindowAutomaton.step_table\n#print axioms Snake9.WindowAutomaton.pot_le\n',encoding='utf-8',newline='\n')
plan.update(status='PREPARED_TRANSFER_WITH_PINNED_DATA_OBJECT',
    module_order=['DataDependencyAudit148' if m=='WindowAutomatonData' else m for m in plan['module_order']],
    framework_modules=['DataDependencyAudit148' if m=='WindowAutomatonData' else m for m in plan['framework_modules']],
    inherited_modules={'WindowAutomatonData':dict(receipt=str(rp),receipt_sha256=sha(rp))},
    selected_scope='Fresh checks of thirteen additional project helpers, two conditional wrappers and a data dependency axiom audit. The single historical data object is reused after exact source/object/log and direct dependency matching.147 semantic models and external libraries retain their stated trust boundaries.',
    prior_plan_sha256=sha(oldplan),reuse_preparer_sha256=sha(__file__))
plan['artifacts'].append(dict(module='DataDependencyAudit148',path=probe.relative_to(H).as_posix(),sha256=sha(probe)))
v2=H/'data/transfer-plan-v2.json';assert not v2.exists();v2.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n')
def save(name,s):
    p=H/'scripts'/name;assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
s=(H/'scripts/check_module.py').read_text(encoding='utf-8').replace('data/transfer-plan.json','data/transfer-plan-v2.json')
needle="    if name=='Std' or name.startswith('Mathlib.'):continue\n"
assert s.count(needle)==1
extra="""    if name in plan['inherited_modules']:
        item=plan['inherited_modules'][name];rp=Path(item['receipt'])
        assert sha(rp)==item['receipt_sha256'];q=read(rp)
        assert q['status']=='PASS_PINNED_HISTORICAL_DATA_OBJECT_REUSE' and not q['fresh_compilation']
        deps[str(rp)]=sha(rp)
        for p,d in q['source_files_sha256'].items():
            assert sha(p)==d,p;deps[p]=d
        continue
"""
s=s.replace(needle,needle+extra)
s=s.replace('Additional project helpers are freshly checked here;147 project semantics are reused with their exact accepted receipts.',
    'Thirteen project helpers are freshly checked; one historical automaton data object is reused with exact source/object/log and direct dependency matching.147 semantics are reused with their exact accepted receipts.')
save('check_module_v2.py',s)
s=(H/'scripts/run_transfer.py').read_text(encoding='utf-8').replace('transfer-plan.json','transfer-plan-v2.json')
s=s.replace('PREPARED_FRESH_PROJECT_TRANSFER_CHAIN_UNCHECKED','PREPARED_TRANSFER_WITH_PINNED_DATA_OBJECT')
s=s.replace('check_module.py','check_module_v2.py').replace('transfer-batch','transfer-v2-batch').replace('transfer-progress','transfer-v2-progress').replace('transfer-launch','transfer-v2-launch')
save('run_transfer_v2.py',s)
s=(H/'scripts/serialize_transfer.py').read_text(encoding='utf-8').replace('scripts/run_transfer.py','scripts/run_transfer_v2.py').replace('data/transfer-batch.lock','data/transfer-v2-batch.lock').replace("'serialization-'","'serialization-v2-'")
save('serialize_transfer_v2.py',s)
print(json.dumps(dict(status=plan['status'],checked_modules_planned=len(plan['module_order']),inherited_data_object_sha256=sha(obj))))
