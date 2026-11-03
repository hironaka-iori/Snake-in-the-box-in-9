"""Retain the exact snake definitions and omit the unrelated witness rebuild."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=H/'data/transfer-plan-v2.json';plan=read(prior)
source=H/'lean/Snake9.lean';raw=source.read_bytes();marker=b'-- BEGIN WITNESS'
assert raw.count(marker)==1
prefix=raw.split(marker,1)[0];new=prefix+b'end Snake9\n'
for row in plan['artifacts']:
    if row['module']=='Snake9':continue
    text=(H/row['path']).read_text(encoding='utf-8')
    assert not re.search(r'\b(witnessValues|witnessVertex|witness_distinct|witness_induced|lower_bound|optimality_of_no192)\b',text),row['module']
folder=H/'lean-core';folder.mkdir(exist_ok=True);dest=folder/'Snake9.lean';assert not dest.exists();dest.write_bytes(new)
row=next(x for x in plan['artifacts'] if x['module']=='Snake9')
row.update(path=dest.relative_to(H).as_posix(),sha256=sha(dest),prior_full_source=str(source),prior_full_source_sha256=sha(source),
    source_change='Exact prefix before BEGIN WITNESS retained, then namespace closed. The independent191-edge witness and optimality conditional are not used by the transfer chain.')
plan.update(status='PREPARED_TRANSFER_WITH_GENERIC_SNAKE_CORE',prior_v2_plan_sha256=sha(prior),core_preparer_sha256=sha(Path(__file__)),
    snake_definitions_preserved_byte_for_byte=True,unrelated_witness_rebuild_omitted=True)
target=H/'data/transfer-plan-v3.json';assert not target.exists();target.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8',newline='\n')
def save(name,s):
    p=H/'scripts'/name;assert not p.exists();p.write_text(s,encoding='utf-8',newline='\n')
s=(H/'scripts/check_module_v2.py').read_text(encoding='utf-8')
before="src=H/'lean'/(a.module.replace('.','/')+'.lean');source=src.read_text(encoding='utf-8')"
after="source_plan=read(H/'data/transfer-plan-v3.json')\nsrc=H/next(x['path'] for x in source_plan['artifacts'] if x['module']==a.module);source=src.read_text(encoding='utf-8')"
assert s.count(before)==1;s=s.replace(before,after).replace('data/transfer-plan-v2.json','data/transfer-plan-v3.json')
s=s.replace("str(H/'lean'),'-o'","str(src.parent),'-o'")
save('check_module_v3.py',s)
s=(H/'scripts/run_transfer_v2.py').read_text(encoding='utf-8').replace('transfer-plan-v2.json','transfer-plan-v3.json')
s=s.replace('PREPARED_TRANSFER_WITH_PINNED_DATA_OBJECT','PREPARED_TRANSFER_WITH_GENERIC_SNAKE_CORE')
s=s.replace('check_module_v2.py','check_module_v3.py').replace('transfer-v2-','transfer-v3-')
before="p=H/'lean'/(m.replace('.','/')+'.lean')";assert s.count(before)==2
s=s.replace(before,"p=H/next(x['path'] for x in plan['artifacts'] if x['module']==m)")
save('run_transfer_v3.py',s)
s=(H/'scripts/serialize_transfer_v2.py').read_text(encoding='utf-8').replace('run_transfer_v2.py','run_transfer_v3.py').replace('transfer-v2-batch','transfer-v3-batch').replace("'serialization-v2-'","'serialization-v3-'")
save('serialize_transfer_v3.py',s)
receipt=dict(status='PASS_EXACT_GENERIC_CORE_PREFIX_PRESERVATION',original_sha256=sha(source),core_sha256=sha(dest),
    prefix_bytes=len(prefix),unchanged_generic_definitions=True,omitted_witness_section_unused_by_other148_sources=True,
    original_witness_source_retained=True,no_new_definition=True,compile_pending=True)
(H/'data/core-source-review.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(receipt))
