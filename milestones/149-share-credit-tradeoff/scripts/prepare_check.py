"""Pin the small arithmetic check and reuse the guarded serial execution procedure."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/148-actual-snake-share-transfer'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=read(P/'data/transfer-plan-v4.json')
external=old['external_library_search_paths']
mathlib=Path(external[0]).parents[3]
pins={}
for name in ['Linarith','NormNum']:
    for path in [mathlib/f'Mathlib/Tactic/{name}.lean',Path(external[0])/f'Mathlib/Tactic/{name}.olean']:
        assert path.is_file(),path;pins[str(path)]=sha(path)
for name in ['lean-toolchain','lake-manifest.json']:
    path=mathlib/name;pins[str(path)]=sha(path)
module='CreditTradeoff149';source=H/f'lean/{module}.lean'
plan=dict(status='PREPARED_ARITHMETIC_OBSTRUCTION',module_order=[module],framework_modules=[module],
    artifacts=[dict(module=module,path=source.relative_to(H).as_posix(),sha256=sha(source))],
    inherited_modules={},external_library_search_paths=external,external_pins=pins)
path=H/'data/check-plan.json';assert not path.exists();path.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
text=(P/'scripts/check_module_v4.py').read_text(encoding='utf-8')
text=text.replace('transfer-plan-v4.json','check-plan.json')
oldscope='Lean4.19 and Mathlib libraries are trusted; compiler, direct library objects, selected entry sources and library manifest are pinned. Thirteen project helpers are freshly checked; one historical automaton data object is reused with exact source/object/log and direct dependency matching.147 semantics are reused with their exact accepted receipts.'
assert text.count(oldscope)==1
text=text.replace(oldscope,'Lean4.19 and Mathlib libraries are trusted; compiler, direct library objects, entry sources and library manifest are pinned. No project helper or local refutation is imported. This module proves arithmetic implications from explicit cycle and path inequalities.')
checker=H/'scripts/check_module.py';assert not checker.exists();checker.write_text(text,encoding='utf-8',newline='\n')
text=(P/'scripts/serialize_transfer_v4.py').read_text(encoding='utf-8')
text=text.replace('148','149').replace('serialization-v4-','serialization-').replace('transfer-v4-batch.lock','arithmetic-batch.lock')
needle="str(H/'scripts/run_transfer_v4.py')"
assert text.count(needle)==1;text=text.replace(needle,"str(H/'scripts/check_module.py'),'CreditTradeoff149'")
controller=H/'scripts/serialize_check.py';assert not controller.exists();controller.write_text(text,encoding='utf-8',newline='\n')
record=dict(status='PREPARED_NOT_CHECKED',source_sha256=sha(source),plan_sha256=sha(path),checker_sha256=sha(checker),controller_sha256=sha(controller),
    reused_sources={str(P/'scripts/check_module_v4.py'):sha(P/'scripts/check_module_v4.py'),str(P/'scripts/serialize_transfer_v4.py'):sha(P/'scripts/serialize_transfer_v4.py')})
(H/'data/check-preparation.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
