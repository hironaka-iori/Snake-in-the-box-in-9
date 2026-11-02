"""Pin exact graph direction tables and emit kernel-checkable Lean data."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources=[ROOT/'milestones/59-extended-share-window/extended/data/model.json',ROOT/'milestones/70-proof-supported-share-model/scripts/build.py',ROOT/'milestones/70-proof-supported-share-model/data/enriched-model.json']
model=json.loads(sources[0].read_text(encoding='utf-8-sig'))
states=model['direction_shapes'];edges=model['extensions']
assert len(states)==132 and len(edges)==505
def canon(ds):
    names=list(dict.fromkeys(ds));return [names.index(x) for x in ds]
source=[states.index(canon(d[:8])) for d in edges]
target=[states.index(canon(d[1:])) for d in edges]
for name in ['lean','data','logs','build']:(HERE/name).mkdir(parents=True,exist_ok=True)
fmt=lambda xs:'[\n  '+',\n  '.join(str(x) for x in xs)+'\n]'
text='''import WindowAutomatonLemmas
import Mathlib.Data.List.Nodup
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def shapes : List (List Nat) := '''+fmt(states)+'''
def extensions : List (List Nat) := '''+fmt(edges)+'''
def sourceIds : List Nat := '''+str(source)+'''
def targetIds : List Nat := '''+str(target)+'''
def sourceId (i : Nat) : Nat := shapes.idxOf (canon ((extensions.getD i []).take 8))
def targetId (i : Nat) : Nat := shapes.idxOf (canon ((extensions.getD i []).drop 1))
theorem shapes_length : shapes.length = 132 := by decide +kernel
#print axioms shapes_length
theorem extensions_length : extensions.length = 505 := by decide +kernel
#print axioms extensions_length
end Snake9.Direction77
'''
(HERE/'lean/DirectionTables.lean').write_text(text,encoding='utf-8',newline='\n')
(HERE/'data/tables.json').write_text(json.dumps(dict(shapes=states,extensions=edges,source_ids=source,target_ids=target),indent=2)+'\n',encoding='utf-8')
(HERE/'data/provenance.json').write_text(json.dumps(dict(status='PINNED_DATA_PENDING_LEAN',sources=[dict(path=p.relative_to(ROOT).as_posix(),sha256=sha(p)) for p in sources],lean_source_sha256=sha(HERE/'lean/DirectionTables.lean'),table_sha256=sha(HERE/'data/tables.json')),indent=2)+'\n',encoding='utf-8')
print('Pinned132 shapes,505 extensions and both endpoint maps.')
