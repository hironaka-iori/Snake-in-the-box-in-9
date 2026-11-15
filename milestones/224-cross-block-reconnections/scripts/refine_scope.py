"""Clarify the two geometric hypotheses identified by the source review."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
changes={
'snake9_research.tex':('The first replacement has no crossing in coordinate 8 and the second\nhas one:', 'For a four-crossing result, the first replacement has no crossing in\ncoordinate 8 and the second has one:'),
'snake9_frontier_explanation.tex':('A simultaneous change of two such blocks can enable extension only if\neach new interior equals or is adjacent to some original interior vertex\nof the other block.', 'A simultaneous change of two such blocks with disjoint interiors can\nenable extension only if each new interior contains a vertex equal or\nadjacent to an original interior vertex of the other block.')}
records={}
for name,(old,new) in changes.items():
    before=(D/name).read_bytes();assert before==(R/'paper'/name).read_bytes();s=before.decode('utf-8');assert s.count(old)==1
    after=s.replace(old,new,1).encode('utf-8');(D/name).write_bytes(after);(R/'paper'/name).write_bytes(after)
    records[name]=dict(before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest())
(H/'data/scope-clarification.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
for prefix in ['frontier','main']:
    p=H/'data'/(prefix+'-compile-final.json');(H/'data'/(prefix+'-compile-initial.json')).write_bytes(p.read_bytes())
print('CLARIFIED_SCOPE; RECOMPILE_REQUIRED')
