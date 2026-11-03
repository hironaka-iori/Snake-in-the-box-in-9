"""Prepare one bounded refinement of the independently replayed native core."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
source=ROOT/'milestones/115-total-count-certificate/scripts/refine.py'
text=source.read_text(encoding='utf-8')
text=text.replace("OLD=ROOT/'milestones/114-total-count-pressure'","OLD=HERE")
text=text.replace('012310-total18','012034-middle5-outer15').replace('snake115-','snake117-')
target=HERE/'scripts/refine.py';assert not target.exists();target.write_text(text,encoding='utf-8')
(HERE/'data/refinement-source.json').write_text(json.dumps(dict(source=source.relative_to(ROOT).as_posix(),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),changes='Use this milestone and the new count-sum certificate; preserve the original bounded refinement and all attempts.'),indent=2)+'\n',encoding='utf-8')
