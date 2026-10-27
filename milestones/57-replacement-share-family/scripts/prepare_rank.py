"""Reuse the checked rank proof with this round's exact graph data."""
from pathlib import Path
import json,re,runpy
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
(HERE/'logs').mkdir(exist_ok=True)
selection=json.loads((HERE/'data/selected-candidate.json').read_text())['selected']
assert selection==[1]
source=(ROOT/'milestones/55-critical-share-family/scripts/prepare_cover_lean.py').read_text()
source=source.replace("cover=json.loads((HERE/'data/cycle-cover.json').read_text())['share_only']", "cover=json.loads((HERE/'data/selected-candidate.json').read_text())")
source=source.replace('CriticalShareCover55','CriticalShareCover57')
source=re.sub(r'\b6\b','1',source).replace('83-edge','48-edge')
generated=HERE/'scripts/generate_rank.py';generated.write_text(source,encoding='utf-8')
runpy.run_path(str(generated),run_name='__main__')
check=(ROOT/'milestones/56-packing-limit-and-revision/scripts/check_lean.py').read_text()
check=check.replace("[HERE/'lean/PackingLimit.lean',HERE/'lean/PaperArithmetic.lean']","sorted((HERE/'lean').glob('*.lean'))")
(HERE/'scripts/check_lean.py').write_text(check,encoding='utf-8')
