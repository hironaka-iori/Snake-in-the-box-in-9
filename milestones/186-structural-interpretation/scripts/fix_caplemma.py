from pathlib import Path
import sys
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation');sys.path.insert(0,str(H/'scripts'))
from replan import replan,read
p=H/'lean/Share186/CapLemmas.lean';s=p.read_text();s=s.replace('have hu := Bool.and_eq_true.mp (List.all_eq_true.mp h a ha)','have hu := List.all_eq_true.mp h a ha\n  simp only [posU,Bool.and_eq_true] at hu')
p.write_text(s,encoding='utf-8',newline='\n');replan(read(H/'data/current-order.json'))
(H/'scripts/fix_caplemma.py').write_bytes(Path(__file__).read_bytes())
