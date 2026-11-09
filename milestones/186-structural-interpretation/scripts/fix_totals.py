from pathlib import Path
import sys
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation');sys.path.insert(0,str(H/'scripts'));from replan import replan,read
p=H/'lean/Share186/Totals.lean';s=p.read_text();assert 'conv_lhs => rw [tots_rows]' in s
p.write_text(s.replace('conv_lhs => rw [tots_rows]','rw [tots_rows]'),encoding='utf-8',newline='\n');replan(read(H/'data/current-order.json'))
(H/'scripts/fix_totals.py').write_bytes(Path(__file__).read_bytes())
