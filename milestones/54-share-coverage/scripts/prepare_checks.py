"""Use the existing pinned Lean check environment for the five-window budget."""
from pathlib import Path
HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
source = (ROOT/'milestones/53-shares-on-sat-obstruction/scripts/check_lean.py').read_text()
source = source.replace('FiniteBlockBudget', 'FiveWindowBudget')
(HERE/'scripts/check_lean.py').write_text(source)
(HERE/'scripts/replay.py').write_text((ROOT/'milestones/53-shares-on-sat-obstruction/scripts/replay.py').read_text())
(HERE/'logs').mkdir(exist_ok=True)
