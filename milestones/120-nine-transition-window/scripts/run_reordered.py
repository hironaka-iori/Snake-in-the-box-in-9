"""Run exactly the saved small proof plan; the checker gates every compiler launch."""
from pathlib import Path
import json,subprocess,sys
H=Path(__file__).resolve().parents[1]
p=json.loads((H/'data/grouped-reordered-plan.json').read_text())
r=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_isolated.py'),*p['modules']])
sys.exit(r.returncode)
