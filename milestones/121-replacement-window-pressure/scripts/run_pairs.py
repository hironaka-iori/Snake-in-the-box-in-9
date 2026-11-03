from pathlib import Path
import json,subprocess,sys
H=Path(__file__).resolve().parents[1]
a=json.loads((H/'data/pair-plan.json').read_text())
raise SystemExit(subprocess.call([sys.executable,'-B','-X','utf8',str(H/'scripts/check_isolated.py'),*a['modules']]))
