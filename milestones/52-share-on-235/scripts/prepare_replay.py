"""Adapt the checked share exporter to this larger core; all generated code is replayed."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];PRIOR=HERE.parent/'51-exact-bucket-pressure'
s=(PRIOR/'scripts/export_share.py').read_text()
s=s.replace("NAME='share3_47';MOD='SharePressure513'","NAME='supported0_95';MOD='SharePressure520'")
s=s.replace('def cap : Nat := 47','def cap : Nat := 95').replace('48 ≤ shareSum','96 ≤ shareSum').replace('≤ 47 by omega','≤ 95 by omega').replace('off=5000','off=6000')
(HERE/'scripts/export_share.py').write_text(s)
s=(PRIOR/'scripts/lrat_share.py').read_text().replace('(2400, 3000, 4000, 5000)','(2400, 3000, 4000, 5000, 6000)').replace("5000: 'O5k'","5000: 'O5k', 6000: 'O6k'")
(HERE/'scripts/lrat_share.py').write_text(s)
for name in ['LratCheckO5k','LratFastO5k14','LratFastO5k15']:
 s=(PRIOR/f'lean/{name}.lean').read_text().replace('O5k','O6k').replace('5000','6000')
 (HERE/f'lean/{name.replace("O5k","O6k")}.lean').write_text(s)
s=(PRIOR/'scripts/replay.py').read_text().replace("for prior,tag in [","for prior,tag in [('51-exact-bucket-pressure','latest'),")
if not (HERE/'scripts/replay.py').exists():
 (HERE/'scripts/replay.py').write_text(s)
