from pathlib import Path
import json,sys
D=Path(__file__).resolve().parent
stats=[list(map(int,s.split()[:4])) for s in (D/'beam.log').read_text().splitlines()]
rows={int(s.split()[0]):s for s in (D/'beam.in').read_text().splitlines()}
ids=[r[0] for r in sorted(stats,key=lambda r:-r[3]) if r[0]>=0][:64]
(D/'focused.in').write_text(''.join(rows[i]+'\n' for i in ids))
