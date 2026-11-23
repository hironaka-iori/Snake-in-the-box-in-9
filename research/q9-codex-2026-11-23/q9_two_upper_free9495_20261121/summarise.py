import hashlib,gzip,json
from pathlib import Path
from collections import Counter
from banks import D
rows=lambda glob:[json.loads(l) for f in D.glob(glob) for l in f.read_text().splitlines()]
proof={(r['id'],r['c']) for r in rows('certified_*.jsonl') if r.get('drat_verified') and not r['cycles']};assert proof=={(i,c) for i in range(16) for c in (0,1)}
colors={};weights=json.loads((D/'integer_replay.json').read_text())['integer_checks']
for i,c,_ in weights:colors.setdefault(i,set()).add(c)
bound={i for i,cs in colors.items() if cs=={0,1}};assert bound=={0,3,16,50,100,1629,3050,4000,4681}
roots_closed={i for i,_ in proof}|bound;added=(D/'reroutes/verified.log').read_text().splitlines();assert len(added)==4
odds=rows('checked_odd.jsonl');assert len(odds)==11 and all(r['drat_verified'] for r in odds)
refs=json.loads((D/'references.json').read_text());exact=sorted(r['donor'] for r in odds if refs[str(r['donor'])][0]==190)
un=[r['id'] for r in rows('odd_*.jsonl') if r.get('target')==191 and r['answer'] is None]
c=Counter();cleaned=0
for f in sorted(D.glob('sat_*.drat.gz'))+sorted(D.glob('sat_*.cnf.gz')):
    raw=Path(str(f)[:-3])
    if raw.exists():
        with gzip.open(f,'rb') as a,raw.open('rb') as b:
            assert hashlib.file_digest(a,'sha256').digest()==hashlib.file_digest(b,'sha256').digest()
        raw.unlink();cleaned+=1
print(json.dumps(dict(complete_192_exclusions=len(roots_closed)+len(added)//2,integer_fully_closed=sorted(bound),exact190=exact,unresolved_191=sorted(un),lower189_upper190=[14,15],archived_proofs=len(list(D.rglob('*.drat.gz'))),verified_then_removed_duplicate_files=cleaned)))
