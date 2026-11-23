from pathlib import Path
from collections import Counter
import json
D=Path(__file__).resolve().parent
def read(n):return list(map(json.loads,(D/n).read_text().splitlines()))
def tally(rows,k):return dict(Counter(r[k] for r in rows))
def main():
    first=[r for f in D.glob('run*.jsonl') for r in map(json.loads,f.read_text().splitlines())];assert len(first)==2816
    narrow={r[0]:r[1] for r in first};narrow.update({r[0]:r[1] for r in read('deep.jsonl')})
    wide={r[0]:r[2] for r in read('wide.jsonl')};wide.update({r[0]:r[1] for r in read('sector_retry.jsonl')})
    small=read('small.jsonl');mosaic=read('mosaic.jsonl');second=read('second.jsonl');core=read('core_moves.jsonl')
    mosaic_status={r[0]:r[1] for r in mosaic}
    for lab,table in (('broad',wide),('mosaic',mosaic_status)):
        for file in sorted(D.glob(f'last-{lab}-*.jsonl')):
            table.update({r[0]:r[1] for r in map(json.loads,file.read_text().splitlines())})
    summary=dict(primary_updated=Counter(narrow.values()),small=tally(small,2),all_birth_tuples=Counter(wide.values()),mosaic=Counter(mosaic_status.values()),generation_two=tally(second,1),degree_core_directed=tally(core,1))
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
