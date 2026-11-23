"""Compare the dynamic-fold length-190 outputs with the record archive sequences under Q9 symmetries."""
import csv
import gzip
import io
import json
import sys
import zipfile
from pathlib import Path
root=Path(__file__).resolve().parent
def canon(word):
    def norm(seq):
        seen={}
        return ''.join(str(seen.setdefault(x,len(seen))) for x in seq)
    return min(norm(word),norm(word[::-1]))
if len(sys.argv)>1:
    with zipfile.ZipFile(sys.argv[1]) as f:
        seedlist={r['actions'] for r in csv.DictReader(io.TextIOWrapper(f.open('record_snakes.csv'))) if r['n']=='10'}
        local={' '.join(l.split()[1:]) for l in (root/'external_q10.steps').read_text().splitlines()}
        assert local==seedlist
        bank={canon(''.join(r['actions'].split())) for r in csv.DictReader(io.TextIOWrapper(f.open('snakes_dim9_190.csv')))}
        assert bank==set(gzip.decompress((root/'reference190.words.gz').read_bytes()).decode().splitlines())
else:
    bank=set(gzip.decompress((root/'reference190.words.gz').read_bytes()).decode().splitlines())
old191=(root.parent/'q9_reordered_segments_20261120/reference191.words').read_text().split()
trims={canon(t) for w in old191 for t in [w[1:],w[:-1]]}
found=set();report={}
for name in ['alias','delete']:
    f=(root/(name+'_catalogue.log')).read_text().splitlines()
    assert f[-1].startswith('DONE')
    words={line.split()[1] for line in f if line.startswith('CLASS190')}
    for word in words:
        assert len(word)==190 and word==canon(word)
        p=[0]
        for c in word:p.append(p[-1]^(1<<int(c)))
        assert len(set(p))==191 and all(((p[i]^v).bit_count()==1)==(i+1==j) for j,v in enumerate(p) for i in range(j))
    found|=words
    report[name]={'classes':len(words),'in_public190':len(words&bank),'in_ref191_trim':len(words&trims)}
report['combined']={'classes':len(found),'in_public190':len(found&bank),'in_ref191_trim':len(found&trims),'public_reference_classes':len(bank),'new_classes':sorted(found-bank-trims)}
print(json.dumps(report,indent=2))
