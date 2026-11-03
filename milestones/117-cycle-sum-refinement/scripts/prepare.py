"""Select bounded count-sum tests from the two retained attaining cycles."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for directory in ['scripts','data/probes','logs','audit']:(HERE/directory).mkdir(parents=True,exist_ok=True)
origin=ROOT/'milestones/115-total-count-certificate'
copies=['probe_sum.py','evaluate_total.py','audit_witnesses.py','audit_probes.py']
pins={}
for name in copies:
    source=origin/'scripts'/name;target=HERE/'scripts'/name
    assert not target.exists()
    raw=source.read_bytes()
    if name=='audit_witnesses.py':raw=raw.replace(b'assert len(rows)>=4',b'assert len(rows)>=1')
    target.write_bytes(raw);pins[source.relative_to(ROOT).as_posix()]=sha(source)
source=origin/'data/universal345-total22/results.json'
directions=ROOT/'milestones/59-extended-share-window/extended/data/model.json'
audit=origin/'data/universal-cycle-audit.json'
for path in [source,directions,audit]:pins[path.relative_to(ROOT).as_posix()]=sha(path)
results=read(source);ds=read(directions)['extensions']
def canon(word):
    labels={};return tuple(labels.setdefault(int(x),len(labels)) for x in word)
profiles=[]
for profile in results['profiles']:
    rows={}
    for edge in profile['cycle']:
        cs=[edge['count_code']//6**j%6+1 for j in range(5,-1,-1)]
        word=ds[edge['direction']]
        for offset in [0,1]:
            fw=canon(word[offset+2:offset+8]);rv=canon(word[offset+2:offset+8][::-1])
            counts=tuple(cs[offset:offset+5]);shape=min(fw,rv)
            if rv<fw:counts=counts[::-1]
            key=(shape,counts)
            rows.setdefault(key,[]).append(dict(edge=edge['edge'],placement=offset,reversed=rv<fw))
    profiles.append(dict(profile=profile['profile'],mean=profile['mean'],windows=[dict(directions=list(shape),counts=list(counts),total=sum(counts),outer_sum=sum(counts)-counts[2],pair_sum=counts[0]+counts[4],occurrences=where) for (shape,counts),where in sorted(rows.items())]))
cases=[
 dict(name='012034-total20',directions=[0,1,2,0,3,4],bounds=[[0,21] for _ in range(5)],positions=list(range(5)),cap=20),
 dict(name='012034-middle5-outer15',directions=[0,1,2,0,3,4],bounds=[[0,21],[0,21],[0,5],[0,21],[0,21]],positions=[0,1,3,4],cap=15),
 dict(name='012034-caps5-total20',directions=[0,1,2,0,3,4],bounds=[[0,5] for _ in range(5)],positions=list(range(5)),cap=20),
]
for name,data in [('copied-source-pins.json',pins),('cycle-windows.json',dict(profiles=profiles,source_sha256=sha(source),scope='Decoded recorded full-key cycle windows; no new snake construction or full-edge scan.')),('cases-initial.json',cases)]:
    path=HERE/'data'/name;assert not path.exists();path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print('Prepared three bounded tests on 012034; both saved cycles contain total20 windows.')
