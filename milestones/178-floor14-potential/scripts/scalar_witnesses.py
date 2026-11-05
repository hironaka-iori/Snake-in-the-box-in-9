"""Reconstruct each witness edge directly from the original scalar source rows."""
from pathlib import Path
import json,ast,struct,hashlib
H=Path(__file__).resolve().parents[1];R=H.parents[1]
cols=R/'milestones/176-boundary-retuning/data/graph-final/source-columns';files={}
for k in ['U','V','weight','direction','count_code']:
    f=(cols/(k+'.npy')).open('rb');assert f.read(6)==b'\x93NUMPY';version=f.read(2)
    size=struct.unpack('<H' if version[0]==1 else '<I',f.read(2 if version[0]==1 else 4))[0]
    hdr=ast.literal_eval(f.read(size).decode());assert hdr['descr'] in ['<i4','<u4']
    files[k]=(f,f.tell(),'<i' if hdr['descr']=='<i4' else '<I')
def val(k,i):
    f,offset,fmt=files[k];f.seek(offset+4*i);return struct.unpack(fmt,f.read(4))[0]
def read(p):return json.loads((R/p).read_text(encoding='utf-8-sig'))
def canon(w):
    d={};return ''.join(str(d.setdefault(x,len(d))) for x in w)
def shape(w):return min(canon(w),canon(w[::-1]))
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
rules=read('milestones/120-nine-transition-window/data/full-rules.json')
removed=set(read('milestones/144-countfree-share18/data/share18-impact/removed-indices.json'))
floors={'012031':16,'012032':16,'012034':14,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}
pending={'012034','012301','012340','012345'}
def row(edge,joint):
    assert edge not in removed
    word=ds[val('direction',edge)];suffix=word[-6:];sh=shape(suffix);code=val('count_code',edge)
    c=[code//6**j%6+1 for j in range(5,-1,-1)];five=c[1:];aligned=five if canon(suffix)==sh else five[::-1]
    credit=0
    for rule in rules:
        if shape(rule['directions'])!=sh:continue
        if all(lo<=x and (21 if x==6 else x)<=hi for x,(lo,hi) in zip(aligned,rule['bounds'])):
            credit=max(credit,24*max(0,rule['lower']-sum(aligned[i] for i in rule['positions'])))
    if sh=='012032':credit=max(credit,24*max(0,9-c[2]-c[4]))
    if shape(word[2:])==shape([0,1,2,3,1,0,4]) and c[0]<6:credit=max(credit,24*max(0,25-sum(c)))
    floor=14 if joint and sh in pending else floors[sh]
    for reverse in [False,True]:
        if canon(suffix[::-1] if reverse else suffix)!='012032':continue
        x=five[::-1] if reverse else five
        if all(lo<=v<=hi for v,lo,hi in zip(x,[4,0,4,0,3],[4,4,4,5,3])):floor=max(floor,17)
    return {'source_edge':edge,'u':val('U',edge),'v':val('V',edge),'weight':max(val('weight',edge),120*c[-1]+floor)+credit,'directions':word,'shape':sh,'counts':c,'extra_credit':credit}
j=json.loads((H/'data/witnesses.json').read_text());records=[]
for witness in j['range_witnesses']:
    rows=[row(x['source_edge'],witness['profile']!='fixed14') for x in witness['walk']]
    assert all(all(x[k]==y[k] for k in ['source_edge','u','v','weight']) for x,y in zip(rows,witness['walk']))
    assert all(x['v']==y['u'] for x,y in zip(rows,rows[1:]))
    records.append({'profile':witness['profile'],'walk':rows,'length':len(rows),'weight':sum(x['weight'] for x in rows)})
for joint in [False,True]:
    rows=[row(x['source_edge'],joint) for x in j['cycle']]
    assert all(all(x[k]==y[k] for k in ['source_edge','u','v','weight']) for x,y in zip(rows,j['cycle']))
    assert rows[0]['u']==rows[-1]['v'] and all(x['v']==y['u'] for x,y in zip(rows,rows[1:]))
    assert len(rows)==9 and sum(x['weight'] for x in rows)==4448
    records.append({'profile':'joint14' if joint else 'fixed14','cycle':rows,'length':9,'weight':4448})
for f,_,_ in files.values():f.close()
(H/'data/scalar-witnesses.json').write_text(json.dumps({'status':'PASS_SCALAR_SOURCE_RECONSTRUCTION','witnesses_sha256':hashlib.sha256((H/'data/witnesses.json').read_bytes()).hexdigest(),'records':records},indent=2)+'\n')
print('PASS scalar reconstruction:',len(records),'walk/cycle certificates')
