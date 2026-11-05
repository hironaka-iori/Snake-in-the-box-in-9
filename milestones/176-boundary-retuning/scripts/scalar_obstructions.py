from pathlib import Path
import json,ast,struct
from fractions import Fraction
h=Path('milestones/176-boundary-retuning');root=Path('.');cols=Path('milestones/164-loss-corrected-potential/data/scaled-floor17/source-columns')
files={}
for key in ['U','V','weight','direction','count_code']:
 f=(cols/(key+'.npy')).open('rb');assert f.read(6)==b'\x93NUMPY';version=f.read(2);size=struct.unpack('<H' if version[0]==1 else '<I',f.read(2 if version[0]==1 else 4))[0];hdr=ast.literal_eval(f.read(size).decode());assert hdr['descr'] in ['<i4','<u4'];files[key]=(f,f.tell(),'<i' if hdr['descr']=='<i4' else '<I')
def val(k,i):
 f,offset,fmt=files[k];f.seek(offset+4*i);return struct.unpack(fmt,f.read(4))[0]
def canon(w):
 d={};return ''.join(str(d.setdefault(x,len(d))) for x in w)
def shape(w):return min(canon(w),canon(w[::-1]))
ds=json.loads(Path('milestones/59-extended-share-window/extended/data/model.json').read_text())['extensions']
rules=json.loads(Path('milestones/120-nine-transition-window/data/full-rules.json').read_text())
floors={'012031':16,'012032':16,'012034':17,'012301':16,'012304':16,'012310':12,'012314':16,'012340':16,'012345':16}
def row(edge,floor,joint=False):
 word=ds[val('direction',edge)];code=val('count_code',edge);counts=[code//6**j%6+1 for j in range(5,-1,-1)];suffix=word[-6:];sh=shape(suffix);five=counts[1:];aligned=five if canon(suffix)==sh else five[::-1];shared=0
 for rule in rules:
  if shape(rule['directions'])!=sh:continue
  if all(rule['bounds'][i][0]<=aligned[i] and (21 if aligned[i]==6 else aligned[i])<=rule['bounds'][i][1] for i in range(5)):
   shared=max(shared,24*max(0,rule['lower']-sum(aligned[j] for j in rule['positions'])))
 if sh=='012032':shared=max(shared,24*max(0,9-counts[2]-counts[4]))
 if shape(word[2:])==shape([0,1,2,3,1,0,4]) and counts[0]<6:shared=max(shared,24*max(0,25-sum(counts)))
 fl=floor if sh=='012034' else floors[sh]
 if joint and sh in ['012301','012340','012345']:fl-=1
 for reverse in [False,True]:
  if canon(suffix[::-1] if reverse else suffix)!='012032':continue
  a=five[::-1] if reverse else five
  if all(lo<=x<=hi for lo,x,hi in zip([4,0,4,0,3],a,[4,4,4,5,3])):fl=max(fl,17)
 return {'source_edge':edge,'u':val('U',edge),'v':val('V',edge),'shape':sh,'counts':counts,'weight':max(val('weight',edge),120*counts[-1]+fl)+shared}
walk=json.loads((h/'data/graph/floor12.json').read_text())['walk']
for x in walk:
 y=row(x['source_edge'],12);assert all(y[k]==x[k] for k in ['u','v','weight'])
cycle=walk[11:20];assert cycle[0]['u']==cycle[-1]['v']
nine=json.loads(Path('milestones/164-loss-corrected-potential/data/scaled-floor17/graph-reconstruction.json').read_text())['nine_walk']
out=[]
for f in range(10,18):
 c=[row(x['source_edge'],f) for x in cycle];w=[row(x['source_edge'],f) for x in nine];C=sum(x['weight'] for x in c);W=sum(x['weight'] for x in w);margin=(227-len(w))*Fraction(C,len(c))-(111600-W)
 out.append({'floor':f,'cycle_weight':C,'cycle_length':len(c),'walk_weight':W,'walk_length':len(w),'maximum_mean':str(Fraction(C,len(c))),'strict234_necessary_margin':str(margin),'cycle':c,'walk':w})
 print(f,'mean<=',Fraction(C,len(c)),'walk',W,'necessary margin',margin)
(h/'data/scalar-obstructions.json').write_text(json.dumps({'status':'PASS_SCALAR_SOURCE_ROW_RECONSTRUCTION','scope':'Same retained graph; obstruction to nonnegative-loss comparison at boundary24, not to stronger geometric or loss information.','rows':out},indent=2)+'\n',encoding='utf-8')
for f,_,_ in files.values():f.close()
