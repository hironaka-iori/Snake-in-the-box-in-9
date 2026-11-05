from pathlib import Path
import json,hashlib,importlib.util,ast,struct
h=Path('milestones/176-boundary-retuning').resolve();r=h.parents[1]
spec=importlib.util.spec_from_file_location('scalar',h/'scripts/scalar_obstructions.py');scalar=importlib.util.module_from_spec(spec);spec.loader.exec_module(scalar)
meta=json.loads((r/'milestones/72-four-count-proof-closure/critical-current/data/source-proved-model.json').read_text());pins={}
for key in ['U','V','weight','direction','count_code']:
 p=r/'milestones/164-loss-corrected-potential/data/scaled-floor17/source-columns'/(key+'.npy')
 with p.open('rb') as f:
  assert f.read(6)==b'\x93NUMPY';version=f.read(2);size=struct.unpack('<H' if version[0]==1 else '<I',f.read(2 if version[0]==1 else 4))[0];header=ast.literal_eval(f.read(size).decode());digest=hashlib.sha256()
  for chunk in iter(lambda:f.read(1048576),b''):digest.update(chunk)
 assert digest.hexdigest()==meta['arrays_sha256'][key]
 pins[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
removed=set(json.loads((r/'milestones/144-countfree-share18/data/share18-impact/removed-indices.json').read_text()))
# Reopen the bounded source columns because the imported script closed its handles.
for key,(f,offset,fmt) in list(scalar.files.items()):scalar.files[key]=((r/'milestones/164-loss-corrected-potential/data/scaled-floor17/source-columns'/(key+'.npy')).open('rb'),offset,fmt)
checks=[]
for folder,joint in [('graph-final',False),('graph-joint15',True)]:
 p=h/'data'/folder/'floor15.json';j=json.loads(p.read_text());assert j['status']=='PASS_POTENTIAL';w=j['walk']
 for x in w:
  assert x['source_edge'] not in removed
  y=scalar.row(x['source_edge'],15,joint);assert all(y[k]==x[k] for k in ['u','v','weight'])
 assert all(a['v']==b['u'] for a,b in zip(w,w[1:]))
 assert j['scaled_mean']*len(w)-9*sum(x['weight'] for x in w)==j['range']
 checks.append({'profile':folder,'edges':len(w),'weight':sum(x['weight'] for x in w),'forced_scaled_range':j['range'],'result_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
obs=json.loads((h/'data/scalar-obstructions.json').read_text())
for row in obs['rows']:
 for x in row['cycle']+row['walk']:assert x['source_edge'] not in removed
 assert row['cycle'][0]['u']==row['cycle'][-1]['v']
 assert all(a['v']==b['u'] for a,b in zip(row['cycle'],row['cycle'][1:]))
 assert all(a['v']==b['u'] for a,b in zip(row['walk'],row['walk'][1:]))
(h/'data/independent-witness-audit.json').write_text(json.dumps({'status':'PASS_INDEPENDENT_SCALAR_WITNESSES','column_pins':pins,'new_potential_walks':checks,'obstruction_floors':list(range(10,18)),'scope':'Independent reconstruction of exact witness rows; full all-edge scans are separately recorded by the producer.'},indent=2)+'\n')
print('PASS_INDEPENDENT_SCALAR_WITNESSES',checks)
for f,_,_ in scalar.files.values():f.close()
