"""Use explicit small meaning subtrees to avoid repeated packed decoding."""
from pathlib import Path
import json,gzip,hashlib,re
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel');R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sem=json.loads(gzip.decompress((R/'milestones/180-share14-certificates/certificates/012034.meanings.json.gz').read_bytes()))
delta=json.loads(gzip.decompress((R/'milestones/183-critical-floor15/certificates/012034-floor15.delta.json.gz').read_bytes()))
meta=read(H/'data/share185.json');rename={int(k):v for k,v in meta['original_to_new'].items()};nv=meta['semantic_variables']
old={rename[int(k)]:v for k,v in sem['meaning'].items() if int(k) in rename}
share={int(k):v for k,v in sem['smeaning'].items()}
for k,v in delta['new_meanings'].items():share[int(k)]=v[:3] if v[0]=='u' else ['t',71,*v[1:]]
new={rename[k]:v for k,v in share.items() if k in rename}
def leaf(k,which):
 v=(old if which=='m' else new).get(k)
 return '.z' if v is None else '(.'+v[0]+' '+' '.join(map(str,v[1:]))+')'
def tree(r,s,which):
 if r+s>nv:return leaf(r,which)
 return '(.n '+tree(r,2*s,which)+' '+tree(r+s,2*s,which)+')'
def root(r,s,which):
 if s==64:return which+str(r)
 return '(.n '+root(r,2*s,which)+' '+root(r+s,2*s,which)+')'
ns='Snake9.LocalWindow.ShareWindow185'
mods=[]
for g in range(8):
 name=f'Share185.MeaningGroup{g:02d}';mods.append(name)
 s='import Share185.Data\nset_option maxRecDepth 100000\nnamespace '+ns+'\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
 for k in range(8*g,8*g+8):
  for w,typ in [('m','MT'),('x','MS')]:s+=f'def {w}{k} : {typ} := '+tree(k,64,w)+'\n'
 s+='end '+ns+'\n';(H/'lean'/(name.replace('.','/')+'.lean')).write_text(s,newline='\n')
s=''.join('import '+n+'\n' for n in mods)+'namespace '+ns+'\nopen Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185\n'
s+='def meaningDirect : MT := '+root(0,1,'m')+'\ndef smeaningDirect : MS := '+root(0,1,'x')+'\nend '+ns+'\n'
(H/'lean/Share185/DirectData.lean').write_text(s,newline='\n');mods+=['Share185.DirectData']
order=read(H/'data/current-order.json');i=order.index('Share185.Structure');order=order[:i]+mods+order[i:]
for name in order[order.index('Share185.Structure'):]:
 p=H/'lean'/(name.replace('.','/')+'.lean')
 assert not (H/'data'/(name+'-audit.json')).exists()
 s=p.read_text().replace('import Share185.Data','import Share185.DirectData')
 s=re.sub(r'\bsmeaning\b','smeaningDirect',s);s=re.sub(r'\bmeaning\b','meaningDirect',s)
 p.write_text(s,newline='\n')
base=read(H/'data/Share185.Structure-execution.json')
base['new_module_order']=order;base['source_sha256']={n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order}
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 (H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
(H/'scripts/direct_meanings.py').write_bytes(Path(__file__).read_bytes())
(H/'data/direct-meanings.json').write_text(json.dumps({'semantic_variables':nv,'groups':8,'subtrees_per_type':64,'packed_definition_preserved':True,'raw_cnf_unchanged':True,'method':'Explicit meaning subtrees; correctness determined by concrete Lean clause soundness checks.'},indent=2)+'\n')
print('DIRECT_MEANINGS',len(order),'modules; packed meanings retained, exact CNF unchanged.')

