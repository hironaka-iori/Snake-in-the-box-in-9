from pathlib import Path
import re,json,hashlib,zipfile
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/'scripts/split_lemmas.py').write_bytes(Path(__file__).read_bytes())
with zipfile.ZipFile(H/'data/pre-lemma-split.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for p in (H/'data').glob('*-execution.json'):z.write(p,p.relative_to(H).as_posix())
 for p in (H/'lean').glob('Share185*.lean'):z.write(p,p.relative_to(H).as_posix())
s=(H/'data/unsplit-generic.lean.txt').read_text()
s=s[s.index('theorem lv_congr'):s.index('end Snake9.LocalWindow.Tags185')]
s=re.sub(r'^section (Lemmas|Families)\n','',s,flags=re.M)
s=re.sub(r'^end (Lemmas|Families)\n','',s,flags=re.M)
s=re.sub(r'^variable .*?\n','',s,flags=re.M)
starts=[m.start() for m in re.finditer(r'^theorem ',s,re.M)]+[len(s)]
names=['Share185Definitions'];var='variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}\nvariable {w : List Nat} {cens : List Centre}\n'
for i,(a,b) in enumerate(zip(starts,starts[1:])):
 name=f'Share185Proof{i:02d}';part=s[a:b]
 body='import '+names[-1]+'\nnamespace Snake9.LocalWindow.Tags185\nopen Snake9.LocalWindow.Tags\nopen Snake9.LocalWindow\n'+var+part+'\nend Snake9.LocalWindow.Tags185\n'
 (H/'lean'/(name+'.lean')).write_text(body,newline='\n');names.append(name)
(H/'lean/LocalWindowTagsShare185.lean').write_text('import '+names[-1]+'\n'+''.join('#print axioms Snake9.LocalWindow.Tags185.'+n+'\n' for n in ['cap_total','soundS','refutedShare_of_check']),newline='\n')
names+=['LocalWindowTagsShare185']
base=json.loads((H/'data/Share185Basic-execution.json').read_text())
tail=base['new_module_order'][base['new_module_order'].index('LocalWindowTagsSharePacked185'):]
order=names+tail
sources={n:sha(H/'lean'/(n.replace('.','/')+'.lean')) for n in order}
base['new_module_order']=order;base['source_sha256']=sources
for name in order:
 if name=='Share185Definitions':continue
 (H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(order,indent=2)+'\n')
print('SPLIT',len(starts)-1,'generic proofs;',len(order),'modules.')

