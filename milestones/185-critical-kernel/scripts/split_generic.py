from pathlib import Path
import json,hashlib,re
H=Path('E:/Snake-in-a-box/milestones/185-critical-kernel')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=H/'lean/LocalWindowTagsShare185.lean';s=p.read_text()
(H/'scripts/split_generic.py').write_bytes(Path(__file__).read_bytes())
(H/'data/unsplit-generic.lean.txt').write_text(s)
markers=['/-! ## Soundness -/','/-! ### Blocks -/','/-! ### Totalizer kinds -/','/-! ### Clause families -/','theorem kind_emp','/-- Main soundness theorem']
positions=[s.index(x) for x in markers]
names=['Share185Definitions','Share185Basic','Share185Blocks','Share185Totals','Share185Counters','Share185Clauses','LocalWindowTagsShare185']
parts=[s[:positions[0]]]+[s[a:b] for a,b in zip(positions,positions[1:])]+[s[positions[-1]:]]
header='namespace Snake9.LocalWindow.Tags185\nopen Snake9.LocalWindow.Tags\nopen Snake9.LocalWindow\n'
var='variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}\nvariable {w : List Nat} {cens : List Centre}\n'
for i,(name,part) in enumerate(zip(names,parts)):
 if i==0:part+='\nend Snake9.LocalWindow.Tags185\n'
 else:
  part=re.sub(r'^section (Lemmas|Families)\n','',part,flags=re.M)
  part=re.sub(r'^end (Lemmas|Families)\n','',part,flags=re.M)
  part=re.sub(r'^variable .*?\n','',part,flags=re.M)
  part='import '+names[i-1]+'\n'+header+var+part
  if i<6:part+='\nend Snake9.LocalWindow.Tags185\n'
 if i==3:part+='\n#print axioms Snake9.LocalWindow.Tags185.cap_total\n'
 (H/'lean'/(name+'.lean')).write_text(part,encoding='utf-8',newline='\n')
plans=list((H/'data').glob('*-execution.json'))
base=json.loads(plans[0].read_text())
order=names+base['new_module_order'][1:]
sources={p.relative_to(H/'lean').with_suffix('').as_posix().replace('/','.'):sha(p) for p in (H/'lean').rglob('*.lean')}
base['new_module_order']=order;base['source_sha256']=sources
for name in order:(H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
print('SPLIT_GENERIC',names)

