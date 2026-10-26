"""Split the same semantic certificate into independently retained kernel checks."""
from pathlib import Path
import ast,gzip,hashlib,json
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--row',type=int,choices=[0,5],required=True);args=ap.parse_args()
HERE=Path(__file__).resolve().parents[1];MOD=f'ShareObstruction53{args.row}';NS='Snake9.LocalWindow.'+MOD
p=HERE/f'lean/LocalWindowSat/{MOD}.lean';backup=HERE/f'data/original-semantic-module{args.row}.txt'
if not backup.exists():backup.write_bytes(p.read_bytes())
s=backup.read_text();front=s.split('theorem check :',1)[0];sat='theorem sat :'+s.split('theorem sat :',1)[1]
folder=HERE/f'lean/LocalWindowSat/{MOD}';folder.mkdir(exist_ok=True)
(folder/'Data.lean').write_text(front+f'end {NS}\n')
header=f'import LocalWindowSat.{MOD}.Data\nimport ShareCheckAppend\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {NS}\nopen Snake9.LocalWindow.Tags\n'
(folder/'Counters.lean').write_text(header+'theorem counters_checked : ctrs.all (ctrOK meaning (centresK window bounds)) = true := by decide +kernel\n'+f'end {NS}\n')
(folder/'Totalizers.lean').write_text(header+'theorem totalizers_checked : tots.all (totOK meaning smeaning window (centresK window bounds)) = true := by decide +kernel\n'+f'end {NS}\n')
meta=json.loads((HERE/f'data/obstruction{args.row}_95.json').read_text());info=json.loads(gzip.decompress((HERE/f'certificates/obstruction{args.row}_95.meanings.json.gz').read_bytes()))
raw=[]
for l in (HERE/f'certificates/obstruction{args.row}_95.cnf').read_text().splitlines():
 if l and not l.startswith(('p','c')):raw.append([2*v if v>0 else -2*v+1 for v in list(map(int,l.split()))[:-1]])
tree=ast.parse((HERE/'scripts/export_share.py').read_text());ns={}
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['stream','tag48']],type_ignores=[]),'packed-tag-helpers','exec'),ns)
tags=[ns['tag48'](info['tags'][i-1]) for i in meta['source_original_clause_ids']]
assert len(tags)==len(raw)==meta['core_clauses']
count=(len(raw)+255)//256
for i,start in enumerate(range(0,len(raw),256)):
 ts=tags[start:start+256];rs=raw[start:start+256];packed=[len(ts[j:j+64])+(ns['stream'](ts[j:j+64],48)<<8) for j in range(0,len(ts),64)]
 text=header+f'noncomputable def tags{i} : List TagS := tagsOfSL ['+','.join(f'(nat_lit 0x{x:x})' for x in packed)+']\n'
 text+=f'def raw{i} : List (List Nat) := '+str(rs)+'\n'
 text+=f'theorem clauses{i}_checked : ckAllS meaning smeaning resolution ctrs tots window cap tags{i} raw{i} = true := by decide +kernel\nend {NS}\n'
 (folder/f'Clauses{i}.lean').write_text(text)
imports=''.join(f'import LocalWindowSat.{MOD}.{name}\n' for name in ['Counters','Totalizers']+[f'Clauses{i}' for i in range(count)])
text=imports+f'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {NS}\nopen Snake9.LocalWindow.Tags\n'
text+='theorem check : checkAllS meaning smeaning resolution ctrs tots window bounds cap tags raw = true := by\n'
text+=f'  have h{count} : ckAllS meaning smeaning resolution ctrs tots window cap [] [] = true := rfl\n'
for i in reversed(range(count)):
 text+=f'  have h{i} := ckAllS_append_true meaning smeaning resolution ctrs tots window cap clauses{i}_checked h{i+1}\n'
text+='  have h : ckAllS meaning smeaning resolution ctrs tots window cap tags raw = true := h0\n'
text+='  simpa only [checkAllS, counters_checked, totalizers_checked, Bool.true_and] using h\n'+sat
p.write_text(text)
(HERE/f'data/semantic-split{args.row}.json').write_text(json.dumps(dict(chunks=count,clauses=len(raw),original_source_sha256=hashlib.sha256(backup.read_bytes()).hexdigest(),reason='The original checking process and tool handles were absent after interruption. Split checks preserve completed kernel work without changing the CNF or mathematical statement.'),indent=2)+'\n')
print('Split semantic clauses into',count,'checks plus counters and totalizers.')
