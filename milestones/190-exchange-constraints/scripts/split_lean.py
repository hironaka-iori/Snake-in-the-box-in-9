from pathlib import Path
import json,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/190-exchange-constraints';D=Path('D:/Codex/2026-10-13/new-chat/work');s=(D/'ExchangeAccounting190.lean').read_text()
positions=[s.index('theorem '+n) for n in ['edgeAccounting','incidenceAccounting','fixedEndpointExchange']];end=s.index('#print axioms edgeAccounting')
files={'EdgeData190':s[:positions[0]]+'#print axioms oneAccounting\n#print axioms oneIncidence\nend ExchangeAccounting190\n',
'EdgeBalance190':'import EdgeData190\nnamespace ExchangeAccounting190\n'+s[positions[0]:positions[1]]+'#print axioms edgeAccounting\nend ExchangeAccounting190\n',
'IncidenceBalance190':'import EdgeData190\nnamespace ExchangeAccounting190\n'+s[positions[1]:positions[2]]+'#print axioms incidenceAccounting\nend ExchangeAccounting190\n',
'ExchangeAccounting190':'import EdgeBalance190\nimport IncidenceBalance190\nnamespace ExchangeAccounting190\n'+s[positions[2]:end]+'#print axioms fixedEndpointExchange\n#print axioms componentAccounting\n#print axioms fiveVertexCases\nend ExchangeAccounting190\n'}
for n,text in files.items():(H/'lean'/(n+'.lean')).write_text(text,encoding='utf-8',newline='\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((H/'data/ExchangeAccounting190-execution.json').read_text());base['new_module_order']=list(files);base['source_sha256']={n:sha(H/'lean'/(n+'.lean')) for n in files}
for n in files:(H/'data'/(n+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/current-order.json').write_text(json.dumps(list(files),indent=2)+'\n');(H/'scripts/split_lean.py').write_bytes(Path(__file__).read_bytes())
