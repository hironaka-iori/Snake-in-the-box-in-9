from pathlib import Path
import json,re,hashlib,datetime
R=Path('E:/Snake-in-a-box');H=R/'milestones/186-structural-interpretation';D=Path('D:/Codex/2026-10-13/new-chat/outputs')
j=json.loads(Path('D:/Codex/2026-10-13/new-chat/work/round186_compilation.json').read_text())
for value in j.values():assert not value.get('isError') and json.loads(value['content'][0]['text'])['kind']=='success'
out={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiler_results':j,'source_sha256':{},'visual_page_inspection':False}
for n in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/n;old=(H/'source-before'/n).read_text(encoding='utf-8');s=p.read_text(encoding='utf-8')
 assert re.findall(r'\\author\{[^\n]+',old)==re.findall(r'\\author\{[^\n]+',s)
 assert re.findall(r'\\hypersetup\{.*?\n\}',old,re.S)==re.findall(r'\\hypersetup\{.*?\n\}',s,re.S)
 assert p.read_bytes()==(R/'paper'/n).read_bytes()
 out['source_sha256'][n]=hashlib.sha256(p.read_bytes()).hexdigest()
(H/'data/document-compilation.json').write_text(json.dumps(out,indent=2)+'\n')
extra='\nThe immediate next unaccepted batch is Share185.Shard38. Batches 00–37 cover 4,864 clauses; 7,560 clauses remain. The two-half split of batch 37 and Share186.ClauseAppend are accepted examples for splitting subsequent oversized batches. All 73 individual counter conditions and their aggregate structural theorem are accepted. The 60 remaining batches and final initial-database composition are unfinished.\n'
for p in [H/'README.md',R/'handoff/CURRENT_STATUS.md',R/'handoff/NEXT_AGENT_PROMPT.md']:
 p.write_text(p.read_text(encoding='utf-8')+extra,encoding='utf-8',newline='\n')
(H/'scripts/publication_ready.py').write_bytes(Path(__file__).read_bytes())
print('Both documents compiled; mirrors, authors and hyperlink settings preserved.')
