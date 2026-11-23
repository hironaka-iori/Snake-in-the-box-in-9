from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'retry.py').read_text()
s=s.replace("with (r/'retry.jsonl').open('w',1) as out:","pending={(n,j) for n,j,idx,g,st,w in (json.loads(l) for l in (r/'retry.jsonl').open()) if st=='UNKNOWN'}\n with (r/'deepretry.jsonl').open('w',1) as out:")
s=s.replace("if st!='UNKNOWN':continue","if (name,j) not in pending:continue").replace('goal,110000','goal,420000')
(r/'deepretry.py').write_text(s)

