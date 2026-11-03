"""Specialize the audited resource-gated checker without changing old files."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for old,new,kind in [('check_pair_lower.py','check_large_lower.py','lower'),('check_pair_clauses.py','check_large_clauses.py','clauses')]:
 template=R/'milestones/128-coupled-pair/audit'/old
 text=template.read_text()
 for a,b in [('PairLower128','LargeLower130'),('PairClauses128','LargeClauses130'),
             ('pair-lower-','large-lower-'),('pair-clauses-','large-clauses-'),
             ('check_pair_lower.py','check_large_lower.py'),('data/pair-counter.json','data/large-counter.json'),
             ('generate_pair_clauses.py','generate_large_clauses.py'),('concrete-pair-generation.json','concrete-large-generation.json'),
             ('proc.wait(timeout=180)','proc.wait(timeout=600)')]:text=text.replace(a,b)
 if kind=='clauses':
  text=text.replace("HERE / 'logs/large-lower-1793687781271460700/record.json'", "HERE / 'data/independent-large-lower-audit.json'")
  text=text.replace('Actual normalized snake satisfaction of the added2863 pair-counter clauses only; no full CNF refutation or six-count floor23.',
                    'Actual normalized snake satisfaction of exactly the 717 added fourth-count counter clauses under fourth>=4; no combined input refutation or six-count lower bound.')
 else:
  text=text.replace('Actual normalized snake pair cap and generic positive-literal counter semantics; no complete CNF refutation or six-count floor23.',
                    'Actual fourth-centre selected cap17 under fourth>=4 and generic positive-literal counter semantics; no complete CNF refutation or six-count lower bound.')
 marker="    save()\n    print(json.dumps(dict(status=state['status'], seconds=state['seconds'], record=str(record),"
 assert text.count(marker)==1
 text=text.replace(marker,"    save()\n    if success:\n        (HERE / 'data/independent-large-"+kind+"-audit.json').write_bytes(record.read_bytes())\n    print(json.dumps(dict(status=state['status'], seconds=state['seconds'], record=str(record),")
 path=H/'audit'/new;assert not path.exists();path.write_text(text,encoding='utf-8',newline='\n')
 rows.append(dict(template=template.relative_to(R).as_posix(),template_sha256=sha(template),checker=path.relative_to(H).as_posix(),checker_sha256=sha(path)))
(H/'audit/checker-generation.json').write_text(json.dumps(dict(status='GENERATED_CHECKERS',script_sha256=sha(Path(__file__)),files=rows),indent=2)+'\n',encoding='utf-8')
print(json.dumps(rows,indent=2))
