from pathlib import Path
import ast,hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
rows=[]
for name in ['47-critical-singleton-patterns','48-low-count-compatibility','49-six-direction-pair-catalogue','50-three-count-return']:
 folder=ROOT/'milestones'/name;p=folder/'data/verification.json';r=json.loads(p.read_text());assert r['status']=='PASS'
 for rel,h in r['sources_sha256'].items():assert hashlib.sha256((folder/'lean'/rel).read_bytes()).hexdigest()==h
 rows.append(dict(milestone=name,receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_hashes_checked=len(r['sources_sha256']),recorded_lean_audits=r['lean_audits']))
model=json.loads((HERE/'data/enriched-model.json').read_text());matched=0
for rule in model['additional_proved_rules']:
 folder=ROOT/'milestones'/rule['source']/'lean';number=rule['number'];is_sum=rule.get('kind')=='sum'
 source=folder/(('SumWindow' if is_sum else 'CycleExclusion')+str(number)+'.lean');text=source.read_text(encoding='utf-8-sig')
 directions=ast.literal_eval(re.search(r'def directions : List Nat := (\[[^\n]+\])',text)[1]);assert directions==rule['dirs']
 if is_sum:
  expected=str(rule['cap']+1)+' ≤ '+' + '.join('coreAlpha p (r+'+str(j)+')' for j in rule['positions'])
  assert expected in text
 else:
  text=(folder/f'LocalWindowCnf/CycleWindow{number}.lean').read_text(encoding='utf-8-sig')
  bounds=ast.literal_eval(re.search(r'def bounds : List \(Nat × Nat\) := (\[[^\n]+\])',text)[1]);expected=[(0,21)]*(len(directions)-1)
  if rule['source'].startswith('47'):expected[rule['position']-1]=(0,1)
  else:
   for pos,cap in zip(rule['positions'],rule['caps']):expected[pos-1]=(0,cap)
  assert bounds==expected
 matched+=1
out=dict(status='PASS',rules_matched_to_proved_statements=matched,records=rows,total_source_hashes_checked=sum(x['source_hashes_checked'] for x in rows),scope='Current source hashes match previous proof verification receipts. Complete imported proof closures were not rebuilt this round.')
(HERE/'data/import-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
