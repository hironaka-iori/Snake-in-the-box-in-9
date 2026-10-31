"""Refine only the frozen critical-edge subset using current completed count cases.
Does NOT re-extract the current complete graph's critical family.
"""
from pathlib import Path
import json,collections
H=Path(__file__).resolve().parent

def canon(word):
 seen={};return [seen.setdefault(v,len(seen)) for v in word]

def hits(edge,case):
 for offset in range(2,5):
  for rev in [False,True]:
   word=edge['directions'][offset:offset+5]
   if canon(word[::-1] if rev else word)!=case['dirs']:continue
   indices=[offset+(5-j if rev else j)-3 for j in range(1,5)]
   # Bucket six denotes [6,21]; every admitted interval contains all or none of it.
   for lo,hi in case['bounds']:
    if hi>=6 and hi!=21:raise ValueError('partial upper cutoff inside count bucket')
    if lo>6:raise ValueError('partial lower cutoff inside count bucket')
   if all(lo<=edge['counts'][i]<=hi for i,(lo,hi) in zip(indices,case['bounds'])):return True
 return False

def run():
 edges=json.loads((H.parent/'global-cycle-compression-20261031/critical_edges_frozen.json').read_text());current=json.loads((H.parent/'global-cycle-compression-20261031/upstream_proved_model.json').read_text());old=json.loads((H/'frozen_source_model.json').read_text());cases=[c for c in json.loads((H/'current_cases.json').read_text()) if c['number'] in current['applied_cases']]
 removed=collections.Counter();kept=[]
 for edge in edges:
  hit=[c['number'] for c in cases if hits(edge,c)]
  for c in hit:removed[c]+=1
  if not hit:kept.append(edge)
 assert all(not removed[c] for c in old['applied_cases'])
 (H/'filtered_critical_edges.json').write_text(json.dumps(kept,separators=(',',':'))+'\n')
 result={'frozen_cases':old['applied_cases'],'current_cases':current['applied_cases'],'added_cases':sorted(set(current['applied_cases'])-set(old['applied_cases'])),'old_records':len(edges),'retained_critical_records':len(kept),'removed_by_case':dict(removed),'scope':'filtering frozen critical subset only; not full-current-family reconstruction'}
 (H/'case_filter.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
