from graph_solver import *
H=Path(__file__).resolve().parent;bank=json.loads((H.parent/'branch241-audit/repo/work/bank9.json').read_text());rows=[]
for entry in range(8):
 for mode in ['leaf','block']:
  p=bank[entry//2]['vertex_sequence'][::(-1 if entry%2 else 1)][:152]
  r=Search(9,192,p,mode,200000,10).run();r['entry']=entry;rows.append(r)
  print(entry,mode,r['status'],r['stats']['nodes'],round(r['seconds'],4),r['stats']['pruned_block'],flush=True)
  (H/'bank152_benchmarks.json').write_text(json.dumps({'scope':'eight restricted prefixes, not global','runs':rows},indent=2)+'\n')
