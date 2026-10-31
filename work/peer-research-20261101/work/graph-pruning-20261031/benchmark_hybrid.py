from graph_solver import *
H=Path(__file__).resolve().parent;bank=json.loads((H.parent/'branch241-audit/repo/work/bank9.json').read_text());rows=[]
for entry in range(8):
 for mode in ['leaf','block','claw','hybrid']:
  p=bank[entry//2]['vertex_sequence'][::(-1 if entry%2 else 1)][:152];t=time.perf_counter()
  r=Search(9,192,p,mode,200000,10).run();r['benchmark_wall_seconds']=time.perf_counter()-t;r['entry']=entry;rows.append(r)
(H/'hybrid_bank152_benchmarks.json').write_text(json.dumps({'scope':'eight restricted prefixes; executable verification, not Lean proof','runs':rows},indent=2)+'\n')
for mode in ['leaf','block','claw','hybrid']:
 a=[r for r in rows if r['mode']==mode];print(mode,sum(x['stats']['nodes'] for x in a),round(sum(x['benchmark_wall_seconds'] for x in a),5),all(x['status']=='UNSAT_EXHAUSTIVE_PYTHON' for x in a))
