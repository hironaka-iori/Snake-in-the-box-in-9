from graph_solver import *
HERE=Path(__file__).resolve().parent
bank=json.loads((HERE.parent/'branch241-audit/repo/work/bank9.json').read_text())
rows=[]
experiments=[('global-Q5-14',5,14,[0],50000,5),('global-Q9-235',9,235,[0],6000,6),('bank0-keep96-192',9,192,bank[0]['vertex_sequence'][:96],10000,5),('bank0-keep128-192',9,192,bank[0]['vertex_sequence'][:128],10000,5)]
for label,n,target,prefix,nodes,sec in experiments:
 for mode in ['reach','parity','leaf','block','separator']:
  r=Search(n,target,prefix,mode,nodes,sec).run();r['experiment']=label;rows.append(r)
  (HERE/'benchmarks.json').write_text(json.dumps({'scope':'bounded ablation; UNKNOWN never proves exclusion','runs':rows},indent=2)+'\n')
  print(json.dumps({'experiment':label,'mode':mode,'status':r['status'],'nodes':r['stats']['nodes'],'seconds':round(r['seconds'],4),'block_prunes':r['stats']['pruned_block'],'separator_prunes':r['stats']['pruned_separator']}),flush=True)
