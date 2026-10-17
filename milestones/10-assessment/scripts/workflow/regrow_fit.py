import json, math, statistics as st
R='/home/user/Snake-in-the-box-in-9/outputs/'
data={}
for k in (128,120,112):
    d=json.load(open(R+f'dfs_regrow_keep{k}.json'))
    data[k]={(r['index'],r['reversed']):r for r in d['results']}
    print(k, d['total_nodes'], d['elapsed_seconds'], d['counts'], len(d['results']))
rows=[json.loads(l) for l in open(R+'dfs_regrow_keep104.partial.jsonl')]
from collections import Counter
print(Counter(r['status'] for r in rows), len(rows))
d104={}
for r in rows:
    d104[(r['index'],r['reversed'])]=r
data[104]=d104
for r in rows: print(r['index'],r['reversed'],r['status'],r['nodes'],r.get('best_vertices'))
# per-instance ratios
for a,b in ((128,120),(120,112),(112,104)):
    common=[key for key in data[b] if key in data[a] and data[b][key]['status']=='INFEASIBLE']
    rat=[data[b][key]['nodes']/max(1,data[a][key]['nodes']) for key in common]
    if rat:
        lg=[math.log10(x) for x in rat]
        print(a,'->',b,'n=',len(rat),'median ratio',st.median(rat),'geo mean',10**st.mean(lg),'sd log10',st.pstdev(lg) if len(lg)>1 else 0, 'min',min(rat),'max',max(rat))
# per-k summary stats
for k in (128,120,112,104):
    ns=[r['nodes'] for r in data[k].values() if r['status']=='INFEASIBLE']
    lg=[math.log10(max(1,x)) for x in ns]
    print(k,'n',len(ns),'sum %.3e'%sum(ns),'median %.3e'%st.median(ns),'geomean %.3e'%10**st.mean(lg),'max %.3e'%max(ns))
