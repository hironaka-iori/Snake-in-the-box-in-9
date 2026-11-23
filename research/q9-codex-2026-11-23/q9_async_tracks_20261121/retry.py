from freeclocks import solve,D
import json,sys
mode=sys.argv[1];wfile='complete_target.in' if mode=='target' else 'seam_damage.in'
data=(D/wfile).read_text().splitlines()
if mode=='target':
    ids=[z['i'] for z in map(json.loads,(D/'complete_sat2.jsonl').read_text().splitlines()) if z['status']=='LIMIT']
    # Start with every incomplete trial on the hardest near-one templates.
    ids=sorted(ids,key=lambda i:(int(i>=404),list(map(json.loads,(D/'complete_target.jsonl').read_text().splitlines()))[i]['defects'],i))[:160]
else:ids=list(range(min(30,len(data))))
for i in ids:
    w,g,*_=data[i].split();st,n,c,cl,z=solve(w,g,2,11000 if mode=='target' else 4000,'cd')
    print(json.dumps(dict(i=i,status=st,states=n,conflicts=c,clauses=cl,word=z),separators=(',',':')),flush=True)
    if z and len(z)>=192:break
