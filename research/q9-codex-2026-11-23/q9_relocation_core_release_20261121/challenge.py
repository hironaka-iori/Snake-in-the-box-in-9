from repair import *
pp=placements()
for z in map(json.loads,(B/'grown.jsonl').read_text().splitlines()):
    r=rows[z['rank']];s=set(z['mandatory']);g=pp[z['rank'],0][0]
    # Remove the two most underrepresented learned groups in the 191-edge source.
    groups=[set(a['core']) for a in z['history'] if a['core']]
    groups.sort(key=lambda h:(len(h-set(g)),len(h)),reverse=True)
    barrier=set.union(*groups[:2]);hard=s-barrier
    for c in (r['majority'],1-r['majority']):
        a=solve(r,hard,g,42000,c)
        print(json.dumps(dict(rank=z['rank'],c=c,released_group=sorted(barrier),freed=sorted(set(r['oldfixed'])-hard),**a)),flush=True)
        if a['result']=='FOUND':sys.exit()
