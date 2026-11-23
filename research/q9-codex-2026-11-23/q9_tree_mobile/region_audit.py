import collections,json
from audit import checked,D
def load(f):return [json.loads(l) for l in (D/f).read_text().splitlines()]
def main():
    cases={};best=None
    parents=[r["path"] for l in (D/"growth.log").read_text().splitlines() if (r:=json.loads(l))["kind"]=="W"]
    for kind in ['target','grow','172']:
        a=load('region_'+kind+'.log');counts=collections.Counter();sizes=[];pairchecks=0
        for i,r in enumerate(a):
            assert r['i']==i;counts[r['status']]+=1;sizes.append(r['region'])
            if r['status']=='FOUND':
                p=r['path'];src=r['source'];s=set(src[::2]);z=set(p[::2]);zone=set(r['area'])
                assert len(p)==2*(len(s)+1)-1 and s-z<=zone and len((z-s)-zone)<=1
                assert len(s-z)>=2 and r['moves']==len(s-z)
                if kind!="target":assert src in parents or src[::-1] in parents;parents.append(p)
                pairchecks+=checked(p)
                if best is None or len(p)>len(best['path']):best=r
        cases[kind]=dict(trials=len(a),status=counts,area_range=[min(sizes),max(sizes)],witness_pairs=pairchecks)
    control=json.loads((D/'region_control.json').read_text());assert len(control)==15
    for z in control:assert z['status']=='FOUND' and len(z['path'])==191;checked(z['path'])
    res=dict(cases=cases,controls=15,best_result=best)
    (D/'region_verified.json').write_text(json.dumps(res,indent=2)+'\n');print(cases)
if __name__=='__main__':main()
