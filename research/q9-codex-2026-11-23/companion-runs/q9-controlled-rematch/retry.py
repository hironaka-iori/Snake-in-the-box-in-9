from pathlib import Path
import argparse,json,sys
from collections import Counter
import search as controlled

def fixed_set(p,cycle,tr,radius):
    name,ctl,kind,bits,sign=tr;sh=(1<<bits[0]) if sign else 0
    w=[(controlled.moved(v^sh,bits)^sh) if v>>ctl&1 else v for v in p]
    def cross(seq):
        ix={x:i for i,x in enumerate(seq)}
        return {(i,ix[x^(1<<ctl)]) for i,x in enumerate(seq) if not x>>ctl&1 and x^(1<<ctl) in ix}
    bad={i for edge in cross(p)^cross(w) for i in edge}
    row=[None,None,None,tr,bad,None,None]
    return controlled.image_case(p,cycle,row,radius)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('repo',type=Path);ap.add_argument('run',type=Path);ap.add_argument('budget',type=int)
    a=ap.parse_args();root=Path(__file__).parent;sys.path.insert(0,str(a.repo))
    from retry_q9_six_cube_sites_cadical import search
    bank={nm:(p,cy) for nm,p,cy in controlled.load_sources(a.repo)};ALL=set(range(512))
    control=json.loads((root/'small_controls.json').read_text())[0]
    p,cy=bank[control['name']]
    tr=[control['name'],8,'swap',[6,7],1]
    seed,fixed=fixed_set(p,cy,tr,1)
    fixed-=set(control['deleted'])
    assert fixed<=set(control['vertices'])
    st,w=search(fixed,seed,191,25000,allowed=ALL)
    assert st=='FOUND' and set(w)>=fixed and len(w)>=192
    controlled.pairwise(w)
    checked_control=w
    doc=json.loads(a.run.read_text());results=[];counts=Counter()
    for row in doc['results']:
        if row['status']!='UNKNOWN':continue
        p,cy=bank[row['transform'][0]];seed,fixed=fixed_set(p,cy,row['transform'],row['radius'])
        assert len(fixed)==row['known_fixed']
        st,w=search(fixed,seed,192,a.budget,allowed=ALL)
        entry=dict(transform=row['transform'],radius=row['radius'],fixed=len(fixed),status=st)
        if w:
            controlled.pairwise(w);assert len(w)>=193 and fixed<=set(w)
            entry['vertices']=w
        results.append(entry);counts[st]+=1
        if w:break
    out=dict(parent=a.run.name,at_least_target=192,budget=a.budget,control=dict(target=191,fixed=len(fixed_set(*bank[tr[0]],tr,1)[1]-set(control['deleted'])),vertices=checked_control),results=results,counts=counts)
    (root/(a.run.stem+'_cadical.json')).write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(counts,flush=True)
if __name__=='__main__':main()
