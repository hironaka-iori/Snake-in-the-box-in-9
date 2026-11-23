from pathlib import Path
import json,itertools,collections,re
from run import validate,verify
from prep import D,path,edges
def cpp(file):
 data={}
 for line in (D/file).read_text().splitlines():
    if line.startswith('R '):
       _,idx,status,*nums=line.split()
       data[int(idx)]=(status,*map(int,nums))
 return data
def jdata(file):return [json.loads(l) for l in (D/file).read_text().splitlines()]
def main():
 ep=jdata('endpoints.jsonl'); rows=cpp('unmasked_endpoints.log');assert len(ep)==len(rows)==14581
 masks=collections.defaultdict(set)
 for r in ep:masks[r['word']].add(tuple(r['rm']))
 for w,sets in masks.items():
    defects=edges(path(w));tips=set().union(*[set(edge) for edge in defects]);assert sets=={r for h in (1,2,3) for r in itertools.combinations(sorted(tips),h) if all(set(r)&set(c) for c in defects)}
 anchors=jdata('minimal.jobs'); per_word=collections.defaultdict(list)
 for i,r in enumerate(anchors):per_word[r['word']].append(i)
 for word,inds in per_word.items():
    sets=masks[word];assert {frozenset(anchors[i]['rm']) for i in inds}=={frozenset(r) for r in sets if not any(set(v)<set(r) for v in sets)}
 joint=cpp('joint.results')
 for i,v in cpp('joint_first2.log').items():
    assert i<2
    if v[0]=='CLOSED':joint[i]=v
 summary=dict(registered_tip_rows=len(rows),registered_tip_status=dict(collections.Counter(v[0] for v in rows.values())),registered_family_size=dict(collections.Counter(len(edges(path(w))) for w in masks)))
 summary['principal_parity_runs']={}
 for mode in ('primary','neighbors','registered','controls'):
    r=jdata(mode+'.results');jobs=jdata(mode+'.jobs');assert len(r)==len(jobs)
    for z,q in zip(r,jobs):
       if 'witness' in z:
          w=z['witness'];p=w['path'];validate(p);assert len(p)==192
          tab=[0]
          for g in w['basis']:tab += [x^g for x in tab]
          assert len(set(tab))==512 and set(q['points'])<=set(tab[x] for x in p)
    summary['principal_parity_runs'][mode]=dict(rows=len(r),status=dict(collections.Counter(z['result'] for z in r)),eligible=sum(z['eligible'] for z in r),bases=sum(z['basis_completions'] for z in r))
 counts=collections.Counter();seed_counts=collections.defaultdict(collections.Counter); unique=set()
 mfile=(D/'broader.map').read_text().splitlines()
 rfile=cpp('broader.results')
 assert len(mfile)==len(rfile)==37203
 for i,line in enumerate(mfile):
    seed,*rm=map(int,line.split());mask=(seed,*rm);assert mask not in unique;unique.add(mask)
    counts[len(rm),rfile[i][0]]+=1;seed_counts[seed][len(rm),rfile[i][0]]+=1
 for word,ids in per_word.items():
    n=193; chords=edges(path(word)); seed=anchors[ids[0]]['seed']; tips={0,192}|{x+d for e in chords for x in e for d in range(-2,3) if 0<=x+d<n}
    exp=set()
    for ix in ids:
       fixed=set(anchors[ix]['rm']);rest=sorted(set(range(n))-fixed)
       for h in range(len(fixed),4):
          for ext in itertools.combinations(rest,h-len(fixed)):
             if h==3 and len(fixed)==1 and not tips.intersection(ext):continue
             exp.add((seed,*sorted(fixed.union(ext))))
    assert exp=={x for x in unique if x[0]==seed}
 summary['principal_broader']={str(k):v for k,v in counts.items()}
 summary['joint_full_parent_ids']=[anchors[ii[0]]['seed'] for ii in per_word.values() if all(i in joint and joint[i][0]=='CLOSED' for i in ii)]
 summary['joint_status']=dict(collections.Counter(v[0] for v in joint.values()));summary['joint_rows_total']=len(anchors)
 summary['joint_by_cover']=[dict(i=i,seed=r['seed'],removed=r['rm'],result=joint.get(i)) for i,r in enumerate(anchors)]
 summary['affine_dual_forms_checked']=sum(q['dual_parity_checks'] for q in json.loads((D/'symmetry.json').read_text()))
 for h in (2,3):
    q=list(map(int,(D/f'joint_control{h}.txt').read_text().split()[1:]))
    for prefix in ('joint','early'):
       lines=(D/f'{prefix}_control{h}.log').read_text().splitlines();rm=list(map(int,next(l for l in lines if l.startswith('EXTRA ')).split()[1:]));w=verify(next(l for l in lines if l.startswith('FOUND ')),set(q)-set(rm),191);assert len(rm)==h-1 and len(w['new_input_points'])==h
 (D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='joint_by_cover'}))
if __name__=='__main__':main()
