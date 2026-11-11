from pathlib import Path
import json,collections
R=Path('E:/Snake-in-a-box');H=R/'milestones/188-dimensional-constructions'
seeds=json.loads((H/'data/lower-dimensional-seeds.json').read_text());bank=json.loads((R/'work/bank9.json').read_text())
def canon(p):
    ds=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    def norm(a):
        names={};return tuple(names.setdefault(x,len(names)) for x in a)
    return min(norm(ds),norm(ds[::-1]))
def projected(p,k):return [(v&((1<<k)-1))|((v>>(k+1))<<k) for v in p]
q8=seeds['8']['vertices'];segments={}
for length in range(90,99):
    segments[length]={canon(q8[start:start+length+1]):start for start in range(len(q8)-length)}
middle={};rows=[]
for index,row in enumerate(bank):
    p=row['vertex_sequence']
    for k in range(9):
        cuts=[i for i in range(len(p)-1) if p[i]^p[i+1]==1<<k]
        if len(cuts)!=2:continue
        a,b=cuts;q=projected(p[a+1:b+1],k);key=canon(q)
        middle.setdefault(key,len(middle))
        rows.append({'bank_index':index,'coordinate':k,'middle_length':len(q)-1,'middle_class':middle[key],
                     'middle_is_segment_of_published_98':key in segments.get(len(q)-1,{}),
                     'middle_vertices':q,'outer_lengths':[a,len(p)-2-b]})
out={'middle_classes':len(middle),'rows':rows,'class_summary':dict(collections.Counter((r['middle_length'],r['middle_class']) for r in rows))}
out['class_summary']={str(k):v for k,v in out['class_summary'].items()}
(H/'data/middle-ancestry.json').write_text(json.dumps(out,indent=2)+'\n')
(H/'scripts/ancestry.py').write_bytes(Path(__file__).read_bytes())
print('All two-crossing cuts',len(rows),'middle classes',len(middle),'is segment matches',sum(r['middle_is_segment_of_published_98'] for r in rows))
print(out['class_summary'])
