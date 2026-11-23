from bank import *
def rows(f):return [l.split() for l in (D/f).open()]
def done(f):
    z=rows(f)[-1];assert z[0]=='DONE',f;return list(map(int,z[1:]))
def legal(p):
    assert len(p)==len(set(p)) and all(0<=x<512 for x in p)
    assert all(((x^y).bit_count()==1)==(j==i+1) for j,y in enumerate(p) for i,x in enumerate(p[:j]))
def canonical(p):
    w=''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]));return min(normalize(w),normalize(w[::-1]))
with gzip.open(D.parent/'q9_port_followup_public191.txt.gz','rt') as f:public={canonical(list(map(int,l.split()))) for l in f}
base=json.loads((D/'audit.json').read_text());closure=json.loads((D/'closure_stats.json').read_text());both=json.loads((D/'joint_stats.json').read_text())
direct=done('transform.log');assert direct[1]==len(rows('sources.txt'))*(511*255)
assert closure['pending']==both['pending']==0
x={str(k):done(f'basis{k}.log' if k>3 else 'triple.log') for k in [3,4,5,6,7]}
multi={}
for n in ('outer','middle'):
    vals=done(n+'.log');multi[n]=dict(zip(['left_classes','placements','trie_nodes','deep_placements','geometry_classes','outer_nodes','longest_recorded'],vals))
    for row in rows(n+'.log'):
        if row[0]=='W':
            p=list(map(int,row[8:]));assert len(p)==int(row[1])+1;legal(p)
            if len(p)==192:multi[n]['best_matches_public']=canonical(p) in public
checks=rows('control_check.log')
out=dict(sources=base['source_count'],first_rank1=dict(cases=direct[1],reordered=direct[3],different_from_source=direct[4],changed_endpoints=direct[5],bank=direct[6]),rank1_fixed_point=closure,joint_fixed_point=both,total_rank1_maps=both['total']*511*255,high_rank_fields=['directions_replaced','source_classes','nodes','degree_patterns','connected_basis_records','capped_sources','new_classes'],high_rank=x,support8_full={'support_8_sources':len(rows('support8.txt')),'k7':done('support8_7.log'),'k8':done('support8_8_finish.log')},join_class_pairs_ordered=both['total']**2,join_prefix_nodes=sum(row[2] for row in base['join_stats']),witnesses_checked=base['validated_joins'],best=base['best'],best_191_public={k:canonical(z['path']) in public for k,z in json.loads((D/'best.json').read_text()).items() if z['length']==191},extension=multi,controls={'pairs':len(checks)//2,'placements_attempted_before':sum(int(z[2]) for z in checks[::2]),'before_hits':sum(int(z[3]) for z in checks[::2]),'restored_pairs':sum(int(z[3])>0 for z in checks[1::2]),'independent_small':json.loads((D/'small.json').read_text()),'full_gl_small':json.loads((D/'gl4.json').read_text())})
print(json.dumps(out,indent=2))
