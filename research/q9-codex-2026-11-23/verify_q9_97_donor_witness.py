"""Independently check the nine-cube edges, lack of chords, and 97-edge donor membership."""
import json
from pathlib import Path
from verify_q9_97_donor_ports import donors,normalize,check
p=Path('q9_97_donor_verified_witness.json');r=json.loads(p.read_text());q=r['q9_vertices']
check(len(q)==r['edges']+1 and len(set(q))==len(q)==r['unique_vertices'],'vertex count mismatch')
check(all(type(x) is int and 0<=x<512 for x in q),'off-cube vertex')
check(all((x^y).bit_count()==1 for x,y in zip(q,q[1:])),'non-unit consecutive step')
chords=sum((x^y).bit_count()==1 for i,x in enumerate(q) for y in q[i+2:])
check(chords==r['chords']==0,'chord')
word=''.join(str((x^y).bit_length()-1) for x,y in zip(q,q[1:]))
check(word==r['transition_word'],'transitions disagree')
bank=donors();hits=[]
for j in range(len(word)-96):
    w=word[j:j+97]
    if len(set(w))<=8:
        key=min(normalize(w),normalize(w[::-1]))
        if key==r['donor_shape'] and key in bank:hits.append(j)
check(hits and r['donor_edges']==97,'specified included donor not found')
print(json.dumps(dict(edges=len(q)-1,distinct_vertices=len(set(q)),chords=chords,donor97_start_indices=hits)))
