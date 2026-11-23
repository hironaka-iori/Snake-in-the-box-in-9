"""Check a 191-edge Q9 witness, all pair distances, and its intact Q8 donor."""
import json
from pathlib import Path
from verify_q9_96_donor_coverage import canonical, check

def main():
    a=json.loads(Path('q9_96_donor_191_witness.json').read_text())
    p=a['q9_vertices']
    check(a['dimension']==9 and a['edges']==len(p)-1==191, 'wrong size')
    check(len(set(p))==len(p) and all(type(v) is int and 0<=v<512 for v in p),'bad vertex')
    for i,v in enumerate(p):
        for j in range(i+1,len(p)):
            check(((v^p[j]).bit_count()==1)==(j==i+1),'not an induced path')
    word=''.join(str((v^u).bit_length()-1) for v,u in zip(p,p[1:]))
    check(word==a['transition_word'],'word differs from the witness')
    j=a['donor_start'];check(a['donor_edges']==96 and 0<=j<=95,'invalid donor index')
    sub=word[j:j+96];mask=1<<a['unused_coordinate']
    check(len(set(sub))==8 and len({v&mask for v in p[j:j+97]})==1,'not contained in a Q8 face')
    donor=canonical(sub)
    check(donor==a['donor_shape'] and donor in Path('q8_catalogue_96_98.words').read_text().split(),'donor not in catalogue')
    print(json.dumps(dict(edges=191,distinct_vertices=len(set(p)),pairs_checked=len(p)*(len(p)-1)//2,chords=0,donor_start=j,donor_edges=96,fixed_axis=a['unused_coordinate'])))
if __name__=='__main__':main()
