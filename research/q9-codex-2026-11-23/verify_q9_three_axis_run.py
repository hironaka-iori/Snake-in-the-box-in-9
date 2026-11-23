from collections import Counter
from pathlib import Path
import json

def verify(p):
    assert all(0<=v<512 for v in p) and len(set(p))==len(p)
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return sum((x^y).bit_count()==1 for j,x in enumerate(p) for y in p[:max(0,j-1)])
def decode(w):
    p=[0]
    for a in w:p.append(p[-1] ^ (1<<int(a)))
    return p
def shape(w):
    def renumber(text):
        d={}
        return tuple(d.setdefault(c,len(d)) for c in text)
    return min(renumber(w),renumber(w[::-1]))
def main():
    words=Path('q9_three_axis.in').read_text().splitlines()
    assert len({shape(w) for w in words})==len(words)
    counts=Counter(verify(decode(w)) for w in words)
    direct=Path('q9_three_axis.log').read_text().splitlines()[-1].split()
    assert direct[0]=='DONE'
    rows,cases,found,cutoffs,nodes=map(int,direct[1:])
    assert rows==len(words) and cases==84*rows and found==cutoffs==0
    reference=Path('q9_three_axis_191.in').read_text().splitlines()
    assert len(reference)==131 and all(len(w)==191 and verify(decode(w))==0 for w in reference)
    c=Path('q9_three_axis_insert_control.log').read_text().split()
    assert c[0]=='FOUND' and c[3]=='191'
    p=list(map(int,c[4:]));assert len(p)==192 and verify(p)==0
    report=dict(candidate_classes=len(words),extra_chords=dict(counts),axis_triples=84,completed_fixed_projection_checks=cases,unresolved=cutoffs,
       clean_192=found,independently_rechecked_true_191_inputs=len(reference),insert_control_verified_edges=len(p)-1,
       small_control=Path('q9_three_axis_repair_control.log').read_text().strip(),
       source='q9_three_axis.in')
    done=Path('q9_three_axis_insert.log').read_text().splitlines()[-1].split()
    expected=len(reference)*84*(7*192-191)
    assert done==['DONE',str(len(reference)),str(expected),'0',str(len(reference)*84*191)]
    report['insert_projection_checks']=dict(true_191_sources=len(reference),
        cases_after_skipping_repeated_insertions=expected,unsolved=0,valid_192=0)
    Path('q9_three_axis_verified.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))
if __name__=='__main__':main()
