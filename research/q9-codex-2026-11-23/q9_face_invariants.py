"""Distinguish minority vertex sets up to translations and coordinate permutations."""
from pathlib import Path
from collections import Counter
old=[list(map(int,l.split())) for l in open("q9_onechord_minority_sets.txt")]
def counts(p):
    look=set(p)
    return (sum((v^(1<<k)) in look for v in p for k in range(9))//2)-(len(p)-1)
def fingerprint(side):
    x=sorted(side); c=[0]*512
    for i,v in enumerate(x):
        for y in x[i+1:]:
            c[v^y]+=1
    return tuple(tuple(sorted(c[z] for z in range(1,512) if z.bit_count()==k)) for k in (2,4,6,8))
sigs={fingerprint(side) for side in old}
new=set();ones=set();representatives={}
for line in open("q9_face_donor_walks.txt"):
    p=list(map(int,line.split())); sig=fingerprint(p[1::2]);new.add(sig)
    chords=counts(p)
    if chords==1: ones.add(sig)
    if sig not in sigs and (sig not in representatives or chords < representatives[sig][0]):
        representatives[sig]=(chords,tuple(sorted(p[1::2])))
print("prior_signatures",len(sigs),"new_bank_signatures",len(new),"absent_from_prior",len(new-sigs),"one_chord_signatures",len(ones),"one_chord_absent_from_prior",len(ones-sigs),file=__import__("sys").stderr)

for _,side in sorted(representatives.values()):print(*side,file=__import__("sys").stdout)
