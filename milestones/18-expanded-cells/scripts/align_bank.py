"""Align known snakes with the alternating cell palette by cube symmetries.

Enumerates 126 inner-coordinate sets and 5!*32*2 palette orientations.
Outer coordinate permutations and even outer translations preserve membership.
"""
import hashlib
import itertools
import json
from pathlib import Path
import time
import numpy as np

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]

def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()

def transform(v, inner, perm, shift, flip):
    outer=[i for i in range(9) if i not in inner]
    return (sum(((v>>inner[perm[j]])&1)<<j for j in range(5)) ^ shift) | (
        (sum(((v>>outer[j])&1)<<j for j in range(4)) ^ flip)<<5)


def main():
    start=time.monotonic()
    bank_path=ROOT/'work/bank9.json'
    base_path=ROOT/'milestones/16-cycle-reservoirs/data/base5-size14.json'
    bank=json.loads(bank_path.read_text())
    bases=json.loads(base_path.read_text())['base_sets']
    holes=set(range(32))-set(bases[0])-set(bases[1])
    palettes=[set(b)|holes for b in bases]
    patterns={}
    for perm in itertools.permutations(range(5)):
        mapping=[sum(((b>>perm[j])&1)<<j for j in range(5)) for b in range(32)]
        for shift in range(32):
            for flip in range(2):
                row=bytes(int((mapping[b]^shift) not in palettes[p^flip]) for p in range(2) for b in range(32))
                patterns.setdefault(row,(perm,shift,flip))
    metadata=list(patterns.values())
    matrix=np.array([list(p) for p in patterns],dtype=np.int16)
    best=[193]*len(bank); records=[None]*len(bank)
    for inner in itertools.combinations(range(9),5):
        outer=[i for i in range(9) if i not in inner]
        hist=np.zeros((64,len(bank)),dtype=np.int16)
        for k,entry in enumerate(bank):
            for v in entry['vertex_sequence']:
                b=sum(((v>>inner[j])&1)<<j for j in range(5))
                p=sum((v>>j)&1 for j in outer)%2
                hist[p*32+b,k]+=1
        counts=matrix@hist
        indices=counts.argmin(axis=0)
        for k,index in enumerate(indices):
            value=int(counts[index,k])
            if value < best[k]:
                best[k]=value;perm,shift,flip=metadata[index]
                records[k]={'bank_index':k,'outside_count':value,'inner_coordinates':list(inner),
                            'inner_permutation':list(perm),'inner_shift':shift,'outer_shift':flip}
    canonical={h*32+v for h in range(16) for v in palettes[h.bit_count()%2]}
    for r in records:
        path=[transform(v,r['inner_coordinates'],r['inner_permutation'],r['inner_shift'],r['outer_shift'])
              for v in bank[r['bank_index']]['vertex_sequence']]
        assert len(path)==192 and len(set(path))==192
        for j,v in enumerate(path):
            for i,w in enumerate(path[:j]):assert ((v^w).bit_count()==1)==(i+1==j)
        outside=sorted(set(path)-canonical)
        assert len(outside)==r['outside_count']
        r.update(path_vertices=path,outside_vertices=outside)
    out={'scope':'Minimum outside-palette counts for this finite published bank, over the enumerated symmetry representatives. No new snake or global bound.',
         'bank_sha256_lf':sha(bank_path),'base_sha256_lf':sha(base_path),'script_sha256_lf':sha(Path(__file__)),
         'raw_orientations_per_coordinate_set':7680,'distinct_palette_patterns':len(patterns),
         'inner_coordinate_sets':126,'minimum_outside_count':min(best),'maximum_bank_minimum':max(best),
         'records':records,'elapsed_seconds':time.monotonic()-start}
    (HERE/'data').mkdir(parents=True,exist_ok=True)
    (HERE/'data/bank-alignments.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    chosen=min(records,key=lambda r:r['outside_count'])
    (HERE/'data/aligned-seed.json').write_text(json.dumps({**chosen,'seed_vertices':chosen['path_vertices'],
          'source_sha256_lf':sha(HERE/'data/bank-alignments.json')},indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:out[k] for k in ('distinct_palette_patterns','minimum_outside_count','maximum_bank_minimum','elapsed_seconds')}),flush=True)
    print('Selected bank index',chosen['bank_index'],flush=True)


if __name__=='__main__':main()
