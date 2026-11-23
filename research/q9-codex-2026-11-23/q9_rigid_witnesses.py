"""Recover a 191-edge witness containing each targeted catalogue entry verbatim."""
from pathlib import Path
import json

def decode(w):
    out=[0]
    for c in w:out.append(out[-1]^1<<int(c))
    return out

def compare(word,known):
    for row,original in enumerate(known):
        for reverse in (False,True):
            w=original[::-1] if reverse else original
            for offset in range(len(w)-len(word)+1):
                sample=w[offset:offset+len(word)]
                if len(set(sample))!=len(set(word)):continue
                mapping=dict(zip(sample,word))
                if len(set(mapping.values()))!=len(mapping) or any(mapping[a]!=b for a,b in zip(sample,word)):continue
                missing=set("012345678")-set(mapping)
                mapping.update(zip(sorted(missing),sorted(set("012345678")-set(mapping.values()))))
                p=decode("".join(mapping[c] for c in w))
                translation=p[offset];p=[v^translation for v in p]
                assert len(p)==len(set(p))==192
                assert p[offset:offset+len(word)+1]==decode(word)
                assert all(((v^u).bit_count()==1)==(i==j+1) for i,v in enumerate(p) for j,u in enumerate(p[:i]))
                return dict(record=row,reverse=reverse,offset=offset,vertices=p)
    raise ValueError("no witness")
if __name__=="__main__":
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    known=Path("q9_far189_spring_20261121/comparison191.words").read_text().split()
    result={i:compare(bank[i],known) for i in (43,44,464,472,576)}
    Path("q9_rigid_five_witnesses.json").write_text(json.dumps(result,indent=1)+"\n")
