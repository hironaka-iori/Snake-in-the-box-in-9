"""Seek a new endpoint on an unblocked 191 record and allow all local blockers to move."""
from pathlib import Path
import json,random
from q9_intact_bank_search import search,verify,word_path
from q9_classify_record_donor_windows import canonical
def main():
    rng=random.Random(286215)
    archive=Path("q9_far189_spring_20261121/comparison191.words").read_text().split()
    prior=json.loads(Path("q9_record_facet_window_classes.json").read_text())
    checked=json.loads(Path("q9_frequent_95_audit.json").read_text())
    assert checked["remaining"]==0
    skip=set(checked["record_ids"]).union(*prior["donor_record_ids"].values())
    assert len(skip)==109
    jobs=[]
    for i,w in enumerate(archive):
        if i in skip:continue
        p=word_path(w);assert len(p)==192 and verify(p)
        for side,ep in enumerate([p[0],p[-1]]):
            for d in range(9):
                y=ep^1<<d
                if y in p:continue
                blockers={v for v in p if v!=ep and (v^y).bit_count()==1}
                assert blockers
                jobs.append((i,side,ep,y,blockers,p))
    rng.shuffle(jobs)
    for radius in (2,3):
        for i,side,ep,y,blockers,p in jobs:
            release={v for v in p if any((v^b).bit_count()<=radius for b in blockers)}-{ep}
            assert blockers<=release
            near=set(p)-blockers
            branches=search(p,192,35000,near,{y},False,omit=release,forbid=blockers)
            print(json.dumps(dict(archive=i,side=side,new_vertex=y,conflicts_with=sorted(blockers),release=len(release),radius=radius,branches=branches)),flush=True)
            if any(b["status"]=="FOUND" for b in branches):return
if __name__=="__main__":main()
