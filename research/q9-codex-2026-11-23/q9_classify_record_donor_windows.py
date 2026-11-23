from pathlib import Path
from collections import defaultdict
import json

def canonical(w):
    def relabel(s):
        mapping={}
        return "".join(str(mapping.setdefault(c,len(mapping))) for c in s)
    return min(relabel(w),relabel(w[::-1]))

def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    archive=Path("q9_far189_spring_20261121/comparison191.words").read_text().split()
    ids={canonical(w):i for i,w in enumerate(bank)}
    assert len({canonical(w) for w in archive})==len(archive)==131
    included=defaultdict(set);longest={};unmatched=[]
    for i,w in enumerate(archive):
        longest[i]=max(len(seg) for axis in "012345678" for seg in w.split(axis))
        for length in (96,97,98):
            for j in range(len(w)-length+1):
                seg=w[j:j+length]
                if len(set(seg))==9:continue
                match=ids.get(canonical(seg))
                if match is None:unmatched.append([i,j,length])
                else:included[match].add(i)
    print(json.dumps(dict(records=len(archive),max_facet_run_histogram={k:list(longest.values()).count(k) for k in sorted(set(longest.values()))},
                          donor_record_ids={k:sorted(v) for k,v in sorted(included.items())},records_matching=len(set.union(*included.values())),
                          unclassified_96_to_98_windows=unmatched),indent=2))
if __name__=="__main__":main()
