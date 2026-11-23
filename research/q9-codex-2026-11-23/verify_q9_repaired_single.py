import sys,json
from collections import defaultdict
from pathlib import Path
from verify_q9_excused_edge import key,chords,vertices,word
from verify_q9_onechord_equivalence import fingerprint,iso
source=Path(sys.argv[1]);out=Path(sys.argv[2])
old=[list(map(int,l.split())) for l in open("q9_onechord_expanded_800.txt")]
known={key(word(p)) for p in old}
new=source.read_text().splitlines();assert len(new)==len(set(map(key,new))) and known.isdisjoint(map(key,new))
p=[vertices(w) for w in new];assert all(len(chords(t))==1 for t in p)
summary={};out.with_suffix(".vertices").write_text("".join(" ".join(map(str,t))+"\n" for t in p))
for offset in (0,1):
    library={tuple(sorted(t[offset::2])) for t in old}
    by=defaultdict(list)
    for s in library:by[fingerprint(s)].append(s)
    fresh={tuple(sorted(t[offset::2])) for t in p};matches=0;newclasses=[]
    for s in sorted(fresh):
        fp=fingerprint(s)
        if any(iso(s,ref) for ref in by[fp]):matches+=1
        elif not any(fingerprint(ref)==fp and iso(s,ref) for ref in newclasses):newclasses.append(s)
    Path(str(out)+f".novel{97-offset}").write_text("".join(" ".join(map(str,s))+"\n" for s in newclasses))
    summary[97-offset]=dict(raw=len(fresh),matches_original=matches,inequivalent_outside_original=len(newclasses))
    Path(str(out)+f".side{97-offset}").write_text("".join(" ".join(map(str,s))+"\n" for s in sorted(fresh)))
print(json.dumps(dict(single_chord_walk_classes=len(p),original_walk_classes=len(known),sides=summary),indent=2))
