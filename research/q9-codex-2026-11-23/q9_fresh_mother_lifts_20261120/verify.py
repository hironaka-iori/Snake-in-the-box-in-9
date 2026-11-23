"""Check the delivered bank, recover the last search status per mother, and verify the Q9 controls."""
from collections import Counter
from pathlib import Path
import json
import runpy

here = Path(__file__).resolve().parent
original = runpy.run_path(str(here.parent / "q8_mother_search_20261120" / "verify.py"))
validate, vertices, canonical, rooted = (original[k] for k in ("valid", "vertices", "canonical", "rooted_subwords"))

def words(file):
    return set((here / file).read_text().split())

bank = words("q8_base726_all20.words")
fresh = words("q8_novel1626_95_20.words")
assert len(fresh) == 1626
assert all(len(word) == 95 and word == canonical(word) and validate(vertices(word), 8) for word in fresh)
known_substrings = {canonical(w) for w in bank if len(w) == 95}
assert fresh.isdisjoint(known_substrings)
arms = set().union(*(rooted(w) for w in fresh)) - bank
assert arms == words("q8_novel1626_95roots20.words")
results = {}
for name in ["q9_q7out_new95a20","q9_q7out_new95b20","q9_q7ref_reopen_a20","q9_q7ref_reopen_b20"]:
    for line in (here / (name+".log")).read_text().splitlines():
        tag, _, word, total, closed, unknown, found, *_ = line.split()
        assert tag == "DONE"
        assert int(total) == int(closed) and int(found) == 0 if "ref_reopen" in name else int(total)==int(closed)+int(unknown)+int(found)
        results[word] = tuple(map(int, (total,closed,unknown,found)))
assert results.keys() == fresh
large = words("q9_55mother20.words")
extra = [s.split() for s in (here/"q9_q7outside_family20.log").read_text().splitlines() if s.split()[2] in large]
counts = tuple(map(sum,zip(*results.values())))
counts96 = tuple(sum(int(s[i]) for s in extra) for i in range(3,7))
assert counts == (7478,7478,0,0) and counts96 == (312,312,0,0)
controls = {}
for name in ("q9_q7ref_control20","q9_onefree_pos20"):
    line = (here/(name+".log")).read_text().splitlines()[0].split()
    path = list(map(int,line[5:]))
    assert line[0]=="FOUND" and len(path)==int(line[3])+1 and validate(path,9)
    controls[name] = len(path)-1
print(json.dumps(dict(new95=len(fresh),new_rooted_arms=len(arms),length_distribution=dict(Counter(map(len,arms))),two_facets_95=counts,two_facets_96=counts96,controls=controls),indent=2))
