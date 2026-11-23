"""Stream each distinct set after deleting one vertex from the candidate endpoint color."""
import sys
seen=set()
expand=[str(v+(256 if v.bit_count()%2 else 0)) for v in range(256)]
for l in open("q9_majority_exchange_sets.txt"):
    s=bytes(sorted(v&255 for v in map(int,l.split())))
    for j in range(len(s)):
        sub=s[:j]+s[j+1:]
        if sub in seen:continue
        seen.add(sub);print(" ".join(expand[v] for v in sub))
