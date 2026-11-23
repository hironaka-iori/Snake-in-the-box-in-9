"""Verify and deduplicate SAT constructions before testing both-end extensions."""
import json
from q9_avoiding_centers import reference,windows
from search_q9_two_flexible_ends import verify

bank=reference(142);seen=set()
for row in map(json.loads,open('q9_avoiding_sat_results.jsonl')):
    status,mask,n,p=row
    if status!='FOUND':continue
    verify(p,n);assert len(p)==n+1
    assert not(bank & set(windows(p,142)))
    key=windows(p,n)[0]
    if key in seen:continue
    seen.add(key)
    print(*p)
