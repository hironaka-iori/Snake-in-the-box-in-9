"""Reproduce the additional boundary and joint-sum probes recorded in this round."""
from probe import solve
for name,caps in [
 ('third-with-first',[3,21,4,21,21,21,21]),
 ('third-with-last',[21,21,4,21,21,21,3]),
 ('sixth-with-first',[3,21,21,21,21,3,21]),
 ('sixth-with-last',[21,21,21,21,21,3,3]),
 ('third-boundary',[3,21,5,21,21,21,3]),
 ('sixth-boundary',[3,21,21,21,21,4,3])]:solve(name,caps)
for k in range(5,9):solve('sixth-cap-'+str(k),[3,21,21,21,21,k,3])
for k in [24,25,26,27,28,30]:solve('middle-sum-'+str(k),[3,21,21,21,21,21,3],seconds=12,joint=(list(range(2,7)),k))
for k in [10,11,12]:solve('two-middle-sum-'+str(k),[3,21,21,21,21,21,3],seconds=10,joint=([3,6],k))
solve('first-third-last-sum-10',[21]*7,seconds=12,joint=([1,3,7],10))
solve('first-sixth-last-sum-10',[21]*7,seconds=12,joint=([1,6,7],10))
solve('first-sixth-last-sum-11',[21]*7,seconds=12,joint=([1,6,7],11))
