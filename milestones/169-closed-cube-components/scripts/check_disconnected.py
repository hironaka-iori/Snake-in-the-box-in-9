import json
from pathlib import Path
results=[]
for a in range(1,5):
    b=9-a
    pairs=[]
    for i in range(a):
        js=range(a,9) if i%2==0 else range(8,a-1,-1)
        pairs.extend((1<<i)|(1<<j) for j in js)
    snake=[]
    for i,v in enumerate(pairs):
        if i:snake.append(pairs[i-1]|v)
        snake.append(v)
    assert len(set(snake))==len(snake)
    for i,u in enumerate(snake):
        for j in range(i+1,len(snake)):
            assert ((u^snake[j]).bit_count()==1)==(j==i+1)
    assert all(v.bit_count()>1 for v in snake)
    missing=[(i,j) for i in range(9) for j in range(i+1,9) if ((1<<i)|(1<<j)) not in snake]
    expected=[(i,j) for i in range(9) for j in range(i+1,9) if (i<a)==(j<a)]
    assert missing==expected
    assert len(snake)-1==2*a*b-2
    results.append(dict(component_sizes=[a,b],edges=len(snake)-1,empty_squares_at_zero=len(missing),vertices=snake))
p=Path(__file__).resolve().parents[1]/'data/disconnected-witnesses.json'
p.write_text(json.dumps(dict(status='PASS',checks='Distinct vertices, all pairwise cube adjacencies, undominated zero, and exact missing-pair graph',examples=results),indent=2)+'\n')
print([(r['edges'],r['empty_squares_at_zero']) for r in results])
