from pathlib import Path
s=Path("q9_three_axis_191.in").read_text().splitlines()[0]
p=[0]
for x in s:p.append(p[-1]^(1<<int(x)))
q=p[:]
for i in (9,57,101,185):q[i]=p[i-1]^p[i]^p[i+1]
assert len(set(q))==len(q)
print(''.join(str((a^b).bit_length()-1) for a,b in zip(q,q[1:])))
for i in (105,137,15,75):
    q=p[:];q[i]=q[i-1]^q[i]^q[i+1]
    assert len(set(q))==len(q) and sum((x^q[j]).bit_count()==1 for t,x in enumerate(q) for j in range(t+2,len(q)))==1
    print(''.join(str((a^b).bit_length()-1) for a,b in zip(q,q[1:])))

