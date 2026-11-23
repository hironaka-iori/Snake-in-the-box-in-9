from pathlib import Path
p=[0]
for c in Path("q9_reordered_segments_20261120/reference191.words").read_text().splitlines()[0]: p.append(p[-1]^(1<<int(c)))
def turn(q,k,a,b):
    return [v^((1<<a)|(1<<b)) if i<k and (((v^q[k])>>a^(v^q[k])>>b)&1) else v for i,v in enumerate(q)]
q=turn(turn(p,4,4,3)[::-1],4,3,1)[::-1]
print(2,''.join(str((a^b).bit_length()-1) for a,b in zip(q,q[1:])))

