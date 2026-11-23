from pathlib import Path
p=[0]
for c in Path('q9_reordered_segments_20261120/reference191.words').read_text().splitlines()[0]:p.append(p[-1]^(1<<int(c)))
for i in range(14,175):
    q=p.copy();q[i]=q[i-1]^q[i]^q[i+1]
    if len(set(q))!=len(q):continue
    bad=[(a,b) for a in range(len(q)) for b in range(a+2,len(q)) if (q[a]^q[b]).bit_count()==1]
    if len(bad)==1:
        print(*q)
        break
else: raise ValueError("no single-chord control")

