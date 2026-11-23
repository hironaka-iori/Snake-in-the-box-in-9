"""Close Q8 snake windows with a single new vertex and check the resulting induced cycles."""
from collections import Counter
import json
from pathlib import Path
from verify_q9_center_avoidance import code
if __name__=="__main__":
    bank={}
    for f in ["q8_combined_exchange_arms.txt","q8_exchange_second_rooted_arms.txt","q8_two_crossing_middle_seeds.txt"]:
        for w in Path(f).read_text().split():
            for length in (94,92):
                for i in range(len(w)-length+1):
                    z=w[i:i+length];p=[0]
                    for c in z:p.append(p[-1]^1<<int(c))
                    if p[-1].bit_count()!=2:continue
                    for d in range(8):
                        v=1<<d
                        if (p[-1]^v).bit_count()!=1 or v in p or any((v^u).bit_count()==1 for u in p[1:-1]):continue
                        cycle=p+[v]
                        assert all(((x^cycle[j]).bit_count()==1)==(j==k+1 or (k==0 and j==len(cycle)-1))
                                   for k,x in enumerate(cycle) for j in range(k+1,len(cycle)))
                        t=list(map(int,z))+[(p[-1]^v).bit_length()-1,d]
                        key=min(code(t[j:]+t[:j]) for j in range(len(t)))
                        bank[key]="".join(map(str,key))
    words=sorted(bank.values(),key=lambda w:(-len(w),w))
    Path("q8_coils_reconstructed.txt").write_text("\n".join(words)+"\n")
    print(json.dumps(Counter(map(len,words))))
