from pathlib import Path
import json,subprocess
def vertices(word):
    p=[0]
    for c in word:p.append(p[-1]^1<<int(c))
    return p
def word(p):return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
def key(w):
    def one(w):
        order=list(dict.fromkeys(w));return tuple(order.index(d) for d in w)
    return min(one(w),one(w[::-1]))
def chords(p):
    assert len(p)==len(set(p))==193 and all(0<=v<512 for v in p)
    assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    return {(j,i) for i,x in enumerate(p) for j in range(i-1) if (p[j]^x).bit_count()==1}
def main():
    old=list(map(int,open("q9_onechord_expanded_800.txt").readline().split()));c=chords(old);assert len(c)==1
    cases=[]
    for i in range(1,192):
        q=old.copy();q[i]=q[i-1]^q[i]^q[i+1]
        if len(set(q))!=193:continue
        d=chords(q)
        if len(d)==2 and c<=d:cases.append(q)
        if len(cases)==8:break
    assert cases
    out=Path("/tmp/q9_one_edge_check_out.words")
    inp="".join(f"2 {word(p)}\n" for p in cases)
    rows=subprocess.check_output(["/tmp/q9excused21","2","0","/dev/null",str(out)],input=inp,text=True).splitlines()
    assert len(rows)==len(cases) and all(line.startswith("ROW ") and int(line.split()[4])==0 for line in rows)
    repaired=out.read_text().splitlines();assert repaired and key(word(old)) in set(map(key,repaired))
    assert all(len(chords(vertices(w)))==1 for w in repaired)
    print(json.dumps(dict(damaged_cases=len(cases),recovered_original=True,verified_single_chord_classes=len(repaired))))
if __name__=="__main__":main()
