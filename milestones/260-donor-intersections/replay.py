"""Independently count all 95 intersection indicators by adding bit columns."""
from collections import Counter
from census import HERE, bank, vertices, load, save, digest

def columns(indicators):
    levels=[list(indicators)]
    i=0
    while i<len(levels):
        row=levels[i]
        carry=[]
        while len(row)>=3:
            a,b,c=row.pop(),row.pop(),row.pop()
            xor=a^b
            carry.append((a&b)|(xor&c))
            row.append(xor^c)
        if len(row)==2:
            a,b=row
            row[:]=[a^b]
            carry.append(a&b)
        if carry: levels.append(carry)
        i+=1
    return [r[0] for r in levels]

if __name__=="__main__":
    from pathlib import Path
    reference=load(HERE/"minimum.json")
    catalogue=load(HERE/"catalogue.json")
    words={w:vertices(bytes.fromhex(w))[1:] for w in catalogue["words"]}
    maps=list(bank.permutation_images())
    for key,row in reference["rows"].items():
        forbidden=[bank.ALL_MAPS^mask for mask in bank.allowed_maps(row["parent"],maps)]
        target=row["minimum"]
        actual=set()
        for word,seq in words.items():
            bits=columns(forbidden[u] for u in seq)
            equal=bank.ALL_MAPS
            smaller=0
            for j in reversed(range(len(bits))):
                if (target>>j)&1:
                    smaller|=equal&~bits[j]
                    equal&=bits[j]
                else: equal&=~bits[j]
            if smaller: raise ValueError("Smaller intersection exists")
            while equal:
                k=equal & -equal
                actual.add((word,k.bit_length()-1))
                equal^=k
        if actual!=set(map(tuple,row["winners"])): raise ValueError("Winner list differs")
    save(HERE/"replay.json",dict(input_sha256=digest(HERE/"minimum.json"),source_sha256=digest(Path(__file__)),
        complete=True,rows=len(reference["rows"]),placements=reference["total_placements"],
        minima=Counter(r["minimum"] for r in reference["rows"].values()),
        optimal_placements=sum(len(r["winners"]) for r in reference["rows"].values())))
