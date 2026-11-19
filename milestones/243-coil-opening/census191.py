"""Find and identify record-length paths reached from the long coil arcs."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json

from open_coil import ADJ, ALL, HERE, bits, verify, vertices


def signature(path):
    transitions = [u ^ v for u, v in zip(path, path[1:])]
    def renamed(word):
        names = {}
        return bytes(names.setdefault(x,len(names)) for x in word)
    return min(renamed(transitions), renamed(reversed(transitions)))


def main():
    coil = json.loads((HERE/"coil9.json").read_bytes())["q9_rows"][0]["vertices"]
    verify(coil, True)
    bank_file = HERE.parents[1]/"work/bank9.json"
    bank = {signature(r["vertex_sequence"]):i for i,r in enumerate(json.loads(bank_file.read_bytes()))}
    if len(bank) != 131:
        raise ValueError("Bank normalization")
    proof = json.loads((HERE/"arc-160-5000000.json").read_bytes())
    found = {}
    rows = []
    for row in proof["rows"]:
        start = row["start"]
        # Reverse the anchored arc and generate right tails before left tails.
        spine = [coil[(start+j)%192] for j in reversed(range(160))]
        fixed = bits(spine)
        first = []
        for e in (spine[0],spine[-1]):
            first.append([v for v in vertices(ADJ[e]) if not (1<<v)&fixed and ADJ[v]&fixed == 1<<e])
        free = ALL
        for v in spine:
            free &= ~(ADJ[v]|(1<<v))
        left, right = [], []
        totals = Counter()
        def grow(is_left, options, available, right_ports):
            if len(left) + len(right) == 32:
                path = left[::-1]+spine+right
                key = signature(path)
                if key not in found:
                    verify(path,False)
                    found[key] = dict(bank_id=bank.get(key), path=path)
                totals[key] += 1
                return
            if is_left:
                grow(False,right_ports,available,0)
            tail = left if is_left else right
            for v in vertices(options):
                tail.append(v)
                closed = ADJ[v] | (1<<v)
                grow(is_left, ADJ[v] & available, available & ~closed, right_ports & ~closed)
                tail.pop()
        grow(True, bits(first[0]), free, bits(first[1]))
        rows.append(dict(start=start, placements=sum(totals.values()),
                         classes={k.hex():v for k,v in totals.items()}))
    record = dict(source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  bank_sha256=sha256(bank_file.read_bytes()).hexdigest(),
                  classes=[dict(signature=k.hex(),**v) for k,v in sorted(found.items())],
                  starts=rows)
    (HERE/"record-census.json").write_text(json.dumps(record,separators=(",",":"))+"\n",
                                           encoding="utf-8",newline="\n")
    print("classes",len(found),"nonbank",sum(r["bank_id"] is None for r in found.values()),
          "placements for the 96 representatives",sum(r["placements"] for r in rows))


if __name__ == "__main__":
    main()
