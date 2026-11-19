"""Index the long eight-dimensional arms for subsequent single-crossing rounds."""
import json

from survey import HERE, partner, save_json
from placements import shape


def main():
    source=partner.PREV/"donors.json"
    donors=json.loads(source.read_bytes())["shapes"]
    exemplars={shape(p):i for i,p in partner.parent_arms().items()}
    rows=[]
    seen=set()
    for index,record in enumerate(donors):
        path=record["path"]
        n=len(path)-1
        if n<96:
            continue
        partner.verify(path,8)
        key=shape(path)
        if key in seen or n>98:
            raise ValueError("Duplicate or oversized donor")
        seen.add(key)
        rows.append(dict(donor_index=index,edges=n,required_partner=191-n,
                         previous_96_class=exemplars.get(key),origin=record["origin"],
                         endpoints=[path[0],path[-1]],path=path))
    if len(rows)!=15 or set(exemplars)-seen or [sum(r["edges"]==k for r in rows) for k in (96,97,98)]!=[11,3,1]:
        raise ValueError("Unexpected donor inventory")
    document=dict(source_sha256=partner.digest(source),coding="Rows use the zero-based donor array index. Paths retain the saved orientation.",
                  remaining_96=[r["donor_index"] for r in rows if r["edges"]==96 and r["previous_96_class"] is None],
                  length_97=[r["donor_index"] for r in rows if r["edges"]==97],rows=rows)
    save_json(HERE/"parents.json",document)
    print("Five classified 96-edge shapes; remaining 96-edge donor indices",document["remaining_96"],
          "97-edge donor indices",document["length_97"])


if __name__=="__main__":
    main()
