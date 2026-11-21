"""Enumerate every one-edge extension of each arm in the two closed components."""
from pathlib import Path
import json
from hashlib import sha256
from geometry import extensions
from enumerate_arms import HERE, check_path, digest, word


def main():
    result = {}
    pins = {}
    for component in ("focus","attainer"):
        source = HERE / (component+"-closure.json")
        data = json.loads(source.read_bytes())
        if not data["closed"]:
            raise ValueError("Component is incomplete")
        pins[source.name] = digest(source)
        rows = {}
        for key, seq in data["paths"].items():
            check_path(seq)
            paths = sorted(set(extensions(tuple(seq))))
            # Check even the rejected slots by the independent pairwise criterion.
            direct = set()
            for orientation in (seq,seq[::-1]):
                for i in range(8):
                    trial = orientation + [orientation[-1] ^ (1<<i)]
                    try:
                        check_path(trial)
                    except ValueError:
                        continue
                    direct.add(tuple(min(trial,trial[::-1])))
            if set(paths) != direct:
                raise ValueError("Extension lists differ")
            rows[key] = [dict(vertices=p,shape=sha256(word(p)).hexdigest()) for p in paths]
        result[component] = rows
    pins.update({p.name:digest(p) for p in [Path(__file__),HERE/"geometry.py"]})
    (HERE/"extension-boundary.json").write_text(json.dumps(dict(pins=pins,components=result),indent=2)+"\n",
                                              encoding="utf-8",newline="\n")
    print({k:sum(map(len,v.values())) for k,v in result.items()})


if __name__ == "__main__":
    main()
