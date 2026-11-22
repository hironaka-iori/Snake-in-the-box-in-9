"""Find compatible donor segments at both ends and grow the best placement freely."""
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
spec = spec_from_file_location("tails", MS / "257-three-exchange-parents/construct.py")
tails = module_from_spec(spec)
spec.loader.exec_module(tails)
bank = tails.bank
sys.path.insert(0, str(MS / "252-shorter-reference-segments"))
from replay_core import word


def main():
    sources = [MS / "255-parity-exchange-arms/partner-pool.json",
               MS / "255-parity-exchange-arms/constructive.json",
               MS / "248-rooted-arm-capacity/attainers.json",
               MS / "257-three-exchange-parents/constructed-51.json",
               HERE / "new-arms.json"]
    pool, previous, attaining, recent, arms = map(tails.load, sources)
    paths = list(pool["shapes"].values()) + [r["partner"] for r in previous["cases"].values()]
    paths += [r["vertices"] for r in previous["donors"]]
    paths += [p["path"] for r in attaining["records"] for p in r["paths"]]
    paths += [r["partner"] for r in recent["cases"].values()]
    donors = list({word(p): p for p in paths}.values())
    words, origins = bank.donor_suffixes(donors)
    images = list(bank.permutation_images())
    result = {}
    for shape, arm in arms["shapes"].items():
        for order in (arm, arm[::-1]):
            parent = [v ^ order[0] for v in order]
            allowed = bank.allowed_maps(parent, images)
            match = bank.longest(words, allowed)
            donor = bank.make_witness(donors, origins[match[1]], match, parent)
            exclusion = bank.exclude_next(donors, words, allowed, match[0]+1)
            prefix = donor["partner"][:max(12, len(donor["partner"])-8)]
            partner, nodes = tails.follow(prefix, parent)
            if tails.replay_tail(prefix, parent) != (nodes, len(partner)-1):
                raise ValueError("Continuation replay disagrees")
            joined = parent[::-1] + [v+256 for v in partner]
            result[str(order[0])] = dict(shape=shape, parent=parent, donor=donor, next_length=exclusion,
                prefix=prefix, continuation_nodes=nodes, partner=partner, joined=joined,
                joined_edges=len(joined)-1, verified_pairs=bank.check_path(joined, 9))
            print(order[0], match[0], len(partner)-1, len(joined)-1, nodes, flush=True)
    data = dict(donor_shapes=len(donors), cases=result, inputs={p.name:sha256(p.read_bytes()).hexdigest()
                for p in [*sources, Path(__file__), Path(spec.origin), Path(bank.__file__)]})
    (HERE / "constructed.json").write_text(json.dumps(data)+"\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
