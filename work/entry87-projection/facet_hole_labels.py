"""Identify the one-hole symmetry classes containing each dense seven-cube shape."""
from collections import deque
import json
from pathlib import Path
from seven_deletions import full_classes, generators, IDENTITY


def hole_labels():
    records = json.loads(Path("seven-deletion-classes.json").read_bytes())
    masks = [sum(1 << v for v in r["forest"]) for r in records["64"]]
    gens = list(generators())
    labels = {}
    for group, (vertices, stabilizer, count) in enumerate(full_classes(masks)):
        fixed = sum(1 << v for v in vertices)
        homes = []
        for i, row in enumerate(records["63"]):
            if row["full_class"] != group:
                continue
            v, = row["deleted"]
            orbit = {v}
            queue = deque([v])
            while queue:
                x = queue.popleft()
                for gen in stabilizer:
                    y = gen[x]
                    if y not in orbit:
                        orbit.add(y)
                        queue.append(y)
            homes.append((i, orbit))
        assert sum(len(o) for _, o in homes) == len(set.union(*(o for _,o in homes))) == 64
        trans = {fixed: IDENTITY}
        queue = deque([fixed])
        while queue:
            mask = queue.popleft()
            for gen, act in gens:
                image = act(mask)
                if image not in trans:
                    trans[image] = trans[mask].translate(gen)
                    queue.append(image)
        assert len(trans) == count
        for mask, g in trans.items():
            groups = [(i, sum(1 << g[v] for v in orbit)) for i, orbit in homes]
            assert sum(bits for _, bits in groups) == mask and mask not in labels
            labels[mask] = groups
    assert len(labels) == 9424
    return labels
