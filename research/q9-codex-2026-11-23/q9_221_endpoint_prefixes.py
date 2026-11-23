def canonical_prefixes(dim, end_distance, steps):
    """One transition sequence per orbit of start-paths fixing both endpoints."""
    end = (1 << end_distance) - 1
    def extend(vertices, directions):
        if len(directions) == steps:
            yield tuple(directions)
            return
        used = set(directions)
        for group in (range(end_distance), range(end_distance, dim)):
            fresh = next((j for j in group if j not in used), None)
            for j in group:
                if j not in used and j != fresh:
                    continue
                w = vertices[-1] ^ (1 << j)
                # The distant endpoint must be available exclusively to the final edge.
                if (w ^ end).bit_count() <= 1:
                    continue
                if w in vertices or any((w ^ v).bit_count() == 1 for v in vertices[:-1]):
                    continue
                yield from extend([*vertices, w], [*directions, j])
    yield from extend([0], [])


if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser(description="Prefixes for the 221-edge Q9 target")
    p.add_argument("steps", type=int, choices=range(1, 220))
    p.add_argument("--list", action="store_true")
    a = p.parse_args()
    for d in (3, 5, 7, 9):
        rows = list(canonical_prefixes(9, d, a.steps))
        print(d, len(rows))
        if a.list:
            for row in rows:
                print(" ", *row)
