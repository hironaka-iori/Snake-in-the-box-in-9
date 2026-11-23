"""Count facet visits for the saved 191-edge class bank and compare with the Q8 catalogue."""
import gzip
import json
from collections import Counter
from pathlib import Path


def canonical(steps):
    def relabel(word):
        axes = {}
        return ''.join(str(axes.setdefault(x, len(axes))) for x in word)
    return min(relabel(steps), relabel(steps[::-1]))


def profile():
    records = {}
    with gzip.open('q9_free_bridge_join_inputs.txt.gz', 'rt') as stream:
        for line in stream:
            vertices = list(map(int, line.split()))
            if len(vertices) == 192:
                steps = [(u ^ v).bit_length() - 1 for u, v in zip(vertices, vertices[1:])]
                records[canonical(steps)] = (vertices, steps)
    assert len(records) == 131
    catalogue = set(Path('q8_catalogue_96_98.words').read_text().split())
    gaps, crossings, hits = Counter(), Counter(), 0
    for vertices, steps in records.values():
        assert len(set(vertices)) == 192 and all(0 <= v < 512 for v in vertices)
        assert all(((vertices[j] ^ v).bit_count() == 1) == (j == i + 1)
                   for i, v in enumerate(vertices) for j in range(i + 1, len(vertices)))
        longest, contains = 0, False
        for axis in range(9):
            cuts = [-1] + [i for i, x in enumerate(steps) if x == axis] + [len(steps)]
            for a, b in zip(cuts, cuts[1:]):
                longest = max(longest, b - a - 1)
                for i in range(a + 1, b - 95):
                    if canonical(steps[i:i+96]) in catalogue:
                        contains = True
        gaps[longest] += 1
        crossings[min(steps.count(axis) for axis in range(9))] += 1
        hits += contains
    return dict(classes=len(records), longest_single_facet_run=dict(sorted(gaps.items())),
                minimum_crossings_in_one_coordinate=dict(sorted(crossings.items())),
                containing_a_catalogued_96=hits)


if __name__ == '__main__':
    print(json.dumps(profile(), indent=2))

