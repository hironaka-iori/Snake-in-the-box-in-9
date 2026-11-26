"""Enumerate induced Q8 paths containing prescribed vertices of an ordered Q8 seed.

The result uses fixed vertex labels 0..255. A path and its reversal are one
result. Keys indicate absent positions of the original seed. Lengths count edges.
"""

from itertools import combinations

NEIGHBORS = tuple(
    sum(1 << (vertex ^ (1 << axis)) for axis in range(8))
    for vertex in range(256)
)
CUBE = (1 << 256) - 1


def _neighbors(vertices):
    result = 0
    while vertices:
        vertex = vertices & -vertices
        vertices ^= vertex
        result |= NEIGHBORS[vertex.bit_length() - 1]
    return result


def _components(occupied):
    components = []
    unseen = occupied
    while unseen:
        front = unseen & -unseen
        component = 0
        while front:
            component |= front
            unseen ^= front
            front = _neighbors(front) & unseen
        components.append(component)
    return tuple(components)


def _ordered_path(occupied, tips):
    node = tips & -tips
    path = []
    previous = 0
    while node:
        vertex = node.bit_length() - 1
        path.append(vertex)
        following = NEIGHBORS[vertex] & occupied & ~previous
        previous, node = node, following
    return tuple(path)


def _enumerate_mask(original, retained, minimum, maximum):
    results = set()
    size = retained.bit_count()
    if size > maximum:
        return results

    degree_zero = 0
    degree_one = 0
    unavailable = original
    cursor = retained
    while cursor:
        bit = cursor & -cursor
        cursor ^= bit
        neighbors = NEIGHBORS[bit.bit_length() - 1]
        degree = (retained & neighbors).bit_count()
        if degree == 0:
            degree_zero |= bit
        elif degree == 1:
            degree_one |= bit
        else:
            unavailable |= neighbors

    available = CUBE & ~unavailable
    fringe = available & _neighbors(degree_zero | degree_one)
    seen = {retained}

    def visit(occupied, zero, one, allowed, fringe, parts, size):
        if len(parts) == 1 and size >= minimum:
            results.add(_ordered_path(occupied, zero | one))
        # A single addition can join at most two current components.
        if size == maximum or size + len(parts) - 1 > maximum:
            return
        if size + allowed.bit_count() < minimum:
            return
        if len(parts) > 1:
            for part in parts:
                if not (_neighbors(part & (zero | one)) & fringe):
                    return

        choices = fringe
        while choices:
            bit = choices & -choices
            choices ^= bit
            next_occupied = occupied | bit
            if next_occupied in seen:
                continue
            seen.add(next_occupied)
            neighbors = NEIGHBORS[bit.bit_length() - 1]
            touched = neighbors & occupied
            degree = touched.bit_count()
            if degree > 2:
                continue

            # Two contacts in the same component close a permanent induced cycle.
            joined = bit
            next_parts = []
            for part in parts:
                contacts = part & touched
                if contacts:
                    if contacts & (contacts - 1):
                        break
                    joined |= part
                else:
                    next_parts.append(part)
            else:
                next_parts.append(joined)
                saturated = one & touched
                next_allowed = allowed & ~bit & ~_neighbors(saturated)
                next_one = (one & ~touched) | (zero & touched)
                if degree == 2:
                    next_allowed &= ~neighbors
                else:
                    next_one |= bit
                visit(
                    next_occupied, zero & ~touched, next_one, next_allowed,
                    (fringe | neighbors) & next_allowed, tuple(next_parts),
                    size + 1,
                )

    visit(retained, degree_zero, degree_one, available, fringe,
          _components(retained), size)
    return results


def iter_buckets(seed, r=2, min_edges=93, max_edges=98):
    """Yield (omitted positions, set of canonical paths) for 0..r omissions.

    The input seed must be an induced Q8 path in traversal order.
    A canonical path begins at its smaller endpoint. Empty buckets are yielded.
    """
    seed = tuple(seed)
    if not 0 <= r < len(seed) or not 0 <= min_edges <= max_edges:
        raise ValueError("Require 0 <= r < len(seed) and 0 <= min_edges <= max_edges")
    bits = tuple(1 << vertex for vertex in seed)
    original = sum(bits)
    for count in range(r + 1):
        for omitted in combinations(range(len(seed)), count):
            retained = original ^ sum(bits[position] for position in omitted)
            yield omitted, _enumerate_mask(original, retained, min_edges + 1, max_edges + 1)


def enumerate_near(seed, r=2, min_edges=93, max_edges=98):
    """Return all buckets yielded by iter_buckets, keyed by omitted positions."""
    return dict(iter_buckets(seed, r, min_edges, max_edges))
