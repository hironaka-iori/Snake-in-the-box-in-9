"""Canonical masks on a Q4 face containing distance-three endpoints."""

from itertools import permutations

from q9_antipodal_root_face import encode_masks
from q9_q4_forest_diagram import forest_masks
from verify_q9_free_dimension_cuts import deg, parts


def spanning_masks():
    # The face uses the three endpoint-difference axes plus axis 3.
    # Only permute the difference axes, preserving both endpoints and the face.
    remaps = [tuple((v & 8) | sum(((v >> i) & 1) << j
                                 for i,j in enumerate(order)) for v in range(16))
              for order in permutations(range(3))]
    terminal_mask = (1 << 0) | (1 << 7)
    for mask in sorted(forest_masks()):
        if mask & terminal_mask != terminal_mask:
            continue
        selected = {v for v in range(16) if mask & (1 << v)}
        if any(deg(selected,v,4) > 1 for v in (0,7)):
            continue
        # A shared component would be the entire endpoint-to-endpoint path.
        if any({0,7} <= component for component in parts(selected,4)):
            continue
        if all(mask <= sum(1 << remap[v] for v in selected) for remap in remaps):
            yield mask


def constrain_spanning_face(formula,pool,population):
    encode_masks(formula,pool,(mask for mask in spanning_masks()
                              if mask.bit_count() == population))
