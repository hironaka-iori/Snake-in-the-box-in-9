"""A complete origin-face split for antipodal 221-edge paths in Q9."""

from itertools import permutations

from q9_q4_forest_diagram import forest_masks


def origin_component_size(mask):
    pending = [0]
    component = {0}
    while pending:
        vertex = pending.pop()
        for axis in range(4):
            neighbor = vertex ^ (1 << axis)
            if mask & (1 << neighbor) and neighbor not in component:
                component.add(neighbor)
                pending.append(neighbor)
    return len(component)


def root_masks():
    # Axis 0 is the first edge. Permutations of axes 1 through 3 preserve it.
    remaps = [tuple((v & 1) | sum(((v >> i) & 1) << j
                                 for i,j in zip((1,2,3),order)) for v in range(16))
              for order in permutations((1,2,3))]
    other_neighbors = (1 << 2) | (1 << 4) | (1 << 8)
    for mask in sorted(forest_masks()):
        if mask & 3 != 3 or mask & other_neighbors:
            continue
        vertices = [v for v in range(16) if mask & (1 << v)]
        if all(mask <= sum(1 << remap[v] for v in vertices) for remap in remaps):
            yield mask


def encode_masks(formula,pool,masks):
    choices = []
    for mask in masks:
        choice = pool.id()
        choices.append(choice)
        for v in range(16):
            literal = v+1 if mask & (1 << v) else -v-1
            formula.append([-choice,literal])
    assert choices
    formula.append(choices)


def constrain_root_face(formula,pool,size):
    # Making axis 0 the first edge and normalizing axes 1 through 3
    # leaves axes 4 through 8 free to be sorted by frequency.
    encode_masks(formula,pool,(mask for mask in root_masks()
                              if origin_component_size(mask) == size))
