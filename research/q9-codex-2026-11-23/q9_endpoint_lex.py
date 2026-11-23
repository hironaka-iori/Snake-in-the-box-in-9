"""Lex constraints for the group permuting coordinates within the endpoint blocks."""
from pysat.formula import IDPool


def add_swap_lex(formula, dim, swaps):
    pool = IDPool(start_from=formula.nv + 1)
    for a,b in swaps:
        assert a < b
        bit_mask = (1 << a) | (1 << b)
        pairs = [(v+1, (v ^ bit_mask)+1) for v in range(1 << dim)
                 if v & bit_mask == 1 << a]
        previous = None
        for index, (left, right) in enumerate(pairs):
            guard = [] if previous is None else [-previous]
            formula.append([*guard,-left,right])
            if index == len(pairs)-1:
                break
            equal_prefix = pool.id()
            formula.extend([[*guard,-left,-right,equal_prefix],
                            [*guard,left,right,equal_prefix]])
            previous = equal_prefix


def add_endpoint_lex(formula, dim, distance):
    """Require the selected-point bit string to be <= each generator image."""
    add_swap_lex(formula,dim,((i,i+1) for i in range(dim-1) if i+1!=distance))
