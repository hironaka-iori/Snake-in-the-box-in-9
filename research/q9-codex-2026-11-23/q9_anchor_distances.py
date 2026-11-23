"""Propagate Hamming lower bounds on path distances from fixed anchors."""


def exclude_interval(f, selected, small_endian_bits, lower, upper, guards=()):
    """For selected vertices forbid a closed interval, using aligned binary blocks."""
    width=len(small_endian_bits)
    lower=max(lower,0)
    upper=min(upper,(1<<width)-1)
    while lower<=upper:
        remaining=(upper-lower+1).bit_length()-1
        alignment=(lower&-lower).bit_length()-1 if lower else width
        free_bits=min(remaining,alignment)
        f.append([-selected,*guards,*(-x if lower>>i&1 else x
                              for i,x in enumerate(small_endian_bits) if i>=free_bits)])
        lower+=1<<free_bits


def add_distances(f,phase,anchors,length):
    """A vertex at position s has q=(s-wt(v))/2, with s in [0,length]."""
    for vertex,bits in enumerate(phase):
        weight=vertex.bit_count()
        max_phase=(1<<len(bits))-1
        exclude_interval(f,vertex+1,bits,(length-weight)//2+1,max_phase)
        for anchor,position in anchors:
            if anchor==vertex:
                continue
            distance=(anchor^vertex).bit_count()
            if position==0:
                exclude_interval(f,vertex+1,bits,0,(distance-1-weight)//2)
            elif position==length:
                exclude_interval(f,vertex+1,bits,(length-distance-weight)//2+1,max_phase)
            else:
                lo=position-distance+1-weight
                hi=position+distance-1-weight
                exclude_interval(f,vertex+1,bits,(lo+1)//2,hi//2)


def add_terminal_neighbor_distances(f, phase, end, length):
    dim = (len(phase) - 1).bit_length()
    for endpoint, position in ((0, 1), (end, length - 1)):
        for axis in range(dim):
            anchor = endpoint ^ (1 << axis)
            value = (position - anchor.bit_count()) // 2
            f.extend([-anchor - 1, bit if value >> i & 1 else -bit]
                     for i, bit in enumerate(phase[anchor]))
            for vertex, bits in enumerate(phase):
                if vertex == anchor:
                    continue
                distance = (anchor ^ vertex).bit_count()
                weight = vertex.bit_count()
                lo = position - distance + 1 - weight
                hi = position + distance - 1 - weight
                exclude_interval(f, vertex + 1, bits, (lo + 1) // 2, hi // 2,
                                 guards=(-anchor - 1,))
