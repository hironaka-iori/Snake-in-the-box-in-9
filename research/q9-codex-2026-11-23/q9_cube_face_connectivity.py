"""Every occupied small cube face must connect to the rest of the path."""

from itertools import combinations


def add_face_connectivity(formula, pool, bonds, dim, vertex_count):
    n = 1 << dim
    for fixed_count in range(2,5):
        if vertex_count <= 1 << (dim-fixed_count):
            continue
        for fixed in combinations(range(dim),fixed_count):
            mask = sum(1 << axis for axis in fixed)
            occupants = {}
            boundary = {}
            for u in range(n):
                occupants.setdefault(u&mask,[]).append(u+1)
            for u,v,edge in bonds:
                a,b = u&mask,v&mask
                if a!=b:
                    boundary.setdefault(a,[]).append(edge)
                    boundary.setdefault(b,[]).append(edge)
            for face,vertices in occupants.items():
                nonempty = pool.id()
                formula.extend([[-v,nonempty] for v in vertices])
                formula.append([-nonempty,*boundary[face]])
