"""Exact arithmetic of the parametrised K7 count (track A, milestone 38; Lean: lean435/c229/C229Final.lean).

Walk (tab230):      89 m <= 19 S + 678,            S = sum_{k=1}^{m-1} alpha_k
Corner identity:    sum_{k<=m} (24 alpha_k + share_k) + 840 (m + 1) <= 221136,  alpha_0, alpha_m >= 4
Uniform floor X:    X (m - 7) <= sum over the m - 7 windows <= 7 sum_k share_k
=>                  (126672 + 19 X) m <= 29387736 + 133 X.
Prints the bound for sample X and the least X for each bound."""


def bound(X):
    return (29387736 + 133 * X) // (126672 + 19 * X)


def least_x(b):
    X = 0
    while bound(X) > b:
        X += 1
    return X


if __name__ == '__main__':
    assert bound(30) == 230 and bound(29) == 231
    for b in range(230, 219, -1):
        X = least_x(b)
        # per-vertex need in corner units, for reference: 24 * 89 / 19 + X / 7
        print(f'm <= {b}: X >= {X:4d}   (per vertex 24 alpha + share >= {24 * 89 / 19 + X / 7:.1f})')
