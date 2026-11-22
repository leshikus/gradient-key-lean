"""Independent finite checks of the P1 greedy-path mathematical invariants.
Not a Lean compiler check; tests the model at small sizes and random max cases.
"""
from itertools import permutations
from random import Random


def run_case(n, columns):
    m = len(columns)
    assert len(set(columns)) == m and all(0 <= c < (1 << n) for c in columns)
    def bit(r, k): return (columns[k] >> r) & 1
    for j in range(m):
        S = frozenset(range(m))
        candidates = [S]
        tested = []
        while len(S) >= 2:
            qualities = [min(sum(bit(r, k) for k in S), sum(1 - bit(r, k) for k in S)) for r in range(n)]
            q = max(qualities)
            assert q > 0
            r = qualities.index(q)  # first in original row order
            assert r not in tested
            tested.append(r)
            T = frozenset(k for k in S if bit(r, k) == bit(r, j))
            assert j in T and T < S
            S = T
            candidates.append(S)
        assert S == {j} and len(tested) <= n
        depth = len(tested)
        for h in range(n + 6):
            get_s = lambda i: len(candidates[min(i, depth)])
            assert depth <= sum(1 for i in range(h) if get_s(i) >= 2) + get_s(h) - 1, (n,m,j,h)
        for d in range(depth):
            for i in range(d + 1, depth + 3):
                for k in candidates[min(i, depth)]:
                    assert bit(tested[d], k) == bit(tested[d], j)
    return m


if __name__ == '__main__':
    rng = Random(142857)
    total = 0
    for n in (1, 2, 3):
        allcols = list(range(2**n))
        for m in range(2, 2**n + 1):
            limit = 600 if n == 3 else 100000
            for ix, cols in enumerate(permutations(allcols, m)):
                if ix >= limit: break
                run_case(n, cols)
                total += 1
    for n in (4, 5, 6):
        for m in (2, 3, 2**(n-1), 2**n):
            for _ in range(50):
                run_case(n, rng.sample(range(2**n), m))
                total += 1
    print(f'PASS: {total} distinct-column tables; all columns; h=0,...,n+5')
    print('Includes n=1, m=2, m=2^n, and h>n.')
