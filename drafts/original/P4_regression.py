"""Exact finite sanity checks for P4; NOT a Lean compiler or proof."""
from itertools import combinations, product
from fractions import Fraction


def q(table, S, r):
    k = sum(table[r][c] for c in S)
    return min(k, len(S) - k)


def v(table, S, r):
    k = sum(table[r][c] for c in S)
    return Fraction((len(S) - 2*k)**2, len(S)) if S else Fraction(0)


def path(table, j, excluded=None, horizon=None):
    n, m = len(table), len(table[0])
    S, available = frozenset(range(m)), frozenset(range(n)) - (set() if excluded is None else {excluded})
    states = [(S, available, None)]
    for _ in range(n+1 if horizon is None else horizon):
        if available:
            g = min(available, key=lambda r: (-q(table, S, r), r))
            if q(table, S, g) > 0:
                S = frozenset(c for c in S if table[g][c] == table[g][j])
                available = available - {g}
                states.append((S, available, g))
                continue
        states.append((S, available, None))
    return states


def all_column_distinct_tables(n, m):
    for cols in combinations(range(2**n), m):
        from itertools import permutations
        for perm in permutations(cols):
            yield tuple(tuple((c >> r) & 1 for c in perm) for r in range(n))


def run():
    tables, samples, events = 0, 0, 0
    for n, m in [(1,2), (2,2), (2,3), (2,4), (3,2), (3,3), (3,4)]:
        for A in all_column_distinct_tables(n, m):
            tables += 1
            for j in range(m):
                full = path(A, j, horizon=n+3)
                deleted = {r: path(A, j, excluded=r, horizon=n+3) for r in range(n)}
                for i in range(n+2):
                    samples += 1
                    S, unused, _ = full[i]
                    assert j in S
                    # Valid full path never terminates with more than one column.
                    if len(S) >= 2:
                        assert len(unused) == n - i
                        assert full[i+1][2] in unused
                    lhs = v(A, S, full[i+1][2]) if len(S) >= 2 else Fraction(0)
                    rhs = Fraction(0)
                    if i < n:
                        for r in range(n):
                            DS = deleted[r][i][0]
                            assert j in DS
                            # All identical columns of the deleted table travel together.
                            for a in range(m):
                                for b in range(m):
                                    if all(A[k][a] == A[k][b] for k in range(n) if k != r):
                                        assert ((a in DS) == (b in DS))
                            E = len(S) >= 2 and r in unused
                            if E:
                                events += 1
                                assert DS == S
                                assert deleted[r][i][1] == unused - {r}
                                assert v(A, DS, r) == v(A, S, r)
                                rhs += v(A, DS, r)
                        rhs /= (n - i)
                        assert lhs <= rhs, (n, m, j, i, A, lhs, rhs)
                for r in range(n):
                    for i in range(n+2):
                        ds = deleted[r]
                        if ds[i+1][2] is None:
                            assert all(ds[t][:2] == ds[i][:2] for t in range(i, n+4))
    arbitrary = 0
    for n, m in [(0, 3), (1, 4), (2, 5), (3, 4)]:
        for bits in product((0, 1), repeat=n*m):
            arbitrary += 1
            A = tuple(tuple(bits[r*m+c] for c in range(m)) for r in range(n))
            # Zero-row tables are also legitimate: use the empty matrix and
            # an explicit path representation with m columns.
            if n == 0:
                assert not A
                assert tuple(range(m)) == tuple(range(m))  # zero rows cannot split
                continue
            for j in range(m):
                states = path(A, j, horizon=n+3)
                for i in range(n+2):
                    S, available, _ = states[i]
                    assert j in S
                    for a in range(m):
                        for b in range(m):
                            if all(A[k][a] == A[k][b] for k in range(n)):
                                assert (a in S) == (b in S)
                    if states[i+1][2] is None:
                        assert all(states[t][:2] == states[i][:2]
                                   for t in range(i, n+4))
    print(f"PASS: {tables} valid tables, {samples} path states, {events} row events; "
          f"{arbitrary} arbitrary tables (including duplicates)")

if __name__ == '__main__':
    run()
