"""Optional independent finite sanity check of the *mathematical* P6 interfaces.
Not a Lean compilation/proof. Enumerates small valid binary tables exactly.
"""
from fractions import Fraction
from itertools import permutations


def path(rows, j, nsteps):
    S = tuple(range(len(rows[0]))) if rows else None
    assert S is not None
    tested = []
    result = []
    for _ in range(nsteps):
        result.append((S, tuple(tested)))
        if len(S) <= 1:
            continue
        scores = [min(sum(row[a] for a in S), len(S)-sum(row[a] for a in S)) for row in rows]
        best = max(scores, default=0)
        if not best:
            continue
        chosen = scores.index(best)
        tested.append(chosen)
        S = tuple(a for a in S if rows[chosen][a] == rows[chosen][j])
    return result


def deleted_candidate(rows, r, j, i):
    others = [row for t, row in enumerate(rows) if t != r]
    m = len(rows[0])
    S = tuple(range(m))
    for _ in range(i):
        if len(S) <= 1:
            continue
        scores = [min(sum(row[a] for a in S), len(S)-sum(row[a] for a in S)) for row in others]
        best = max(scores, default=0)
        if best:
            g = scores.index(best)
            S = tuple(a for a in S if others[g][a] == others[g][j])
    return S


def imb(row, S):
    return Fraction((len(S)-2*sum(row[a] for a in S))**2, len(S))


def run(n, m):
    words = list(__import__('itertools').product((0,1), repeat=n))
    samples = 0
    avgV = [Fraction(0) for _ in range(n)]
    avgU = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for cols in permutations(words, m):
        rows = [tuple(col[r] for col in cols) for r in range(n)]
        for j in range(m):
            samples += 1
            paths = path(rows, j, n)
            for i, (S, tested) in enumerate(paths):
                v = min([imb(row, S) for row in rows]) if len(S) >= 2 else Fraction(0)
                avgV[i] += v
                active = [r for r in range(n) if len(S) >= 2 and r not in tested]
                if len(S) >= 2:
                    assert len(active) == n-i, (n,m,cols,j,i,S,active,tested)
                terms = []
                for r in range(n):
                    T = deleted_candidate(rows, r, j, i)
                    u = imb(rows[r], T)
                    avgU[i][r] += u
                    if r in active:
                        assert T == S, (cols, j, i, r, T, S)
                        assert v <= u
                        terms.append(u)
                assert v <= sum(terms, Fraction(0))/(n-i), (n,m,cols,j,i,S,terms)
    assert all(u <= samples for group in avgU for u in group)
    assert all(v <= Fraction(n, n-i)*samples for i,v in enumerate(avgV))
    print(f"n={n}, m={m}: {samples} samples; V=" + ", ".join(str(v/samples) for v in avgV))

for n,m in [(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)]:
    run(n,m)
