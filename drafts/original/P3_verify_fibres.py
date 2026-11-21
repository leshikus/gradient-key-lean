"""Small exhaustive mathematical checks of the P3 row-deletion fibre laws.

Independent of Lean elaboration; does not certify P3_ConditionalFibre.lean.
"""
from itertools import product
from collections import Counter


def distinct(A, m):
    return len({tuple(row[j] for row in A) for j in range(m)}) == m


def valid_extension(B, x, m):
    return all(a == b or any(row[a] != row[b] for row in B) or x[a] != x[b]
               for a in range(m) for b in range(m))


def all_tables(rows, m):
    for bits in product((0, 1), repeat=rows*m):
        yield tuple(bits[i*m:(i+1)*m] for i in range(rows))


def run_case(n, m):
    seen = tested = impossible = positive = duplicate = 0
    # Index all VALID full tables by the deletion key just once.
    by_fibre = [dict() for _ in range(n+1)]
    for A in all_tables(n+1, m):
        if distinct(A, m):
            for r in range(n+1):
                key = A[:r] + A[r+1:]
                by_fibre[r].setdefault(key, set()).add(A)
    for B in all_tables(n, m):
        ext = {x for x in product((0, 1), repeat=m)
               if valid_extension(B, x, m)}
        if ext:
            positive += 1
            if len({tuple(row[j] for row in B) for j in range(m)}) < m:
                duplicate += 1
        else:
            impossible += 1
        for r in range(n+1):
            fibre = by_fibre[r].get(B, set())
            assert len(fibre) == len(ext)
            assert {A[r] for A in fibre} == ext
            assert {B[:r] + (x,) + B[r:] for x in ext} == fibre
            tested += 1
            for j0 in range(m):
                # In the uniform product sample (A,j), fixing j=j0 leaves
                # each table in the fibre exactly once.
                counts = Counter(A[r] for A in fibre)
                assert set(counts) == ext
                assert all(counts[x] == 1 for x in ext)
                assert sum(counts.values()) == len(ext)
                seen += 1
    return dict(remaining_rows=n, columns=m,
                deleted_tables=positive+impossible, positive=positive,
                with_duplicates=duplicate, zero_fibres=impossible,
                row_fibres=tested, joint_fibres=seen)


if __name__ == "__main__":
    for n, m in [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5)]:
        print(run_case(n, m))
    print("PASS (exhaustive finite checks; Lean NOT COMPILED)")
