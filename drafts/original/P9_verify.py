#!/usr/bin/env python3
"""Independent finite audit of Gradient Key Section 4 (not a Lean check).

Enumerates *unordered* sets of distinct column words. Column permutations
produce the same mean cost and path identities after relabelling, so each
unordered table represents exactly m! equally weighted labelled tables.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from math import floor, log2, log


def rowbits(columns, n):
    return [tuple((c >> r) & 1 for c in columns) for r in range(n)]


def path(rows, j, steps):
    m = len(rows[0]) if rows else steps[1]  # (depth cap, m) if no rows
    if not rows:
        m = steps[1]
    else:
        m = len(rows[0])
    cap = steps[0]
    S = frozenset(range(m))
    states, tested, v = [S], [], []
    for _ in range(cap):
        if len(S) <= 1:
            v.append(Fraction(0))
            states.append(S)
            continue
        counts = [sum(row[a] for a in S) for row in rows]
        qualities = [min(k, len(S) - k) for k in counts]
        q = max(qualities, default=0)
        if q == 0:
            v.append(Fraction(0))  # terminated multi-leaf of row-deleted tree
            states.append(S)
            continue
        r = qualities.index(q)  # first max in row order
        k = counts[r]
        v.append(Fraction((len(S) - 2 * k) ** 2, len(S)))
        tested.append(r)
        S = frozenset(a for a in S if rows[r][a] == rows[r][j])
        states.append(S)
    return states, tested, v


def scan_paths():
    profiles, counts = {}, defaultdict(int)
    tie_witness = None
    roworder_witness = None
    for n in range(1, 5):
        for m in range(2, min(2 ** n, 5) + 1):
            N, acc_e, acc_p, acc_v, acc_depth = 0, [Fraction(0)] * (n+2), [Fraction(0)] * (n+1), [Fraction(0)] * (n+1), Fraction(0)
            for cols in combinations(range(1 << n), m):
                rows = rowbits(cols, n)
                for j in range(m):
                    N += 1
                    states, tested, v = path(rows, j, (n+1,m))
                    assert len(states[-1]) == 1, ('nontermination', n,m,cols,j,states)
                    assert len(tested) == len(set(tested)), ('row reused',n,m,cols,j,tested)
                    assert len(tested) <= n
                    for i,S in enumerate(states[:-1]):
                        acc_e[i] += len(S) - 1
                        if len(S) > 1:
                            acc_p[i] += 1
                            counts['original_forks'] += 1
                            if i < n:
                                acc_v[i] += v[i]
                    acc_e[n+1] += len(states[n+1]) - 1
                    acc_depth += len(tested)
                    for d,r in enumerate(tested):
                        S = states[d]
                        k = sum(rows[r][a] for a in S)
                        q = min(k,len(S)-k)
                        qualities = [min(sum(row[a] for a in S),len(S)-sum(row[a] for a in S)) for row in rows]
                        assert q > 0 and r == qualities.index(max(qualities))
                        if tie_witness is None and qualities.count(max(qualities)) >= 2:
                            tie_witness = (n,m,cols,j,d,r,qualities)
                        for i in range(d+1,len(states)):
                            assert len({rows[r][a] for a in states[i]}) == 1
                    for r in range(n):
                        B = rows[:r] + rows[r+1:]
                        stB, _, _ = path(B,j,(n+1,m))
                        counts['deleted_paths'] += 1
                        for i,SB in enumerate(stB):
                            for a in SB:
                                for b in range(m):
                                    if all(row[a] == row[b] for row in B):
                                        assert b in SB, ('pair closure', n,m,cols,j,r,i,SB,a,b)
                            if len(states[i]) >= 2 and r not in tested[:i]:
                                assert states[i] == SB, ('coupling',n,m,cols,j,r,i,states[i],SB)
                                counts['couplings'] += 1
            e=[x/N for x in acc_e]; p=[x/N for x in acc_p]; V=[x/N for x in acc_v]; t=acc_depth/N
            assert e[0]==m-1
            for i in range(n):
                assert e[i+1] == (e[i]-p[i]+V[i])/2, ('recurrence',n,m,i,e,p,V)
                assert V[i] <= Fraction(n,n-i), ('mean',n,m,i,V[i])
                if p[i] > 0:
                    assert float(V[i]) <= 2*float(p[i])*(1+log(2*n/((n-i)*float(p[i])))) + 1e-10
            for h in range(n+2):
                assert t <= sum(p[:min(h,n+1)],Fraction(0)) + e[h],('tail',n,m,h)
            ell = m.bit_length()-1
            bound = ell-1+m/(2**ell) + sum(2**(i-ell)*min(n/(n-i),2+2*log(2*n/(n-i))) for i in range(ell))
            assert float(t) <= bound + 1e-10
            assert float(t) < log2(m) + 2 + 2*log(2*ell)
            assert float(t) < log2(m) + 1 + (ell-1)/(n-ell+1)
            if n >= 2*ell-2:
                assert float(t) < log2(m) + 2
            counts['models'] += 1
            counts['table_column_samples'] += N
            profiles[n,m]=str(t)
    return counts, tie_witness, profiles


def valid_extensions(B):
    m=len(B)
    return [x for x in range(1<<m) if all(B[a]!=B[b] or ((x>>a)&1)!=((x>>b)&1) for a in range(m) for b in range(a+1,m))]


def check_conditional():
    visited = set()
    counts = defaultdict(int)
    examples = {}
    for n in range(1, 4):
        for m in range(2, min(1<<n,5)+1):
            for cols in combinations(range(1<<n),m):
                for r in range(n):
                    B=tuple(tuple((c>>k)&1 for k in range(n) if k!=r) for c in cols)
                    if B in visited: continue
                    visited.add(B)
                    ext=valid_extensions(B)
                    assert ext
                    counts['deleted_tables'] += 1
                    # Every possible union of equality classes, including empty set.
                    for sbits in range(1<<m):
                        S={a for a in range(m) if (sbits>>a)&1}
                        if any((a in S)!=(b in S) and B[a]==B[b] for a in range(m) for b in range(m)):
                            continue
                        f=sum(all(B[a]!=B[b] for b in range(m) if b!=a) for a in S)
                        sq=[]
                        for x in ext:
                            k=sum((x>>a)&1 for a in S)
                            imbalance = Fraction((len(S)-2*k)**2,len(S)) if S else Fraction(0)
                            sq.append(imbalance)
                        mean=sum(sq,Fraction(0))/len(ext)
                        target=Fraction(f,len(S)) if S else Fraction(0)
                        assert mean==target, ('moment', n,m,B,S,ext,mean,target)
                        counts['closed_sets']+=1
                        if len(S)>0: counts['positive_sets']+=1
                        if not examples and len(S) == m and f > 0 and any(B[a]==B[b] for a in range(m) for b in range(a+1,m)):
                            examples={'B':B,'S':sorted(S),'f':f,'extensions':len(ext),'mean':str(mean)}
    return counts,examples

if __name__ == '__main__':
    ct, tie, profiles = scan_paths()
    moment, example = check_conditional()
    print('PATH_AUDIT',dict(ct))
    print('TIE_WITNESS',tie)
    print('EXACT_T_VALUES',profiles)
    print('CONDITIONAL_MOMENT',dict(moment))
    print('EXAMPLE',example)
