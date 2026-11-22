"""Exact independent exhaustive check of the P2 partition identity.
This checks mathematics, not Lean compilation.
"""
from itertools import product
from fractions import Fraction

count=0
for m in range(0, 7):
    for key in product(range(3), repeat=m):
        for bit in product(range(2), repeat=m):
            parent_size = {}
            next_size = {}
            imbalance = {}
            fork = {}
            for c in range(3):
                a=sum(key[j]==c and bit[j]==1 for j in range(m))
                b=sum(key[j]==c and bit[j]==0 for j in range(m))
                s=a+b
                parent_size[c] = s
                fork[c] = int(s >= 2)
                imbalance[c] = Fraction((a-b)**2, s) if s>=2 else Fraction(0)
            for j in range(m):
                next_size[j] = sum(key[k]==key[j] and bit[k]==bit[j] for k in range(m))
                assert next_size[j]>=1
                if parent_size[key[j]] == 1:
                    assert next_size[j]==1 and fork[key[j]]==0 and imbalance[key[j]]==0
            lhs=sum(Fraction(next_size[j]-1) for j in range(m))
            rhs=(sum(Fraction(parent_size[key[j]]-1) for j in range(m))
                -sum(Fraction(fork[key[j]]) for j in range(m))
                +sum(imbalance[key[j]] for j in range(m)))/2
            assert lhs==rhs, (m,key,bit,lhs,rhs)
            count+=1
print(f"PASS: {count} exact finite partition instances, m=0..6, 3 parent labels, both branch bits")

# Check the paper's fully concrete greedy rule for all injective binary tables
# for n = 1..3 (small enough for exhaustive enumeration).
from itertools import permutations
ct=0
for n in (1,2,3):
    words=list(product((False,True),repeat=n))
    for m in range(1,min(4,len(words))+1):
        for columns in permutations(words,m):
            path=[set(range(m)) for _ in range(m)]
            for i in range(n+2):
                sizes=[len(x) for x in path]
                v=[];p=[];new=[]
                for j,S in enumerate(path):
                    if len(S)==1:
                        v.append(Fraction(0));p.append(0);new.append(S)
                    else:
                        row=max(range(n),key=lambda r: min(sum(columns[k][r] for k in S),
                                    sum(not columns[k][r] for k in S)))
                        # tie is first in row order, not max's last
                        k=sum(columns[k][row] for k in S)
                        v.append(Fraction((len(S)-2*k)**2,len(S)))
                        p.append(1)
                        new.append({x for x in S if columns[x][row]==columns[j][row]})
                lhs=sum(Fraction(len(S)-1) for S in new)
                rhs=(sum(Fraction(s-1) for s in sizes)-sum(p)+sum(v))/2
                assert lhs==rhs,(n,m,columns,i,lhs,rhs)
                path=new
                ct+=1
print(f"PASS: {ct} exact greedy-depth checks, n=1..3, m<=4; all injective ordered tables")
