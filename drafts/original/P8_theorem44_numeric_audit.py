"""Independent numerical sanity check of Section 4 algebra; not a Lean proof."""
import math
import random

rng = random.Random(4408)
trials = 0
worst = (float('inf'), None)
for n in range(1, 21):
    ms = {2, 2**n}
    for k in range(1, n + 1):
        ms.update((2**k, 2**k + 1, 2**(k+1) - 1))
    ms = sorted(m for m in ms if 2 <= m <= 2**n)
    for m in ms:
        ell = m.bit_length() - 1
        assert 1 <= ell <= n
        assert 2**ell <= m < 2**(ell+1)
        assert (2*ell - 2 <= n) == (2*ell <= n + 2)
        for _ in range(100):
            e = float(m - 1)
            total_p = 0.0
            main_sum = 0.0
            for i in range(ell):
                p = rng.choice((0., 1., rng.random(), rng.random()))
                c = 2*n/(n-i)
                v = 0.0 if p == 0 else rng.random() * min(n/(n-i), 2*p*(1+math.log(c/p)))
                e = (e-p+v)/2
                total_p += p
                w = 2**(i-ell)
                main_sum += w*min(n/(n-i), 2+2*math.log(c))
            t = total_p + e
            main_rhs = ell-1+m/2**ell+main_sum
            a = math.log2(m) + 2 + 2*math.log(2*ell)
            b = math.log2(m) + 1 + (ell-1)/(n-ell+1)
            c = math.log2(m) + 2
            assert t <= main_rhs+1e-10, (n,m,'main',t,main_rhs)
            assert t < a+1e-10, (n,m,'a',t,a)
            assert t < b+1e-10, (n,m,'b',t,b)
            if n >= 2*ell-2:
                assert t < c+1e-10, (n,m,'c',t,c)
            assert ell-1+m/2**ell <= math.log2(m)+1e-12
            worst = min(worst, (b-t, (n,m,ell)))
            trials += 1
print(f'PASS: {trials} numerical parameter trials, n=1..20, including powers of two and m=2')
print(f'Smallest observed margin in (b): {worst[0]:.8g}, at (n,m,ell)={worst[1]}')
