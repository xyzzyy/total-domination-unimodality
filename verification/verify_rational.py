"""Check the paper's logarithm bounds with exact rational arithmetic.

No floating point or Decimal arithmetic is used in the comparisons.
The analytic valley index differs from the index in the Lean proof.
"""
from fractions import Fraction as F
from functools import lru_cache


def series(z):
    lower = 2 * sum((z ** (2*j + 1) / (2*j + 1) for j in range(24)), F(0))
    remainder = 2 * z**49 / (49 * (1 - z*z))
    return lower, lower + remainder


LN2_LO, LN2_HI = series(F(1, 3))


@lru_cache(None)
def lg_bounds(u):
    u = F(u)
    assert u > 0
    exponent = 0
    while u >= 2:
        u /= 2
        exponent += 1
    while u < 1:
        u *= 2
        exponent -= 1
    lo, hi = series((u - 1) / (u + 1))
    return exponent + lo / LN2_HI, exponent + hi / LN2_LO


def expression(constant, terms):
    lo = hi = F(constant)
    for multiplier, argument in terms:
        left, right = lg_bounds(argument)
        if multiplier < 0:
            left, right = right, left
        lo += multiplier * left
        hi += multiplier * right
    return lo, hi


def main():
    m, p, q = 18000, 210, 359
    C = 1 + m*q + 3*m*p*q
    P, Q = m*p, m*q
    N1 = C + P + Q
    k2 = 2050725001
    j1, s = k2 - 1 - Q, k2 - 1 - P
    a, b = 2374, 2375
    t = F(2676, 2675)
    bounds = {
        'B1': expression(0, [(-1, N1 + 1)]),
        'B3': expression(C-N1, [(Q, 3), (-1, C+1), (-1, Q+1)]),
        'U1': expression(-N1, [(N1, 1+t), (-j1, t)]),
        'U2': expression(-N1, [(C, a+b), (Q, a*(a+2*b)),
                               (-s, a), (-(C+2*Q-s), b)]),
        'U3': expression(C+q+18-N1, [(1, m), ((m-1)*q, 3),
                                (m-1, 1+F(1, 2**18))]),
    }
    for name in ('B1', 'B3'):
        assert bounds[name][0] > F('-31.930'), name
        print(f'{name}: lower offset > -31.930 (exact rational check)')
    for name, limit in [('U1', '-102.461'), ('U2', '-104.192'), ('U3', '-150.086')]:
        assert bounds[name][1] < F(limit), name
        print(f'{name}: upper offset < {limit} (exact rational check)')
        assert min(bounds['B1'][0], bounds['B3'][0]) - bounds[name][1] > F('70.5')
    # 3 * 2^(-70.5) < 2^(-68), by squaring: 9 < 2^5.
    assert 9 < 2**5
    print('PASS: U1 + U2 + U3 < 2^(-68) min(B1, B3).')


if __name__ == '__main__':
    main()
