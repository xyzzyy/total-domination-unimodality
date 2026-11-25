"""Numerical check of the analytic counterexample G(m,p,q) = G(18000, 210, 359).

Everything here is a bound on log2 of a natural number, computed with 60-digit
Decimal arithmetic (the quantities are ~4e9 bits, so float64 would also do).
The *exact* integer conditions that are cheap (k-ordering, the eigenvector
condition of the transfer matrix) are checked with Python integers.

Notation (see the paper):
  C  = 1 + mq + 3mpq   free vertices (leaf + clause vertices)
  P  = mp, Q = mq,  N1 = C + P + Q
  k1 = 1 + Q + floor(N1/2)                         (peak of family I)
  k3 = 1 + P + Q + floor(C/2) + floor(Q/3)         (peak of family II)
  k2 = 2,050,725,001                               (valley)
Lower bounds   d_t(k1) >= binom(N1, N1//2)                 >= 2^N1 / (N1+1)
               d_t(k3) >= binom(C,C//2) binom(Q,Q//3) 2^(Q-Q//3) >= 2^C 3^Q / ((C+1)(Q+1))
Upper bound    d_t(k2) <= U1 + U2 + U3 with
  U1 = binom(N1, k2-1-Q)              <= (1+t)^N1 / t^(k2-1-Q),       t = (T+1)/T
  U2 = [x^s](1+x)^C (2x+x^2)^Q        <= (a+b)^C (a(a+2b))^Q / (a^s b^(C+2Q-s)),
       s = k2-1-P, (a,b) = (2374, 2375)  [Chernoff at x = a/b]
  U3 = 2^C |III|,  |III| <= m 2^q L (Lam/L)^(m-1), Lam = 3^q (L+1), L = 2^18.
"""
from decimal import Decimal as D, getcontext
import math

getcontext().prec = 60
LN2 = D(2).ln()
def lg(x):  # log2 of a positive Decimal/int
    return D(x).ln() / LN2

m, p, q = 18000, 210, 359
C = 1 + m*q + 3*m*p*q
P, Q = m*p, m*q
N1 = C + P + Q
n_vertices = 1 + C + P + 2*Q
k1 = 1 + Q + N1//2
k3 = 1 + P + Q + C//2 + Q//3
k2 = 2050725001
T = 2675
a, b = 2374, 2375
L = 2**18
Lam = 3**q * (L + 1)

print(f"C = {C:,}  P = {P:,}  Q = {Q:,}  N1 = {N1:,}  |V| = {n_vertices:,}")
print(f"k1 = {k1:,}  k2 = {k2:,}  k3 = {k3:,}")
assert (C, P, Q, N1, n_vertices) == (4077522001, 3780000, 6462000, 4087764001, 4094226002)
assert (k1, k3) == (2050344001, 2051157001)
assert k1 < k2 < k3 and 1 + P + Q <= k2
print(f"k3 - k1 = {k3-k1:,}  (= m(3p-q)/6 = {m*(3*p-q)//6:,})")

# --- exact integer side conditions -------------------------------------------
assert 3**q > 2**(p+q), "phase balance 3^q > 2^(p+q)"
print(f"q log2 3 - (p+q) = {float(q*lg(3) - (p+q)):.6f}")
assert (2**(p+q) + 2**q * L) * L <= Lam, "eigenvector condition, first row"
assert 3**q * (L + 1) <= Lam, "eigenvector condition, second row"
print("transfer-matrix eigenvector conditions: OK (exact integers)")
# Q is divisible by 3, so floor(Q/3) is the mode of Bin(Q, 1/3):
assert Q % 3 == 0

# --- lower bounds ------------------------------------------------------------
LB1 = N1 - lg(N1 + 1)
LB3 = C + Q*lg(3) - lg(C + 1) - lg(Q + 1)
LB = min(LB1, LB3)

# --- upper bounds ------------------------------------------------------------
j1 = k2 - 1 - Q
t = D(T + 1) / D(T)
U1 = N1*lg(1 + t) - j1*lg(t)
s = k2 - 1 - P
assert s <= C + 2*Q
U2 = C*lg(a + b) + Q*lg(a*(a + 2*b)) - s*lg(a) - (C + 2*Q - s)*lg(b)
U3 = C + lg(m) + q + lg(L) + (m - 1)*(lg(Lam) - lg(L))

# exact log2-binomials via lgamma, for comparison only (float)
def lbinom(n, k):
    return (math.lgamma(n+1) - math.lgamma(k+1) - math.lgamma(n-k+1)) / math.log(2)
print()
print(f"log2 LB1 (k1)  >= N1 + {float(LB1 - N1):.3f}      [exact log2 binom: N1 + {lbinom(N1, N1//2) - N1:.3f}]")
print(f"log2 LB3 (k3)  >= N1 + {float(LB3 - N1):.3f}")
print(f"log2 U1        <= N1 + {float(U1 - N1):.3f}     [exact log2 binom: N1 + {lbinom(N1, j1) - N1:.3f}]")
print(f"log2 U2        <= N1 + {float(U2 - N1):.3f}")
print(f"log2 U3        <= N1 + {float(U3 - N1):.3f}")
print()
for name, U in (("U1 (family I)", U1), ("U2 (family II)", U2), ("U3 (mixed)", U3)):
    print(f"margin  min(LB1,LB3) - {name:15s} = {float(LB - U):8.3f} bits"
          f"   (vs LB1: {float(LB1-U):.3f}, vs LB3: {float(LB3-U):.3f})")
worst = min(LB - U1, LB - U2, LB - U3)
assert worst > 2, "U1+U2+U3 < min(LB1, LB3) needs each margin > log2 3"
print(f"\nworst margin {float(worst):.2f} bits > log2(3): d_t(k2) < min(d_t(k1), d_t(k3)).  NOT UNIMODAL.")

# --- heuristics quoted in the paper ------------------------------------------
sigma1 = math.sqrt(N1/4)
sigma2 = math.sqrt(C/4 + Q*2/9)
print(f"\nstd dev family I ~ {sigma1:,.0f}, family II ~ {sigma2:,.0f}; separation k3-k1 = {k3-k1:,} "
      f"~ {(k3-k1)/sigma1:.1f} sigma")
print(f"optimal Chernoff T for U1: {(N1-j1)/(2*j1-N1):.1f};  optimal x for U2 ~ "
      f"{math.exp(-(C/2 + Q + Q/3 - s) / (C/4 + 2*Q/9)):.7f} vs a/b = {a/b:.7f}")
