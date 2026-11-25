"""Independent exact re-derivation of d_t(G,k) for the computational counterexamples.

Written from the definition in the paper, sharing no code with graph_exact.py or
the earlier audit.  No FLINT.  Method:
  1. build the graph G_{w,d}(m,p; q_0..q_{m-1}) explicitly and check that it is
     simple, connected, bipartite and has no isolated vertex;
  2. on small members of the family, compare the transfer-matrix formula below
     with brute-force enumeration of all 2^n vertex subsets;
  3. for the large graph, evaluate the variable polynomial H(x) at all N-th
     roots of unity (N > number of variable vertices) modulo ~760 NTT-friendly
     primes (vectorised with numpy), recover its coefficients by an inverse DFT,
     convolve with binomial coefficients binom(C, .) mod P to get
     [x^k] x(1+x)^C H(x), and rebuild the exact integers by CRT.
     The product of the primes exceeds 2^(n+1) > every coefficient, so the
     reconstruction is exact.

Transfer matrix (derived in the paper): D_t = x (1+x)^C H(x), C = 1 + #clauses,
H = Tr prod_i M_i, states r in {0..w} = length of the current run of *full*
A-blocks (capped at w).  Block i with A-row not full: r -> 0, weight
((1+x)^p - x^p) g^{q_i}, g = x(1+x)^d (all B of the block chosen, Z free).
A-row full: r -> min(r+1, w), weight x^p g^{q_i} if the new run is < w, else
x^p (g + x^d)^{q_i} (each B may be omitted, which forces its d Z-partners).
"""
import json, sys, time
from collections import deque
from itertools import combinations
import numpy as np

sys.set_int_max_str_digits(0)

def build(m, p, w, d, qs):
    assert len(qs) == m and 1 <= w <= m
    adj = []
    def new():
        adj.append(set()); return len(adj) - 1
    def edge(u, v):
        assert u != v and v not in adj[u]
        adj[u].add(v); adj[v].add(u)
    hub, leaf = new(), new()
    edge(hub, leaf)
    A = [[new() for _ in range(p)] for _ in range(m)]
    B = [[new() for _ in range(q)] for q in qs]
    Z = [[[new() for _ in range(d)] for _ in row] for row in B]
    for v in [x for r in A for x in r] + [x for r in B for x in r] + \
             [x for r in Z for y in r for x in y]:
        edge(hub, v)
    nclause = 0
    for i in range(m):
        for b, bv in enumerate(B[i]):
            for zv in Z[i][b]:
                c = new(); edge(c, bv); edge(c, zv); nclause += 1
            for s in range(w):
                for av in A[(i - s) % m]:
                    c = new(); edge(c, bv); edge(c, av); nclause += 1
    n = len(adj)
    assert all(adj[v] for v in range(n)), "isolated vertex"
    col = [-1] * n; col[0] = 0; dq = deque([0])
    while dq:
        u = dq.popleft()
        for v in adj[u]:
            if col[v] < 0: col[v] = 1 - col[u]; dq.append(v)
            else: assert col[v] != col[u], "odd cycle"
    assert min(col) == 0, "disconnected"
    edges = sum(len(a) for a in adj) // 2
    return adj, nclause, edges

def brute(adj):
    n = len(adj); masks = [sum(1 << v for v in a) for a in adj]
    out = [0] * (n + 1)
    for S in range(1 << n):
        if all(S & mk for mk in masks): out[bin(S).count("1")] += 1
    return out

# ---------- modular arithmetic helpers (numpy int64, moduli < 2^31) ----------
def is_prime(n):
    if n < 2: return False
    for sp in (2, 3, 5, 7, 11, 13): 
        if n % sp == 0: return n == sp
    dd, s = n - 1, 0
    while dd % 2 == 0: dd //= 2; s += 1
    for a in (2, 3, 5, 7, 11):   # deterministic for n < 2.1e12
        x = pow(a, dd, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def vpow(base, e, P):
    res = np.ones_like(base); b = base.copy()
    while e:
        if e & 1: res = res * b % P
        b = b * b % P; e >>= 1
    return res

def root_table(P, N):
    h = 2
    while True:                       # element of exact order N
        g0 = pow(h, (P - 1) // N, P)
        if pow(g0, N // 2, P) != 1: break
        h += 1
    R = np.empty(N, dtype=np.int64); R[0] = 1
    step, filled = g0, 1
    while filled < N:                 # R[j] = g0^j by doubling
        R[filled:2*filled] = R[:filled] * step % P
        step = step * step % P; filled *= 2
    return R

def H_coeffs_mod(m, p, w, d, qs, P, N):
    """Coefficients of H(x) = Tr prod M_i modulo P (requires N > deg H)."""
    R = root_table(P, N)
    x = R
    xp = vpow(x, p, P)
    abad = (vpow(x + 1, p, P) - xp) % P
    g = x * vpow(x + 1, d, P) % P
    gfree = (g + vpow(x, d, P)) % P
    cache = {}
    for q in set(qs):
        gq = vpow(g, q, P)
        cache[q] = (abad * gq % P, xp * gq % P, xp * vpow(gfree, q, P) % P)
    # v[start, state, point]; trace over start states
    v = np.zeros((w + 1, w + 1, N), dtype=np.int64)
    for s in range(w + 1): v[s, s, :] = 1
    for q in qs:
        bad, part, full = cache[q]
        nv = np.empty_like(v)
        nv[:, 0, :] = v.sum(axis=1) % P * bad % P
        if w >= 2:
            nv[:, 1:w, :] = v[:, 0:w-1, :] * part % P
        nv[:, w, :] = (v[:, w-1, :] + v[:, w, :]) % P * full % P
        v = nv
    Hval = sum(v[s, s, :] for s in range(w + 1)) % P
    # inverse DFT: h_k = N^{-1} sum_j H(g^j) g^{-jk}, as an N x N product in blocks
    invN = pow(N, P - 2, P)
    j = np.arange(N, dtype=np.int64)
    h = np.empty(N, dtype=np.int64)
    for k0 in range(0, N, 256):
        ks = np.arange(k0, min(N, k0 + 256), dtype=np.int64)
        W = R[(-np.outer(ks, j)) % N]                       # g^{-jk}
        h[k0:k0+len(ks)] = (W * Hval % P).sum(axis=1) % P * invN % P
    return h

def coeffs_mod(m, p, w, d, qs, C, ks, P, nvars):
    """[x^k] x (1+x)^C H(x) modulo P, for k in ks."""
    N = 1 << (nvars + 1).bit_length()
    h = [int(t) for t in H_coeffs_mod(m, p, w, d, qs, P, N)]
    assert all(t == 0 for t in h[nvars + 1:])               # sanity: deg H <= nvars
    fact = [1] * (C + 1)
    for i in range(1, C + 1): fact[i] = fact[i-1] * i % P
    inv_fact_C = pow(fact[C], P - 2, P)
    invf = [1] * (C + 1); invf[C] = inv_fact_C
    for i in range(C, 0, -1): invf[i-1] = invf[i] * i % P
    out = []
    for k in ks:
        tot = 0
        for jj in range(nvars + 1):
            r = k - 1 - jj
            if 0 <= r <= C and h[jj]:
                tot += h[jj] * (fact[C] * invf[r] % P * invf[C - r] % P)
        out.append(tot % P)
    return out

def nvars_of(m, p, d, qs):
    return m * p + (1 + d) * sum(qs)

def ntt_primes(N, count):
    """The `count` largest primes P < 2^31 with P = 1 (mod N)."""
    out, c = [], (1 << 31) // N - 1
    while len(out) < count and c > 0:
        if is_prime(c * N + 1): out.append(c * N + 1)
        c -= 1
    assert len(out) == count, "not enough NTT primes"
    return out

def small_tests():
    cases = [(2,1,2,0,[1,1]), (2,1,2,1,[1,1]), (3,1,2,0,[1,1,1]), (3,1,3,0,[1,1,1]),
             (2,1,2,0,[1,2]), (3,1,2,1,[1,1,1]), (2,2,1,0,[1,2]), (3,1,1,1,[1,1,1]),
             (3,1,3,1,[1,0,1]), (4,1,2,0,[1,1,0,1])]
    for m, p, w, d, qs in cases:
        adj, nc, _ = build(m, p, w, d, qs)
        n = len(adj); assert n <= 21, n
        bf = brute(adj)
        nv = nvars_of(m, p, d, qs)
        for P in ntt_primes(1 << 12, 2):
            got = coeffs_mod(m, p, w, d, qs, nc + 1, range(n + 1), P, nv)
            assert got == [c % P for c in bf], (m, p, w, d, qs)
        print(f"  brute force agrees: (m,p,w,d,qs)={(m,p,w,d,qs)}, n={n}", flush=True)

def main(cert_path):
    cert = json.load(open(cert_path))
    m, p, w, d, Q = (cert[k] for k in "m p w d Q".split())
    qs = [(i + 1) * Q // m - i * Q // m for i in range(m)]
    adj, nc, edges = build(m, p, w, d, qs)
    n = len(adj)
    print(f"graph: n={n}, edges={edges}, clauses={nc}: simple, connected, bipartite, no isolated vertex")
    assert (n, edges) == (cert["vertices"], cert["edges"])
    ks = cert["degrees"]
    nv = nvars_of(m, p, d, qs)
    N = 1 << (nv + 1).bit_length()
    # every coefficient is < 2^n; each prime exceeds 2^30
    primes = ntt_primes(N, (n + 64) // 30 + 1)
    print(f"{len(primes)} primes of ~31 bits, N={N}", flush=True)
    t0 = time.time()
    M, vals = 1, [0] * len(ks)
    for idx, P in enumerate(primes):
        res = coeffs_mod(m, p, w, d, qs, nc + 1, ks, P, nv)
        # incremental CRT
        inv = pow(M % P, P - 2, P)
        for i, r in enumerate(res):
            t = (r - vals[i]) % P * inv % P
            vals[i] += M * t
        M *= P
        if idx % 100 == 0:
            print(f"  prime {idx}/{len(primes)}  {time.time()-t0:.0f}s", flush=True)
    ref = [int(s) for s in cert["coefficients"]]
    print("exact CRT reconstruction equals certificate:", vals == ref)
    assert vals == ref
    a, b, c = vals
    print(f"d_t({ks[0]}) > d_t({ks[1]}) < d_t({ks[2]}):", a > b < c,
          f"; ratios {a*10**9//b/1e9:.9f}, {c*10**9//b/1e9:.9f}; {len(str(b))} digits")

if __name__ == "__main__":
    print("small cases vs brute force:")
    small_tests()
    for path in sys.argv[1:]:
        print("\n==", path); main(path)
