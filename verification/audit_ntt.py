"""Independent pure-Python audit of the Theorem B total domination counterexamples.

Checks:
1. Graph simplicity, connectivity, bipartiteness, and minimum degree >= 1.
2. Exact open-neighborhood total domination brute-force (2^n) vs transfer-matrix
   formula on seven small parameter sets.
3. Independent pure-Python modular NTT verification (no FLINT, no shared code) of
   the exact target coefficients in cert_22601.json and cert_25423.json modulo
   two distinct NTT-friendly primes (998244353 and 1004535809).
"""
import json
import sys
from collections import deque
from pathlib import Path

sys.set_int_max_str_digits(0)

BASE = Path(__file__).resolve().parent


def build_graph(m, p, w, d, qs):
    assert len(qs) == m and 1 <= w <= m
    adj = []

    def add_v(k=1):
        s = len(adj)
        for _ in range(k):
            adj.append([])
        return list(range(s, s + k))

    def add_e(u, v):
        adj[u].append(v)
        adj[v].append(u)

    A = [add_v(p) for _ in range(m)]
    B = [add_v(q) for q in qs]
    Z = [[add_v(d) for _ in block] for block in B]
    nv = len(adj)

    clause_count = 0
    for i in range(m):
        for j, b_v in enumerate(B[i]):
            for z_v in Z[i][j]:
                (c,) = add_v(1)
                add_e(c, b_v)
                add_e(c, z_v)
                clause_count += 1
            for s in range(w):
                for a_v in A[(i - s) % m]:
                    (c,) = add_v(1)
                    add_e(c, b_v)
                    add_e(c, a_v)
                    clause_count += 1

    hub, leaf = add_v(2)
    add_e(hub, leaf)
    for v in range(nv):
        add_e(hub, v)

    n = len(adj)
    edge_pairs = set()
    for u, nbrs in enumerate(adj):
        assert len(nbrs) >= 1, f"isolated vertex {u}"
        assert len(nbrs) == len(set(nbrs)), f"parallel edge at {u}"
        assert u not in nbrs, f"self-loop at {u}"
        for v in nbrs:
            edge_pairs.add((min(u, v), max(u, v)))

    color = {0: 0}
    dq = deque([0])
    while dq:
        u = dq.popleft()
        for v in adj[u]:
            if v not in color:
                color[v] = 1 - color[u]
                dq.append(v)
            else:
                assert color[v] != color[u], "not bipartite"
    assert len(color) == n, "not connected"
    return adj, nv, clause_count, len(edge_pairs)


def brute_total_dom_poly(adj):
    n = len(adj)
    masks = [0] * n
    for u, nbrs in enumerate(adj):
        m = 0
        for v in nbrs:
            m |= 1 << v
        masks[u] = m
    coeffs = [0] * (n + 1)
    for subset in range(1, 1 << n):
        ok = True
        for m in masks:
            if (subset & m) == 0:
                ok = False
                break
        if ok:
            coeffs[subset.bit_count()] += 1
    return coeffs


def eval_formula_mod(m, p, w, d, qs, c, x_val, mod):
    """Evaluate D_t(G, x_val) mod `mod` directly via scalar w x w transfer matrix."""
    xp = pow(x_val, p, mod)
    a_nonfull = (pow(1 + x_val, p, mod) - xp) % mod
    g_forced = (x_val * pow(1 + x_val, d, mod)) % mod
    g_free = (g_forced + pow(x_val, d, mod)) % mod

    def mat_mul(X, Y):
        out = [[0] * w for _ in range(w)]
        for i in range(w):
            row = X[i]
            for k in range(w):
                rk = row[k]
                if rk:
                    yk = Y[k]
                    for j in range(w):
                        out[i][j] = (out[i][j] + rk * yk[j]) % mod
        return out

    mats = {}
    for q in set(qs):
        gfq = pow(g_forced, q, mod)
        gfrq = pow(g_free, q, mod)
        M = [[0] * w for _ in range(w)]
        for s in range(w):
            M[s][0] = (M[s][0] + a_nonfull * gfq) % mod
            if s < w - 1:
                M[s][s + 1] = (M[s][s + 1] + xp * gfq) % mod
            else:
                M[s][w - 1] = (M[s][w - 1] + xp * gfrq) % mod
        mats[q] = M

    prod = [[1 if i == j else 0 for j in range(w)] for i in range(w)]
    for q in qs:
        prod = mat_mul(prod, mats[q])

    tr = sum(prod[i][i] for i in range(w)) % mod
    return (x_val * pow(1 + x_val, c + 1, mod) % mod) * tr % mod


def poly_coeffs_mod_ntt(m, p, w, d, qs, c, mod, root_prim):
    """Compute exact full polynomial D_t(G, x) mod `mod` via NTT."""
    n_total = m * p + (1 + d) * sum(qs) + c + 2
    N = 1
    while N <= n_total:
        N <<= 1
    assert (mod - 1) % N == 0
    g = pow(root_prim, (mod - 1) // N, mod)
    evals = [0] * N
    w_k = 1
    for k in range(N):
        evals[k] = eval_formula_mod(m, p, w, d, qs, c, w_k, mod)
        w_k = (w_k * g) % mod

    g_inv = pow(g, mod - 2, mod)
    j = 0
    for i in range(1, N):
        bit = N >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            evals[i], evals[j] = evals[j], evals[i]

    length = 2
    while length <= N:
        wlen = pow(g_inv, N // length, mod)
        half = length >> 1
        for i in range(0, N, length):
            wn = 1
            for k in range(half):
                u = evals[i + k]
                v = (evals[i + k + half] * wn) % mod
                evals[i + k] = (u + v) % mod
                evals[i + k + half] = (u - v) % mod
                wn = (wn * wlen) % mod
        length <<= 1

    inv_N = pow(N, mod - 2, mod)
    return [(val * inv_N) % mod for val in evals[: n_total + 1]]


def main():
    print("=== Step 1: Independent brute-force (2^n) check on 7 small graphs ===")
    small_cases = [
        (2, 1, 2, 0, [1, 1]),
        (2, 1, 2, 1, [1, 1]),
        (3, 1, 2, 0, [1, 1, 1]),
        (3, 1, 3, 0, [1, 1, 1]),
        (2, 1, 2, 0, [1, 2]),
        (3, 1, 2, 1, [1, 1, 1]),
        (2, 2, 1, 0, [1, 2]),
    ]
    mod = 998244353
    for m, p, w, d, qs in small_cases:
        adj, nv, c, ne = build_graph(m, p, w, d, qs)
        assert len(adj) <= 19, f"too large for brute force: {len(adj)}"
        bf = brute_total_dom_poly(adj)
        for x_val in [1, 2, 3, 7, 123456]:
            bf_val = 0
            xp = 1
            for coeff in bf:
                bf_val = (bf_val + coeff * xp) % mod
                xp = (xp * x_val) % mod
            f_val = eval_formula_mod(m, p, w, d, qs, c, x_val, mod)
            assert bf_val == f_val, f"MISMATCH on {(m, p, w, d, qs)} at x={x_val}"
        print(
            f"  PASS brute force: {(m, p, w, d, qs)} -> n={len(adj)}, edges={ne}, "
            f"gamma_t={next(k for k, v in enumerate(bf) if v)}"
        )

    print("\n=== Step 2: Independent NTT-mod-prime audit of cert_22601.json and cert_25423.json ===")
    primes = [(998244353, 3), (1004535809, 3)]
    for fname in ["cert_22601.json", "cert_25423.json"]:
        cert = json.loads((BASE / fname).read_text())
        m, p, w, d, Q = cert["m"], cert["p"], cert["w"], cert["d"], cert["Q"]
        qs = [(i + 1) * Q // m - i * Q // m for i in range(m)]
        adj, nv, c, ne = build_graph(m, p, w, d, qs)
        assert len(adj) == cert["vertices"]
        assert ne == cert["edges"]
        assert nv == cert["variables"]
        assert c == cert["clauses"]
        degs = cert["degrees"]
        exact_ints = [int(s) for s in cert["coefficients"]]
        assert degs[0] < degs[1] < degs[2]
        assert exact_ints[0] > exact_ints[1] and exact_ints[2] > exact_ints[1]
        print(f"\n  {fname}: n={len(adj)}, edges={ne}, simple+connected+bipartite+min_deg>=1 VERIFIED")
        scale = 1 << (max(exact_ints).bit_length() - 50)
        print(f"    Strict valley check on exact JSON ints ({len(str(exact_ints[1]))} digits):")
        print(f"      d_t({degs[0]}) > d_t({degs[1]}): {exact_ints[0] > exact_ints[1]}")
        print(f"      d_t({degs[2]}) > d_t({degs[1]}): {exact_ints[2] > exact_ints[1]}")
        print(f"      ratio left/valley  = {(exact_ints[0] // scale) / (exact_ints[1] // scale):.10f}")
        print(f"      ratio right/valley = {(exact_ints[2] // scale) / (exact_ints[1] // scale):.10f}")

        for mod_p, prim_root in primes:
            coeffs_mod = poly_coeffs_mod_ntt(m, p, w, d, qs, c, mod_p, prim_root)
            for idx, k in enumerate(degs):
                assert coeffs_mod[k] == exact_ints[idx] % mod_p, (
                    f"MOD MISMATCH for {fname} deg {k} mod {mod_p}"
                )
            print(f"    Independent pure-Python NTT mod {mod_p}: ALL 3 coefficients match")

    print("\nALL INDEPENDENT AUDITS PASSED.")


if __name__ == "__main__":
    main()
