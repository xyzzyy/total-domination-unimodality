"""Exact transfer-matrix certificate generator for connected bipartite
counterexamples to Alikhani-Jafari (2016) Conjecture 2.9.

Requires python-flint.
"""
from collections import deque
from functools import lru_cache
import json
import math
import sys
from flint import fmpz_poly as Poly

X = Poly([0, 1])
ONE = Poly([1])
ZERO = Poly([])
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def sizes(m, Q):
    return [(i + 1) * Q // m - i * Q // m for i in range(m)]


def graph(m, p, w, d, qs):
    """Build every edge. Variable blocks A and switch blocks B are cyclic."""
    adj = []

    def vertices(count):
        start = len(adj)
        adj.extend(set() for _ in range(count))
        return list(range(start, len(adj)))

    def edge(a, b):
        if a == b or b in adj[a]:
            raise ValueError("invalid edge")
        adj[a].add(b)
        adj[b].add(a)

    def clause(a, b):
        (c,) = vertices(1)
        edge(c, a)
        edge(c, b)

    a = [vertices(p) for _ in range(m)]
    b = [vertices(q) for q in qs]
    private = [[vertices(d) for _ in block] for block in b]
    variable_count = len(adj)
    for i, block in enumerate(b):
        for j, v in enumerate(block):
            for z in private[i][j]:
                clause(v, z)
            for step in range(w):
                for u in a[(i - step) % m]:
                    clause(v, u)
    clause_count = len(adj) - variable_count
    hub, leaf = vertices(2)
    edge(hub, leaf)
    for v in range(variable_count):
        edge(hub, v)
    side = {hub: 0}
    todo = deque([hub])
    while todo:
        v = todo.popleft()
        for u in adj[v]:
            if u not in side:
                side[u] = 1 - side[v]
                todo.append(u)
            if side[u] == side[v]:
                raise ValueError("odd cycle")
    if len(side) != len(adj):
        raise ValueError("disconnected")
    return adj, variable_count, clause_count


def brute_total_dom(adj):
    n = len(adj)
    masks = [sum(1 << w for w in nb) for nb in adj]
    counts = [0] * (n + 1)
    for s in range(1 << n):
        if all(s & m for m in masks):
            counts[s.bit_count()] += 1
    return counts


def from_left(m, p, w, d, qs):
    """Forward transfer-matrix recurrence (Lemma 5)."""
    af = X**p
    ab = (1 + X) ** p - af
    good = X * (1 + X) ** d
    free = good + X**d
    bits = {q: (ab * good**q, af * good**q, af * free**q) for q in set(qs)}
    result = ZERO
    for start in range(w):
        states = [ZERO] * w
        states[start] = ONE
        for q in qs:
            bad, partial, full = bits[q]
            nxt = [sum(states, ZERO) * bad] + [v * partial for v in states[:-1]]
            nxt[-1] += states[-1] * full
            states = nxt
        result += states[start]
    return result


def from_right(m, p, w, d, qs):
    """Independent backward transfer-matrix recurrence via divide-and-conquer."""
    a_all = (1 + X) ** p
    a_full = X**p
    selected = X * (1 + X) ** d
    omitted = X**d

    @lru_cache(None)
    def trans(seq):
        if len(seq) == 1:
            q = seq[0]
            unmarked = selected**q
            marked = (selected + omitted) ** q - unmarked
            mat = [[ZERO for _ in range(w)] for _ in range(w)]
            for ttl in range(w):
                mat[ttl][max(0, ttl - 1)] = unmarked * (a_full if ttl else a_all)
                mat[ttl][w - 1] += marked * a_full
            return mat
        mid = len(seq) // 2
        left, right = trans(seq[:mid]), trans(seq[mid:])
        return [
            [
                sum((u * v for u, v in zip(row, col) if u and v), ZERO)
                for col in zip(*right)
            ]
            for row in left
        ]

    mat = trans(tuple(reversed(qs)))
    return sum((mat[i][i] for i in range(w)), ZERO)


def at_degrees(h, c, indices):
    """Extract target coefficients of x(1+x)^(c+1) H(x) by exact binomial convolution."""
    n = c + 1
    coeffs = [int(v) for v in h.coeffs()]
    answer = []
    for k in indices:
        shift = k - 1
        lo = max(0, shift - n)
        hi = min(len(coeffs) - 1, shift)
        if lo > hi:
            answer.append(0)
            continue
        r = shift - lo
        b = math.comb(n, r)
        total = 0
        for j in range(lo, hi + 1):
            total += b * coeffs[j]
            b = b * r // (n - r + 1)
            r -= 1
        answer.append(total)
    return answer


def check_small():
    for m, p, w, d, qs in [
        (2, 1, 2, 0, [1, 1]),
        (2, 1, 2, 1, [1, 1]),
        (3, 1, 2, 0, [1, 1, 1]),
        (2, 1, 2, 0, [1, 2]),
    ]:
        adj, nv, c = graph(m, p, w, d, qs)
        if len(adj) > 18:
            raise ValueError("small graph order")
        l = from_left(m, p, w, d, qs)
        r = from_right(m, p, w, d, qs)
        direct = brute_total_dom(adj)
        if l != r or at_degrees(l, c, range(len(adj) + 1)) != direct:
            raise ArithmeticError("graph enumeration")
    print("Both graph recurrences matched all subset counts on four small graphs.", flush=True)


def certify(m, p, w, d, Q, indices, output):
    qs = sizes(m, Q)
    adj, nv, c = graph(m, p, w, d, qs)
    graph_order = nv + c + 2
    edges = sum(map(len, adj)) // 2
    print(f"Connected bipartite graph: {graph_order} vertices, {edges} edges.", flush=True)
    left = from_left(m, p, w, d, qs)
    print("First exact variable polynomial complete.", flush=True)
    right = from_right(m, p, w, d, qs)
    if left != right or left.degree() != nv:
        raise ArithmeticError("exact polynomial mismatch")
    vals = at_degrees(left, c, indices)
    full = right * X * (1 + X) ** (c + 1)
    if vals != [int(full[k]) for k in indices]:
        raise ArithmeticError("coefficient mismatch")
    if not (indices[0] < indices[1] < indices[2] and min(vals[0], vals[2]) > vals[1]):
        raise ArithmeticError("no strict valley")
    normalization = 1 << (max(vals).bit_length() - 1)
    scaled = [v * 10**8 // normalization for v in vals]
    peaks = [i for i in range(1, graph_order) if full[i - 1] < full[i] > full[i + 1]]
    result = dict(
        m=m,
        p=p,
        w=w,
        d=d,
        Q=Q,
        vertices=graph_order,
        edges=edges,
        variables=nv,
        clauses=c,
        degrees=indices,
        strict_peaks=peaks,
        coefficients=[str(v) for v in vals],
        scale_power=normalization.bit_length() - 1,
        scaled_floors=scaled,
    )
    with open(output, "w") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print("Integer counts agree. Scaled floors:", scaled, "strict peaks:", peaks, flush=True)


if __name__ == "__main__":
    check_small()
    if len(sys.argv) > 1:
        m, p, w, d, Q, i, j, k = map(int, sys.argv[1:9])
        certify(m, p, w, d, Q, [i, j, k], sys.argv[9])
