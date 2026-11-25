#set document(title: "Counterexamples to the Unimodality of Total Domination Polynomials", author: "Andrew MacKenzie")
#set page(paper: "us-letter", margin: (x: 1.0in, top: 0.77in, bottom: 0.77in), numbering: "1")
#set text(font: "New Computer Modern", size: 10.8pt, lang: "en")
#show math.equation: set text(font: "New Computer Modern Math")
#set par(justify: true, leading: 0.65em, spacing: 0.65em, first-line-indent: 1.5em)
#set heading(numbering: (..nums) => numbering("1.1", ..nums))
#show heading.where(level: 1): set text(size: 14pt)
#show heading.where(level: 2): set text(size: 11pt)
#show figure.caption: set text(size: 10pt)
#show figure.where(kind: table): set block(below: 1.1em)
#show figure.where(kind: image): set block(below: 1.1em)
#show figure.where(kind: "thm"): it => block(width: 100%, breakable: false, above: 1em, below: 1em, align(left, it.body))
#let env(sup, title: none, italic: true, body) = figure(
  kind: "thm", supplement: sup, numbering: "1", outlined: false,
  [#strong[#sup #context counter(figure.where(kind: "thm")).display()#if title != none [ (#title)].] #if italic {emph(body)} else {body}],
)
#let result(letter, title, body) = block(breakable: false, above: 0.95em, below: 0.95em)[
  *Theorem #letter (#title).* #emph(body)
]
#let proof = emph[Proof.]
#let qed = h(0.45em) + sym.square.stroked
#let fam = math.cal
#let lg = math.op("log")
#let tr = math.op("tr")
#let Vvar = $V_("var")$

#align(center)[
  #text(16pt, weight: "bold")[Counterexamples to the Unimodality of\ Total Domination Polynomials]
  #v(0.5em)
  #text(11pt)[Andrew MacKenzie] \
  #text(9pt)[#link("mailto:andrew@xyzzyy.dev")[andrew\@xyzzyy.dev] #h(1em) #link("https://orcid.org/0009-0001-3913-4693")[ORCID: 0009-0001-3913-4693]] \
  #text(9pt)[November 2026]
]
#v(1.0em)
#block(inset: (x: 2.2em))[
  #align(center)[*Abstract*]
  #v(0.35em)
  #set par(first-line-indent: (amount: 1.5em, all: true))
  The total domination polynomial $D_t (G,x) = sum_(k=0)^n d_t (G,k) x^k$ of a finite graph $G$ without isolated vertices counts its total dominating sets by cardinality. Alikhani and Jafari conjectured in 2016 that $D_t (G,x)$ is unimodal for every such graph. We construct connected bipartite graphs whose total domination polynomials fail to be unimodal. An elementary analytic argument exhibits a counterexample on 4,094,226,002 vertices whose valley coefficient lies more than $2^68$ times below two surrounding coefficients; the non-unimodality of this graph is formally verified in Lean 4 without external axioms. Exact transfer-matrix computations give two smaller counterexamples on 22,601 and 25,423 vertices, each strictly bimodal on its support.
]

#v(1.5em)
= Introduction

Let $G$ be a finite simple graph with $n$ vertices and no isolated vertices. A subset $S subset.eq V(G)$ is a *total dominating set* if every vertex of $G$ has at least one neighbor in $S$ @HY. Writing $d_t (G,k)$ for the number of total dominating sets of cardinality $k$, the *total domination polynomial* of $G$ is
$ D_t (G,x) = sum_(k=0)^n d_t (G,k) x^k. $
A sequence $(a_0, dots, a_n)$ of real numbers is *unimodal* if it is weakly increasing up to some index and weakly decreasing thereafter—equivalently, if it contains no *strict valley*, meaning no triple $i < j < k$ with $a_j < min(a_i,a_k)$.

In 2016, Alikhani and Jafari conjectured that the total domination polynomial of every graph without isolated vertices is unimodal (@AJ16, Conjecture 2.9). In the same work, they established unimodality for complete graphs and friendship graphs and used Hall’s marriage theorem to show that $d_t (G,i) <= d_t (G,i+1)$ for all $0 <= i < n/2$ (@AJ16, Theorem 2.8); subsequent work identified additional unimodal families and provided computational evidence on small graphs @AJ21.

The corresponding question for ordinary (closed-neighborhood) domination polynomials, posed earlier by Alikhani and Peng @AP, has been extensively studied. Beaton and Brown proved unimodality for paths, cycles, complete multipartite graphs, and asymptotically almost all graphs, while also showing that ordinary domination polynomials need not be log-concave @BB. Further unimodal families, root bounds, and partial monotonicity results were obtained by Bencs, Csikvári, and Regts @BCR, Zhang @Z, Burcroff and O’Brien @BO, and Omar @O. Recently, Chalmers circulated a preprint disproving the Alikhani–Peng conjecture via connected bounded-degree bipartite graphs with arbitrarily many deep peaks @Chalmers26. Total domination behaves differently from ordinary domination because selected vertices must themselves be dominated by other selected vertices, and the Alikhani–Jafari conjecture had remained open.

In this note we construct a family of connected bipartite graphs whose total domination polynomials fail to be unimodal. A single hub–leaf gadget forces the hub into every total dominating set, reducing the remaining constraints to a cyclic two-variable clause system with two competing pure phases of nearly equal total mass but well-separated typical cardinalities. A Peierls-type transfer-matrix bound suppresses mixed configurations, leaving a strict valley between the two peaks. Tuning the parameters analytically gives an elementary, machine-verified counterexample, while exact transfer-matrix computations produce much smaller ones.

#result("A", "Analytic counterexample")[
  The graph $G = G(18000,210,359)$ defined in @sec-construction is simple, connected, and bipartite, has no isolated vertices, and has $4 thin 094 thin 226 thin 002$ vertices. At indices $k_1 = 2 thin 050 thin 344 thin 001$, $k_2 = 2 thin 050 thin 725 thin 001$, and $k_3 = 2 thin 051 thin 157 thin 001$,
  $ d_t (G,k_2) < 2^(-68) min(d_t (G,k_1),d_t (G,k_3)). $
]

#result("B", "Smaller computer-assisted counterexamples")[
  There exist connected bipartite graphs $G_1$ and $G_2$ on $22 thin 601$ and $25 thin 423$ vertices, respectively, satisfying
  $ d_t (G_1, 11 thin 843) > d_t (G_1, 11 thin 858) < d_t (G_1, 11 thin 888),
    quad d_t (G_2, 13 thin 299) > d_t (G_2, 13 thin 356) < d_t (G_2, 13 thin 380). $
  Each coefficient sequence has support $[Q+1, n]$ (with $Q=969$ for $G_1$ and $Q=1090$ for $G_2$), has no equal adjacent nonzero entries, and is strictly bimodal with its unique local maxima at the outer indices above.
]

= Construction <sec-construction>

Let $m,p >= 1$, $1 <= w <= m$, $d >= 0$, and $q_0, dots, q_(m-1) >= 0$ be integers with $Q = sum_(i=0)^(m-1) q_i >= 1$, and set $P = m p$. We define a graph $G_(w,d)(m,p; bold(q))$, with block indices taken modulo $m$, on the following disjoint vertex sets:

- a *hub* $h$ and a pendant *leaf* $ell$ adjacent only to $h$;
- *variable vertices* $A_(i,a)$, $B_(i,b)$, and $Z_(i,b,e)$ for $i in ZZ_m$, $0 <= a < p$, $0 <= b < q_i$, and $0 <= e < d$, each adjacent to $h$;
- *private clause vertices* $z_(i,b,e)$ adjacent to $B_(i,b)$ and $Z_(i,b,e)$ for each $(i,b,e)$;
- *coupling clause vertices* $c_(i,b,s,a)$ adjacent to $B_(i,b)$ and $A_(i-s,a)$ for each $(i,b,a)$ and $0 <= s < w$.

No other vertices or edges are present. Denote the set of variable vertices by #Vvar, and call the leaf together with all clause vertices the *free vertices*. There are $|Vvar| = P + (1+d)Q$ variable vertices and $Q(d + w p)$ clause vertices, so setting $C = 1 + Q(d + w p)$ for the number of free vertices gives
$ |V(G)| = 1 + C + P + (1+d)Q, quad |E(G)| = 1 + P + (1+d)Q + 2Q(d + w p). $

For the analytic proof in Section 3 we specialize to the uniform case $w=3$, $d=1$, and $q_i = q >= 1$ for all $i$, writing $G(m,p,q) = G_(3,1)(m,p;(q,dots,q))$ for $m >= 3$. In this case we abbreviate $Z_(i,b,0)$ and $z_(i,b,0)$ to $Z_(i,b)$ and $z_(i,b)$, so that $Q = m q$ and $C = 1 + m q + 3 m p q$.

#figure(
  image("construction.svg", width: 91%),
  caption: [Clause vertices incident to a single switch vertex $B_(i,b)$ in $G(m,2,q)$. The variable vertices $A_(i-s,a)$ belong to blocks $i-2$, $i-1$, and $i$.],
) <fig-construction>

#env("Lemma", title: [Characterization of total dominating sets])[
  A subset $S subset.eq V(G)$ is a total dominating set if and only if $h in S$ and the variable subset $X = S inter Vvar$ intersects the two-element neighborhood of every clause vertex. Call such a subset $X subset.eq Vvar$ *valid*. The membership of every free vertex in $S$ is unconstrained.
] <lem-tds>

#proof Because $ell$ has unique neighbor $h$, any total dominating set $S$ must contain $h$. Moreover, every clause vertex has degree two with both neighbors in #Vvar, so $X = S inter Vvar$ must contain at least one of the two neighbors of every clause vertex, i.e., $X$ is valid.

Conversely, suppose $h in S$ and $X$ is valid. Then $h$ dominates $ell$ and every vertex of #Vvar, while validity ensures that every clause vertex has a neighbor in $X subset.eq S$. It remains only to check that $h$ itself has a neighbor in $S$. Since $Q >= 1$, there exists a vertex $B_(i,b)$. If $B_(i,b) in X$, then $B_(i,b)$ dominates $h$. Otherwise $B_(i,b) in.not X$; validity then forces $Z_(i,b,0) in X$ when $d >= 1$ (via $z_(i,b,0)$), and forces $A_(i,0) in X$ when $d = 0$ (via $c_(i,b,0,0)$, which exists because $w, p >= 1$). In either case $X$ is nonempty and therefore dominates $h$. Since no free vertex is needed to dominate any vertex once $h in S$ and $X$ is valid, all $C$ free vertices may be chosen independently. #qed

#env("Lemma", title: [Structural properties])[
  The graph $G_(w,d)(m,p; bold(q))$ is simple, connected, and bipartite, and has no isolated vertices.
] <lem-graph>

#proof Every edge joins a vertex in ${h} union {"clause vertices"}$ to a vertex in ${ell} union Vvar$, so the graph is bipartite. No edge is repeated and no loop is formed because all clause vertices are distinct and each is joined to two distinct variable vertices ($B_(i,b)$ is disjoint from all $A$- and $Z$-vertices). Every vertex in ${ell} union Vvar$ is adjacent to $h$, and every clause vertex is adjacent to some $B_(i,b)$ and thus lies at distance two from $h$; hence $G$ is connected and has minimum degree at least one. #qed

#block(breakable: false, above: 0.75em)[
  By @lem-tds, summing over all subsets of free vertices and all valid variable subsets yields the factorization
  #set math.equation(numbering: "(1)")
  $ D_t (G,x) = x(1+x)^C H(x), quad H(x) = sum_(X "valid") x^(|X|). $ <eq-factor>
]

= Analytic proof of Theorem A

== Two pure families and a Chernoff valley bound

Fix $G = G(m,p,q)$ with $m >= 3$ and $3 divides Q$, and set $N_1 = C + P + Q$. We cover all valid variable sets $X subset.eq Vvar$ by three families:
- $fam(I)$ consists of all valid sets containing every $B$ vertex;
- $fam(I I)$ consists of all valid sets containing every $A$ vertex;
- $fam(I I I)$ consists of all remaining valid sets (those omitting at least one $B$ vertex and at least one $A$ vertex).

Notice that $fam(I)$ and $fam(I I)$ are not disjoint (their intersection contains valid sets with all $A$ and all $B$ vertices), which works in our favor for both lower and upper bounds.

Within $fam(I)$, every clause vertex is already dominated by its $B$ neighbor, so all $P$ vertices of type $A$ and all $Q$ vertices of type $Z$ are unconstrained; together with the hub and $C$ free vertices, $fam(I)$ contributes $x^(1+Q)(1+x)^(N_1)$ to $D_t (G,x)$. Within $fam(I I)$, every coupling clause $c_(i,b,s,a)$ is already dominated by its $A$ neighbor, leaving only the private clauses $z_(i,b)$, which allow three choices for each pair $(B_(i,b), Z_(i,b))$: two of size one and one of size two. Thus $fam(I I)$ contributes $x^(1+P+Q)(1+x)^C (2+x)^Q$ to $D_t (G,x)$.

For the left peak, set $k_1 = 1 + Q + floor(N_1 / 2)$. Because the central binomial coefficient is a maximum among the $N_1 + 1$ terms summing to $2^(N_1)$, restricting to $fam(I)$ gives
$ d_t (G,k_1) >= binom(N_1, floor(N_1/2)) >= B_1 := 2^(N_1)/(N_1 + 1). $

For the right peak, set $k_3 = 1 + P + Q + floor(C/2) + Q/3$. Let $a_j = binom(Q,j) 2^(Q-j)$ for $0 <= j <= Q$. Since $a_(j+1)/a_j = (Q-j)/(2(j+1))$, the sequence $(a_j)$ increases up to $j = Q/3$ and decreases thereafter, so $a_(Q/3)$ is a maximum among the $Q+1$ terms summing to $3^Q$. Retaining only the single convolution term $(floor(C/2), Q/3)$ from $fam(I I)$ gives
$ d_t (G,k_3) >= binom(C, floor(C/2)) binom(Q, Q/3) 2^(Q - Q/3)
  >= B_3 := (2^C 3^Q)/((C+1)(Q+1)). $

For an intermediate index $k_2$ satisfying $1 + Q <= k_2 <= 1 + Q + N_1$ and $1 + P + Q <= k_2 <= 1 + P + C + 2Q$, put $j_1 = k_2 - 1 - Q$ and $s = k_2 - 1 - P$, and write $H_3(x) = sum_(X in fam(I I I)) x^(|X|)$. Because $fam(I) union fam(I I) union fam(I I I)$ covers all valid variable sets, $d_t (G,k_2) <= U_1 + U_2 + U_3$, where
$ U_1 = binom(N_1, j_1), quad U_2 = [x^s](1+x)^C (x(2+x))^Q, $
$ U_3 = [x^(k_2)] x(1+x)^C H_3(x) <= 2^C |fam(I I I)|. $
The final inequality holds because every valid variable set in $fam(I I I)$ has $2^C$ total extensions over the free vertices.

#env("Lemma", title: [Chernoff coefficient bound])[
  If $f(x) = sum_(r >= 0) f_r x^r$ has nonnegative coefficients and $t > 0$, then $[x^a] f <= f(t) / t^a$ for every integer $a >= 0$.
] <lem-coeff>

#proof Every term in the sum $f(t) = sum_(r >= 0) f_r t^r$ is nonnegative, so $f_a t^a <= f(t)$. #qed

Applying @lem-coeff to $(1+x)^(N_1)$ at $t = (T+1)/T$ with $T = 2675$ (close to the minimizer $j_1 / (N_1 - j_1)$), and to $(1+x)^C (x(2+x))^Q$ at $x = alpha / beta$ with $(alpha, beta) = (2374, 2375)$, gives
$ U_1 <= (1+t)^(N_1)/t^(j_1), quad
  U_2 dot alpha^s beta^(C + 2Q - s) <= (alpha + beta)^C (alpha(alpha + 2beta))^Q. $ <eq-chernoff>

== Suppressing mixed configurations

For any valid set $X subset.eq Vvar$, define a cyclic binary word $tau in {0,1}^(ZZ_m)$ by setting $tau_j = 1$ if some $B_(j,b)$ is absent from $X$, and $tau_j = 0$ otherwise. Whenever $tau_j = 1$, the coupling clauses incident to that absent vertex force all $A$ vertices in blocks $j$, $j-1$, and $j-2$ into $X$. In particular, if $tau$ is constant, then either $tau equiv 0$ (all $B$ vertices present, so $X in fam(I)$) or $tau equiv 1$ (every block $A_j$ forced in by $tau_j = 1$, so $X in fam(I I)$). Every $X in fam(I I I)$ therefore has a nonconstant word $tau$, which must contain at least one index $i in ZZ_m$ with $(tau_i, tau_(i+1)) = (0,1)$.

#env("Lemma", title: [Mixed-family bound])[
  Suppose $L >= 1$ and $Lambda > 0$ satisfy $(2^(p+q) + 2^q L) L <= Lambda$ and $3^q (1 + L) <= Lambda$. Then
  $ |fam(I I I)| L^(m-1) <= m dot 2^q dot L dot Lambda^(m-1). $
] <lem-mixed>

#proof Fix a cyclic word $tau in {0,1}^(ZZ_m)$. In block $j$, the pairs $(B_(j,b), Z_(j,b))$ admit $2^q$ choices when $tau_j = 0$ (all $B_(j,b)$ present, each $Z_(j,b)$ optional) and $3^q - 2^q <= 3^q$ choices when $tau_j = 1$. Meanwhile, the $A$ vertices of block $j$ are forced into $X$ whenever any of $tau_j$, $tau_(j+1)$, or $tau_(j+2)$ equals $1$. Relaxing the constraint from $tau_(j+2)$ for an upper bound leaves at most $2^p$ choices for block $A_j$ when $tau_j = tau_(j+1) = 0$, and a single choice otherwise. Multiplying across blocks, the number of valid sets $X$ with word $tau$ is at most $product_(j in ZZ_m) W_(tau_j, tau_(j+1))$, where
$ W = mat(2^(p+q), 2^q; 3^q, 3^q). $

Each $X in fam(I I I)$ admits at least one position $i in ZZ_m$ with $(tau_i, tau_(i+1)) = (0,1)$. Fixing $i$ and summing the product of transition weights over all words of length $m-1$ starting at $tau_(i+1) = 1$ and returning to $tau_i = 0$ contributes $W_(0,1) (W^(m-1))_(1,0) = 2^q (W^(m-1))_(1,0)$. Summing over the $m$ choices of $i$ gives
$ |fam(I I I)| <= m dot 2^q (W^(m-1))_(1,0). $

Now set $v = (1, L)^(top)$. By hypothesis,
$ (W v)_0 = 2^(p+q) + 2^q L <= (Lambda / L) dot 1, quad (W v)_1 = 3^q (1 + L) <= (Lambda / L) dot L, $
so $W v <= (Lambda / L) v$ entrywise. Since $W$ has nonnegative entries, induction yields $W^(m-1) v <= (Lambda / L)^(m-1) v$. Finally, $(W^(m-1))_(1,0) <= (W^(m-1))_(1,0) dot 1 + (W^(m-1))_(1,1) dot L = (W^(m-1) v)_1 <= (Lambda / L)^(m-1) L$. Multiplying through by $m dot 2^q L^(m-1)$ completes the proof. #qed

== Parameters and rational certification for Theorem A

Specialize to $(m,p,q) = (18000, 210, 359)$. Then
$ C = 4 thin 077 thin 522 thin 001, quad P = 3 thin 780 thin 000, quad Q = 6 thin 462 thin 000, $
$ N_1 = 4 thin 087 thin 764 thin 001, quad n = 4 thin 094 thin 226 thin 002, $
and the chosen indices are $k_1 = 2 thin 050 thin 344 thin 001$, $k_2 = 2 thin 050 thin 725 thin 001$, and $k_3 = 2 thin 051 thin 157 thin 001$, giving $j_1 = 2 thin 044 thin 263 thin 000$ and $s = 2 thin 046 thin 945 thin 000$.

In @lem-mixed, choose $L = 2^18$ and $Lambda = 3^q (1 + L)$. The second hypothesis holds with equality. For the first, exact integer arithmetic gives $3^359 > 2^569$, whence
$ (2^(p+q) + 2^q L) L = 2^587 + 2^395 < 2^587 + 2^569 = 2^569 (1 + 2^18) < 3^359 (1 + L) = Lambda. $

#figure(
  table(
    columns: (auto, 1fr, auto),
    align: (left, left, right),
    inset: (x: 7pt, y: 6pt),
    stroke: (x, y) => (bottom: if y == 0 { 0.7pt } else { 0.35pt + luma(205) }),
    table.header([*Quantity*], [*Logarithmic expression*], [*Offset from* $N_1$]),
    [$lg_2 B_1$], [$N_1 - lg_2(N_1 + 1)$], [$-31.929$],
    [$lg_2 B_3$], [$C + Q lg_2 3 - lg_2(C + 1) - lg_2(Q + 1)$], [$-26.869$],
    [$lg_2 U_1$], [$N_1 lg_2(1 + t) - j_1 lg_2 t$], [$-102.462$],
    [$lg_2 U_2$], [$C lg_2(alpha + beta) + Q lg_2(alpha(alpha + 2beta))$ \ $quad - s lg_2 alpha - (C + 2Q - s) lg_2 beta$], [$-104.193$],
    [$lg_2 U_3$], [$C + lg_2 m + q + 18$ \ $quad + (m - 1)(q lg_2 3 + lg_2(1 + 2^(-18)))$], [$-150.087$],
  ),
  caption: [Logarithmic forms of the peak lower bounds $B_1, B_3$ and valley upper bounds $U_1, U_2, U_3$, together with their offsets from $N_1$ rounded to three decimal places. Here $t = 2676/2675$ and $(alpha, beta) = (2374, 2375)$.],
) <tab-margins>

To certify the numerical comparisons in @tab-margins without relying on floating-point rounding, write any positive rational $u$ as $u = 2^a y$ with $a in ZZ$ and $1 <= y < 2$, and set $z = (y-1)/(y+1) in [0, 1/3)$. From the identity $ln y = ln((1+z)/(1-z)) = 2 sum_(j=0)^infinity z^(2j+1)/(2j+1)$, truncating after $j = 23$ and bounding the tail by a geometric series gives $S(z) <= ln y <= S(z) + R(z)$, where
$ S(z) = 2 sum_(j=0)^23 z^(2j+1)/(2j+1), quad R(z) = (2 z^49)/(49(1 - z^2)). $
#block(breakable: false)[
  Evaluating the same bounds for $ln 2$ at $z = 1/3$ yields the two-sided rational enclosure
  $ a + S(z)/(S(1/3) + R(1/3)) <= lg_2 u <= a + (S(z) + R(z))/S(1/3). $
]
Substituting these enclosures into @tab-margins (with orientations reversed for negative multipliers) is a finite rational computation, carried out in exact fraction arithmetic by `verify_rational.py`. It certifies lower offsets strictly above $-31.930$ for both $lg_2 B_1$ and $lg_2 B_3$, and upper offsets strictly below $-102.461$, $-104.192$, and $-150.086$ for $lg_2 U_1$, $lg_2 U_2$, and $lg_2 U_3$, respectively. Every $U_r$ therefore satisfies $U_r < 2^(-70.5) min(B_1, B_3)$. Since $3 dot 2^(-70.5) < 2^(-68)$ (as $9 < 2^5$), we conclude that
$ d_t (G, k_2) <= U_1 + U_2 + U_3 < 2^(-68) min(B_1, B_3) <= 2^(-68) min(d_t (G, k_1), d_t (G, k_3)). $
Combining this with @lem-graph proves Theorem A. #qed

== Intuition: why two competing phases produce a valley

The mechanism behind Theorem A is probabilistic. Families $fam(I)$ and $fam(I I)$ have total masses $2^C 2^(P+Q)$ and $2^C 3^Q$, which stay closely balanced whenever $p/q approx lg_2(3/2) approx 0.58496$. Choosing the convergent $p/q = 210/359$ leaves an imbalance of only $q lg_2 3 - (p+q) approx 0.001538$ bits per block—about $27.7$ bits across the entire ring.

Conditioned on lying in $fam(I)$ or $fam(I I)$, the cardinality of a uniformly random total dominating set is distributed as
$ 1 + Q + "Bin"(N_1, 1/2)
  quad "and" quad
  1 + P + Q + "Bin"(C, 1/2) + "Bin"(Q, 1/3), $
respectively, where the two binomial summands in the second law are independent. Their means are separated by $P/2 - Q/6 = m(3p - q)/6 = 813 thin 000$, while their standard deviations are approximately $31 thin 968$ and $31 thin 950$—a separation of roughly $25.4$ standard deviations. Meanwhile, each $(0,1)$ transition in a mixed word forces a block of $A$ vertices to be full without unlocking its $B$ vertices, incurring a domain-wall penalty of $2^(-p)$ (comparable to $(2/3)^q$). The coarse bounds in @tab-margins spend most of the vertex budget overcoming the smoothing factor $(1+x)^C$ analytically; exact transfer-matrix calculations with larger window width $w$ and $d = 2$ shrink the required order by five orders of magnitude.

= Smaller counterexamples via exact transfer matrices

To construct smaller counterexamples, we allow non-uniform block sizes $q_i$ distributed as evenly as possible around $Q/m$:
$ q_i = floor((i+1)Q/m) - floor(i Q/m), quad 0 <= i < m. $
We take $G_1 = G_(9,2)(156, 2; bold(q))$ with $Q = 969$ (so $q_i in {6,7}$) and $G_2 = G_(6,2)(117, 3; bold(q))$ with $Q = 1090$ (so $q_i in {9,10}$).

#env("Lemma", title: [Exact transfer-matrix representation])[
  Let $g(x) = x(1+x)^d$. For each $0 <= i < m$, define the $(w+1) times (w+1)$ matrix $M_i$ over $ZZ[x]$, indexed by $0, 1, dots, w$, whose only possibly nonzero entries are
  $ (M_i)_(r, 0) &= ((1+x)^p - x^p) g^(q_i) && quad (0 <= r <= w), \
    (M_i)_(r, r+1) &= x^p g^(q_i) && quad (0 <= r < w - 1), \
    (M_i)_(r, w) &= x^p (g + x^d)^(q_i) && quad (r in {w-1, w}). $
  Then $H(x) = tr(M_0 M_1 dots.c M_(m-1))$.
] <lem-transfer>

#proof Call block $A_i$ *full* in a subset $X subset.eq Vvar$ if all $p$ of its vertices lie in $X$. Scanning around the ring, let the state $r in {0, 1, dots, w}$ record the number of consecutive full $A$-blocks ending at block $i-1$, capped at $w$. At step $i$, choosing a non-full block $A_i$ carries weight $(1+x)^p - x^p$ and resets the run length to $0$; choosing a full block $A_i$ carries weight $x^p$ and advances the state to $min(r+1, w)$.

If the updated run length is strictly less than $w$, then at least one $A$ vertex among blocks $i-w+1, dots, i$ is absent from $X$, so every $B_(i,b)$ in block $i$ is forced into $X$ and its $d$ private $Z$ vertices are unconstrained, contributing $g^(q_i)$. If the updated run length equals $w$, then all $w$ blocks $A_(i-w+1), dots, A_i$ are full, so each $B_(i,b)$ may also be omitted at the cost of forcing all $d$ of its private $Z$ vertices into $X$, contributing $(g + x^d)^(q_i)$.

Taking the trace sums over all cyclic state sequences whose ending state equals their starting state. If at least one block $A_i$ is non-full, the reset to state $0$ at that block uniquely determines the state at every index around the cycle. If all $m$ blocks are full, then because $m >= w$ the only consistent fixed state is $w$. Hence every valid variable subset $X$ is counted exactly once with weight $x^(|X|)$. #qed

#figure(
  table(
    columns: (1.1fr, 1fr, 1fr),
    align: (left, center, center),
    inset: (x: 8pt, y: 4pt),
    stroke: (x, y) => (bottom: if y == 0 { 0.7pt } else { 0.35pt + luma(205) }),
    table.header([*Quantity*], [*$G_1$*], [*$G_2$*]),
    [Parameters $(m,p,w,d,Q)$], [$(156, 2, 9, 2, 969)$], [$(117, 3, 6, 2, 1090)$],
    [Block sizes $q_i$], [$6, 7$], [$9, 10$],
    [Vertices $n$], [22,601], [25,423],
    [Edges], [41,980], [47,222],
    [Variable vertices $|Vvar|$], [3,219], [3,621],
    [Clause vertices], [19,380], [21,800],
    [Support $[gamma_t, n]$], [$[970, 22 thin 601]$], [$[1 thin 091, 25 thin 423]$],
    [Turning points $(k_1, k_2, k_3)$], [$(11 thin 843, 11 thin 858, 11 thin 888)$], [$(13 thin 299, 13 thin 356, 13 thin 380)$],
    [$d_t (G, k_1) slash d_t (G, k_2)$], [1.000236], [1.014411],
    [$d_t (G, k_3) slash d_t (G, k_2)$], [1.001533], [1.001448],
    [Decimal digits per coefficient], [6,510], [7,323],
  ),
  caption: [Parameters and exact valley statistics for the graphs $G_1$ and $G_2$ of Theorem B. Ratios are rounded to six decimal places.],
) <tab-small>

#figure(
  image("valley_plot.svg", width: 100%),
  caption: [Exact total domination coefficients near the valleys of $G_1$ (left) and $G_2$ (right), normalized by the valley value $d_t (G, k_2)$. Note the different vertical scales.],
) <fig-valleys>

Because the coefficients at $(k_1, k_2, k_3)$ have 6,510 and 7,323 decimal digits, we verified Theorem B through three independent exact computational pipelines:

+ *Dual exact transfer recurrences in FLINT.* Using exact integer polynomial arithmetic via `python-flint` @FLINT, we compute $H(x)$ both by the forward recurrence of @lem-transfer and by an independent backward recurrence tracking how many upcoming $A$-blocks are forced full by previously omitted $B$-vertices (multiplied via divide-and-conquer). Both recurrences match exhaustive $2^n$ subset enumeration on small test graphs and agree identically on $H(x)$ for $G_1$ and $G_2$. Expanding the full product $D_t (G,x) = x(1+x)^C H(x)$ confirms that each polynomial has support $[Q+1, n]$, has no equal adjacent nonzero coefficients, and changes monotonicity direction only at $(k_1, k_2, k_3)$.
+ *Independent modular NTT check.* A separate pure-Python implementation builds both graphs explicitly, checks simplicity, connectivity, bipartiteness, and absence of isolated vertices, validates the transfer formula against $2^n$ brute force on seven small instances, and evaluates the target coefficients via a number-theoretic transform modulo the two primes $998 thin 244 thin 353$ and $1 thin 004 thin 535 thin 809$, matching the exact certificates at every entry.
+ *Exact Chinese remainder reconstruction.* A third independent script (`independent_check.py`) re-verifies graph properties and tests the transfer formula against brute force on ten graphs of order at most $20$. For $G_1$ and $G_2$, it evaluates $H$ at the 4096th roots of unity modulo distinct 31-bit primes congruent to $1 mod 4096$ (756 primes for $G_1$ and 850 primes for $G_2$, whose products exceed $2^(n+64)$). Since $deg(H) = |Vvar| < 4096$, an inverse discrete Fourier transform recovers $H$ modulo each prime, binomial convolution extracts the three target coefficients via @eq-factor, and the Chinese remainder theorem reconstructs the exact integers, confirming all six coefficients and both strict valley inequalities.

All three counterexamples in Theorems A and B also fail to be log-concave (and hence fail to be real-rooted by Newton’s inequalities). Indeed, every superset of a total dominating set is again a total dominating set, so the nonzero coefficients of $D_t (G,x)$ form an interval of consecutive integers; any nonnegative log-concave sequence with contiguous support is necessarily unimodal.

= Formal verification in Lean 4

To eliminate any possibility of oversight in the combinatorial reduction or numerical estimates of Theorem A, we formalized the non-unimodality of $G(18000, 210, 359)$ in Lean 4 (v4.14.0) @Lean. The core development uses only Lean’s standard library with no external dependencies, and compiles cleanly both as a modular project and as a single self-contained file `AlikhaniJafari.lean`.

A finite simple graph on `Fin N` is represented by a symmetric, irreflexive Boolean adjacency function, with connectivity defined via walks, bipartiteness via a proper two-coloring, and `HasNoIsolated` requiring a neighbor for every vertex. The predicate `IsTotalDom G S` checks that every vertex has an adjacent vertex in `S`, and `totalDomCount G k` is defined directly as the count of subsets of cardinality `k` in an explicit, proven-exhaustive, duplicate-free enumeration of all $2^N$ Boolean vectors on `Fin N`. Unimodality (`IsUnimodal f`) is defined as the absence of a strict valley (`min (f i) (f k) ≤ f j` for all `i < j < k`), which is equivalent to standard unimodality for sequences of natural numbers with finite support.

The proof mirrors Section 3 across eight modules: `Basic` (list counting, bijections, binomial identities, and pure-`Nat` inequalities), `Graph` (the inductive vertex type `Vtx`, `ringGraph`, and @lem-graph), `Config` and `Bridge` (the exact factorization into hub, free vertices, and valid variable configurations, proving @lem-tds), `Families` (the lower bounds $B_1, B_3$ and Chernoff upper bounds $U_1, U_2$), `Mixed` (@lem-mixed), `Numerics` (exact integer certification of the strict valley inequalities), and `Main`, which assembles the top-level theorem:

#block(inset: (left: 0.75em))[
  #set text(size: 8.6pt)
  ```lean
  theorem alikhani_jafari_false :
      IsConnected theGraph ∧ IsBipartite theGraph ∧ HasNoIsolated theGraph ∧
        ¬ IsUnimodal (totalDomCount theGraph)
  ```
]

Rather than evaluating logarithms, the `Numerics` module certifies the valley purely in exact `Nat` arithmetic using elementary Bernoulli and geometric bounds; for arithmetic convenience with exact integer multiples of $m$, it targets the nearby valley index $k_2 = 2 thin 050 thin 722 thin 001$ (between the same outer indices $k_1$ and $k_3$ on the same graph $G(18000, 210, 359)$). Checking `#print axioms alikhani_jafari_false` confirms that the proof depends only on Lean’s three standard foundational axioms (`propext`, `Classical.choice`, and `Quot.sound`), with no `sorry` and no `native_decide` trust assumptions.

A companion interface in Mathlib v4.14.0 (`AlikhaniJafariMathlib.lean`) bridges this core theorem to standard Mathlib definitions: `SimpleGraph`, `SimpleGraph.Connected`, `SimpleGraph.Colorable 2`, finite-subset counting over `Finset`, and `Polynomial ℕ`, proving directly that there is no mode $m in NN$ for which the coefficient function is `MonotoneOn` on $(-infinity, m]$ and `AntitoneOn` on $[m, infinity)$.

= Concluding remarks and open questions

Several natural questions remain open.

*Minimum counterexample order.* What is the smallest number of vertices of a graph whose total domination polynomial is not unimodal? Theorem 2.8 of Alikhani and Jafari @AJ16 forces any valley index to exceed $n/2$, as holds in all three of our examples ($2 thin 047 thin 113 thin 001 < k_2$ in Theorem A, and $11 thin 300.5 < 11 thin 858$ and $12 thin 711.5 < 13 thin 356$ in Theorem B). It seems likely that counterexamples well below $22 thin 601$ vertices exist.

*Trees and bounded maximum degree.* Are total domination polynomials of trees always unimodal, or even log-concave? (For independence polynomials of trees, log-concavity is known to fail starting at order 26 @KL.) Our graphs have girth four (witnessed by the 4-cycle $B_(i,b), c_(i,b,0,a), A_(i,a), h$) and unbounded maximum degree because the hub $h$ is adjacent to all variable vertices. In contrast, Chalmers’s counterexamples to the Alikhani–Peng conjecture for ordinary domination have uniformly bounded maximum degree @Chalmers26. Can a family of graphs with bounded maximum degree also have non-unimodal total domination polynomials?

*Arbitrary valleys and prescribed shapes.* Can a total domination polynomial exhibit arbitrarily many strict valleys, as holds for ordinary domination polynomials @Chalmers26, or realize arbitrary relative orderings of selected coefficients in the spirit of Alavi, Malde, Schwenk, and Erdős for independence sequences @AMSE?

*Code and data availability.* The standalone Lean 4 formalization (`lean/AlikhaniJafari.lean` and modular `lean/AJ/` sources), the Mathlib v4.14.0 bridge (`mathlib/`), the exact rational, FLINT, modular NTT, and CRT verification scripts (`verification/`), and the exact coefficient certificates for $G_1$ and $G_2$ are publicly available at #link("https://github.com/xyzzyy/total-domination-unimodality")[`https://github.com/xyzzyy/total-domination-unimodality`].

*Use of AI tools.* Large language model assistants were used during this work to help explore candidate graph constructions, write verification scripts, assist with the Lean 4 formalization, and edit the exposition. All mathematical claims were checked independently via Lean 4 and exact arithmetic, and the author takes full responsibility for the contents of this paper.

#bibliography("refs.bib", style: "ieee")
