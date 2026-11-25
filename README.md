# Counterexamples to the Unimodality of Total Domination Polynomials

[![Preprint DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24519568.svg)](https://doi.org/10.5281/zenodo.24519568)

Accompanying formalization, exact verification scripts, and coefficient certificates for:

> Andrew MacKenzie, *Counterexamples to the Unimodality of Total Domination Polynomials* (2026). Preprint DOI: [10.5281/zenodo.24519568](https://doi.org/10.5281/zenodo.24519568).

This repository disproves Conjecture 2.9 of Alikhani and Jafari (arXiv:1605.02222; *J. Discrete Math. Sci. Cryptogr.* 23(4), 2020) by constructing connected bipartite graphs whose total domination polynomials are not unimodal.

## Contents

- `paper/` — Typst source (`main.typ`), bibliography (`refs.bib`), compiled PDF (`main.pdf`), and SVG figures (`construction.svg`, `valley_plot.svg`).
- `lean/` — Zero-dependency Lean 4 (v4.14.0) formalization of Theorem A on $G(18000, 210, 359)$ (4,094,226,002 vertices), provided both as a modular Lake project (`AJ/`) and as a single self-contained file (`AlikhaniJafari.lean`). Uses only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry` and no `native_decide`.
- `mathlib/` — Companion Mathlib v4.14.0 interface (`AlikhaniJafariMathlib.lean`) bridging the core theorem to `SimpleGraph`, `SimpleGraph.Connected`, `SimpleGraph.Colorable 2`, `Finset`, and `Polynomial ℕ`.
- `verification/` — Exact rational certification and independent computational checks:
  - `verify_rational.py` — Exact `fractions.Fraction` certification of the $2^{-68}$ valley margin in Theorem A (Table 1).
  - `verify_margins.py` — 60-digit decimal check of the Theorem A bounds (`verify_margins.out`).
  - `graph_exact.py` — Dual exact transfer-matrix recurrences in `python-flint` for $G_1$ ($n = 22{,}601$) and $G_2$ ($n = 25{,}423$).
  - `audit_ntt.py` — Pure-Python graph audit, $2^n$ brute-force check on 7 small instances, and exact modular NTT verification modulo $998{,}244{,}353$ and $1{,}004{,}535{,}809$.
  - `independent_check.py` — Exact Chinese remainder theorem reconstruction of the 6,510- and 7,323-digit target coefficients using 756 and 850 distinct 31-bit primes.
  - `cert_22601.json`, `cert_25423.json` — Exact integer coefficient certificates for $G_1$ and $G_2$.
  - `plot_valley.py` — Reproduces `valley_plot.svg` directly from exact FLINT polynomials.

## Quick Reproduction

### 1. Lean 4 formalization (zero external dependencies)

Requires Lean `v4.14.0` (e.g., via `elan`).

```sh
# Single-file check:
lean lean/AlikhaniJafari.lean

# Modular Lake project:
cd lean && lake build
```

For the Mathlib v4.14.0 bridge, see `mathlib/README.md`.

### 2. Analytic proof certification (Theorem A)

Requires Python 3.11+ (standard library only):

```sh
cd verification
python3 verify_rational.py
python3 verify_margins.py
```

### 3. Smaller counterexamples (Theorem B)

Pure-Python checks (Python 3.11+, standard library + NumPy for `independent_check.py`):

```sh
cd verification
python3 audit_ntt.py
python3 independent_check.py cert_22601.json cert_25423.json
```

Full polynomial computation via dual recurrences (requires `python-flint`):

```sh
cd verification
python3 graph_exact.py 156 2 9 2 969 11843 11858 11888 cert_22601.json
python3 graph_exact.py 117 3 6 2 1090 13299 13356 13380 cert_25423.json
```

### 4. Compile the paper

Requires Typst 0.15+:

```sh
cd paper
typst compile main.typ main.pdf
```
