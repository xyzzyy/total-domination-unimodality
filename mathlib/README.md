# Alikhani–Jafari conjecture in Mathlib

This project proves that a connected bipartite graph with no isolated vertices
can have a non-unimodal total domination polynomial. This refutes
[Conjecture 2.9 of Alikhani and Jafari](https://arxiv.org/pdf/1605.02222#page=5).

## Build

Use Lean `v4.14.0` with Mathlib tag `v4.14.0`, commit
`4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`. From this directory, run:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib/Algebra/Polynomial/Coeff.lean \
  Mathlib/Combinatorics/SimpleGraph/Coloring.lean \
  Mathlib/Combinatorics/SimpleGraph/Path.lean \
  Mathlib/Data/Fintype/Fin.lean Mathlib/Data/Fintype/Powerset.lean
lake build
```

If macOS reports `__DATA_CONST segment missing SG_READ_ONLY flag` when it
starts the cache executable, use this command with the same file arguments.
Then run `lake build`.

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get Mathlib/Algebra/Polynomial/Coeff.lean \
  Mathlib/Combinatorics/SimpleGraph/Coloring.lean \
  Mathlib/Combinatorics/SimpleGraph/Path.lean \
  Mathlib/Data/Fintype/Fin.lean Mathlib/Data/Fintype/Powerset.lean
```

Both commands fetch prebuilt Mathlib files. The build compiles the copied
`AJ` modules and the Mathlib proof.

## Final theorem

The declarations below are in namespace `AlikhaniJafariMathlib`. The
coefficient counts size-`k` subsets that contain a neighbor of every vertex.
The polynomial sums these counts through the number of vertices.

```lean
noncomputable def totalDomCoeff {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun S : Finset V => (∀ v, ∃ u ∈ S, G.Adj v u) ∧ S.card = k).card

noncomputable def totalDomPoly {V : Type*} [Fintype V] (G : SimpleGraph V) : Polynomial ℕ :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), Polynomial.C (totalDomCoeff G k) * Polynomial.X ^ k

theorem alikhani_jafari_conjecture_false :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.Colorable 2 ∧ (∀ v, ∃ u, G.Adj v u) ∧
        ¬ ∃ m : ℕ, MonotoneOn (totalDomPoly G).coeff (Set.Iic m) ∧
          AntitoneOn (totalDomPoly G).coeff (Set.Ici m)
```

The graph has 4,094,226,002 vertices. Its coefficient at index 2,050,722,001
is smaller than the coefficients at indices 2,050,344,001 and 2,051,157,001.
The proof transfers these inequalities through a bijection between finite
subsets and their Boolean membership functions. It keeps the counts symbolic.

The build prints the axiom dependencies of the final theorem.

```text
'AlikhaniJafariMathlib.alikhani_jafari_conjecture_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
