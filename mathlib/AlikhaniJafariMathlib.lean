import AJ
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset

open scoped BigOperators

namespace AlikhaniJafariMathlib

/-- The number of size-`k` subsets that contain a neighbor of every vertex. -/
noncomputable def totalDomCoeff {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun S : Finset V => (∀ v, ∃ u ∈ S, G.Adj v u) ∧ S.card = k).card

/-- The total domination polynomial of a finite simple graph. -/
noncomputable def totalDomPoly {V : Type*} [Fintype V] (G : SimpleGraph V) : Polynomial ℕ :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), Polynomial.C (totalDomCoeff G k) * Polynomial.X ^ k

theorem coeff_totalDomPoly {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (totalDomPoly G).coeff k = totalDomCoeff G k := by
  classical
  simp only [totalDomPoly, Polynomial.finset_sum_coeff, Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hk
  · rfl
  · symm
    unfold totalDomCoeff
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro S hS
    have hcard := (Finset.mem_filter.mp hS).2.2
    exact hk (Nat.lt_succ_of_le (hcard ▸ S.card_le_univ))

/-- The Mathlib graph with the same adjacency relation as the core graph. -/
def ofCore {n : ℕ} (G : AlikhaniJafariDisproof.SimpleGraph n) : SimpleGraph (Fin n) where
  Adj u v := G.adj u v = true
  symm := fun {u v} h => (G.symm u v).symm.trans h
  loopless := fun v h => Bool.noConfusion ((G.loopless v).symm.trans h)

theorem ofCore_adj {n : ℕ} (G : AlikhaniJafariDisproof.SimpleGraph n) (u v : Fin n) :
    (ofCore G).Adj u v ↔ G.adj u v = true := Iff.rfl

instance {n : ℕ} (G : AlikhaniJafariDisproof.SimpleGraph n) : DecidableRel (ofCore G).Adj :=
  fun u v => inferInstanceAs (Decidable (G.adj u v = true))

private theorem reachable_ofCore {n : ℕ} {G : AlikhaniJafariDisproof.SimpleGraph n} {u v : Fin n}
    (h : AlikhaniJafariDisproof.Reachable G u v) : (ofCore G).Reachable u v := by
  induction h with
  | refl _ => exact ⟨.nil⟩
  | step hedge _ ih =>
    obtain ⟨walk⟩ := ih
    exact ⟨.cons hedge walk⟩

theorem connected_ofCore {n : ℕ} {G : AlikhaniJafariDisproof.SimpleGraph n} [Nonempty (Fin n)]
    (h : AlikhaniJafariDisproof.IsConnected G) : (ofCore G).Connected :=
  ⟨fun u v => reachable_ofCore (h u v)⟩

theorem colorable_ofCore {n : ℕ} {G : AlikhaniJafariDisproof.SimpleGraph n}
    (h : AlikhaniJafariDisproof.IsBipartite G) : (ofCore G).Colorable 2 := by
  obtain ⟨color, hcolor⟩ := h
  let coloring : (ofCore G).Coloring Bool :=
    SimpleGraph.Coloring.mk color fun {u v} h => hcolor u v h
  simpa only [Fintype.card_bool] using coloring.colorable

private def finsetBoolEquiv (n : ℕ) : Finset (Fin n) ≃ (Fin n → Bool) where
  toFun S v := decide (v ∈ S)
  invFun f := Finset.univ.filter fun v => f v = true
  left_inv S := by ext v; simp
  right_inv f := by funext v; cases h : f v <;> simp [h]

theorem countTrue_eq_card {n : ℕ} (f : Fin n → Bool) :
    AlikhaniJafariDisproof.countTrue f = (Finset.univ.filter fun v => f v = true).card := by
  induction n with
  | zero => simp [AlikhaniJafariDisproof.countTrue]
  | succ n ih =>
    rw [Fin.card_filter_univ_succ']
    change (if f 0 = true then 1 else 0) +
      AlikhaniJafariDisproof.countTrue (AlikhaniJafariDisproof.finTail f) = _
    rw [ih]
    rfl

theorem totalDomCoeff_ofCore {n : ℕ} (G : AlikhaniJafariDisproof.SimpleGraph n) (k : ℕ) :
    totalDomCoeff (ofCore G) k = AlikhaniJafariDisproof.totalDomCount G k := by
  classical
  let p : (Fin n → Bool) → Bool := fun f =>
    AlikhaniJafariDisproof.isTotalDomBool G f && (AlikhaniJafariDisproof.countTrue f == k)
  have allVecs : (AlikhaniJafariDisproof.allBoolVecs n).toFinset = Finset.univ := by
    ext f
    simp [AlikhaniJafariDisproof.mem_allBoolVecs]
  have nodup : ((AlikhaniJafariDisproof.allBoolVecs n).filter p).Nodup :=
    (AlikhaniJafariDisproof.allBoolVecs_nodup n).sublist (List.filter_sublist _)
  change totalDomCoeff (ofCore G) k = (AlikhaniJafariDisproof.allBoolVecs n).countP p
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup nodup,
    List.toFinset_filter, allVecs]
  unfold totalDomCoeff
  apply Finset.card_equiv (finsetBoolEquiv n)
  intro S
  have hcard : AlikhaniJafariDisproof.countTrue (finsetBoolEquiv n S) = S.card :=
    (countTrue_eq_card _).trans (congrArg Finset.card ((finsetBoolEquiv n).left_inv S))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, Bool.and_eq_true,
    AlikhaniJafariDisproof.isTotalDomBool_eq_true, beq_iff_eq, hcard,
    AlikhaniJafariDisproof.IsTotalDom]
  simp only [finsetBoolEquiv, Equiv.coe_fn_mk, decide_eq_true_eq, ofCore_adj, and_comm]

/-- The counterexample has 4,094,226,002 vertices. -/
def counterexample : SimpleGraph (Fin 4094226002) := ofCore AlikhaniJafariDisproof.theGraph

instance : DecidableRel counterexample.Adj :=
  inferInstanceAs (DecidableRel (ofCore AlikhaniJafariDisproof.theGraph).Adj)

/-- The middle coefficient is strictly smaller than both outer coefficients. -/
theorem counterexample_valley :
    2050344001 < (2050722001 : ℕ) ∧ 2050722001 < (2051157001 : ℕ) ∧
    (totalDomPoly counterexample).coeff 2050722001 <
      (totalDomPoly counterexample).coeff 2050344001 ∧
    (totalDomPoly counterexample).coeff 2050722001 <
      (totalDomPoly counterexample).coeff 2051157001 := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [coeff_totalDomPoly]
  change totalDomCoeff (ofCore AlikhaniJafariDisproof.theGraph) AlikhaniJafariDisproof.Params.k2 <
      totalDomCoeff (ofCore AlikhaniJafariDisproof.theGraph) AlikhaniJafariDisproof.Params.k1 ∧
    totalDomCoeff (ofCore AlikhaniJafariDisproof.theGraph) AlikhaniJafariDisproof.Params.k2 <
      totalDomCoeff (ofCore AlikhaniJafariDisproof.theGraph) AlikhaniJafariDisproof.Params.k3
  simpa only [totalDomCoeff_ofCore] using AlikhaniJafariDisproof.valley

private theorem not_unimodal_of_valley {f : ℕ → ℕ} {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hji : f j < f i) (hjk' : f j < f k) :
    ¬ ∃ m : ℕ, MonotoneOn f (Set.Iic m) ∧ AntitoneOn f (Set.Ici m) := by
  rintro ⟨m, hmono, hanti⟩
  rcases le_total j m with hjm | hmj
  · exact (not_le_of_gt hji) (hmono (hij.le.trans hjm) hjm hij.le)
  · exact (not_le_of_gt hjk') (hanti hmj (hmj.trans hjk.le) hjk.le)

/-- A finite connected bipartite graph with no isolated vertices refutes the conjecture. -/
theorem alikhani_jafari_conjecture_false :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      G.Connected ∧ G.Colorable 2 ∧ (∀ v, ∃ u, G.Adj v u) ∧
        ¬ ∃ m : ℕ, MonotoneOn (totalDomPoly G).coeff (Set.Iic m) ∧
          AntitoneOn (totalDomPoly G).coeff (Set.Ici m) := by
  obtain ⟨hconnected, hbipartite, hnoIsolated, _⟩ :=
    AlikhaniJafariDisproof.alikhani_jafari_false
  obtain ⟨hij, hjk, hji, hjk'⟩ := counterexample_valley
  refine ⟨Fin 4094226002, inferInstance, counterexample, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact connected_ofCore hconnected
  · exact colorable_ofCore hbipartite
  · exact hnoIsolated
  · exact not_unimodal_of_valley hij hjk hji hjk'

#print axioms alikhani_jafari_conjecture_false

end AlikhaniJafariMathlib
