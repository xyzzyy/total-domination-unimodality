import AJ.Bridge
import AJ.Families
import AJ.Mixed
import AJ.Numerics

/-!
# Main theorem: a connected bipartite graph whose total domination polynomial is not unimodal

`theGraph = ringGraph 18000 210 359` has `numV 18000 210 359 = 4,094,226,002` vertices.
Its total domination sequence has a strict valley:
  `d_t(k₂) < d_t(k₁)` and `d_t(k₂) < d_t(k₃)` with `k₁ < k₂ < k₃`.

OWNER: coordinator.
-/

namespace AlikhaniJafariDisproof
open Params

theorem hm0 : 0 < m := by decide
theorem hp0 : 0 < p := by decide
theorem hq0 : 0 < q := by decide
theorem hm3 : 3 ≤ m := by decide

/-- The explicit counterexample graph. -/
def theGraph : SimpleGraph (numV m p q) := ringGraph m p q hm0 hp0 hq0

theorem theGraph_numV : numV m p q = 4094226002 := by decide

theorem hC : numFree m p q = C := rfl
theorem hP : m * p = P := rfl
theorem hQ : m * q = Q := rfl
theorem hN1 : C + P + Q = N1 := rfl

theorem peak1 : choose N1 (N1 / 2) ≤ totalDomCount theGraph k1 := by
  have h := lb_peak1 m p q hm0
  rw [hC, hP, hQ, hN1] at h
  unfold theGraph
  rw [totalDomCount_eq]
  exact h

theorem peak3 :
    choose C (C / 2) * (choose Q (Q / 3) * 2 ^ (Q - Q / 3)) ≤ totalDomCount theGraph k3 := by
  have h := lb_peak3 m p q hm0
  rw [hC, hP, hQ] at h
  unfold theGraph
  rw [totalDomCount_eq]
  exact h

theorem valley_upper :
    totalDomCount theGraph k2 ≤
      choose N1 (k2 - 1 - Q) + fam2Count m p q hm0 (k2 - 1 - P) + 2 ^ C * mixedCount m p q hm0 := by
  have hk : 1 + m * p + m * q ≤ k2 := k_order.2.2
  have h := ub_valley m p q hm0 k2 hk
  rw [hC, hP, hQ, hN1] at h
  unfold theGraph
  rw [totalDomCount_eq]
  exact h

theorem hs2 : k2 - 1 - P ≤ C + 2 * Q := by decide

theorem fam2_at_k2 :
    fam2Count m p q hm0 (k2 - 1 - P) * (α ^ (k2 - 1 - P) * β ^ (C + 2 * Q - (k2 - 1 - P))) ≤
      (α + β) ^ C * (α * (α + 2 * β)) ^ Q := by
  have h := fam2_chernoff m p q hm0 (k2 - 1 - P) α β (by rw [hC, hQ]; exact hs2)
  rw [hC, hQ] at h
  exact h

theorem mixed_at :
    mixedCount m p q hm0 * L ^ (m - 1) ≤ m * 2 ^ q * L * Λ ^ (m - 1) :=
  mixed_bound m p q hm0 hm3 L Λ (by decide) mix_h0 mix_h1

/-- The strict valley. -/
theorem valley :
    totalDomCount theGraph k2 < totalDomCount theGraph k1 ∧
    totalDomCount theGraph k2 < totalDomCount theGraph k3 := by
  have hv := numeric_valley _ _ fam2_at_k2 mixed_at
  have hu := valley_upper
  exact ⟨Nat.lt_of_le_of_lt hu (Nat.lt_of_lt_of_le hv.1 peak1),
         Nat.lt_of_le_of_lt hu (Nat.lt_of_lt_of_le hv.2 peak3)⟩

theorem not_unimodal : ¬ IsUnimodal (totalDomCount theGraph) := by
  intro h
  have h' := h k1 k2 k3 k_order.1 k_order.2.1
  have hv := valley
  have : min (totalDomCount theGraph k1) (totalDomCount theGraph k3) ≤ totalDomCount theGraph k2 := h'
  rcases Nat.le_total (totalDomCount theGraph k1) (totalDomCount theGraph k3) with hle | hle
  · rw [Nat.min_eq_left hle] at this; omega
  · rw [Nat.min_eq_right hle] at this; omega

/-- **Main theorem.** The Alikhani–Jafari conjecture (2016, Conj. 2.9) is false:
    `theGraph` is a finite simple connected bipartite graph with no isolated vertices
    whose total domination polynomial is not unimodal. -/
theorem alikhani_jafari_false :
    IsConnected theGraph ∧ IsBipartite theGraph ∧ HasNoIsolated theGraph ∧
      ¬ IsUnimodal (totalDomCount theGraph) :=
  ⟨ringGraph_connected m p q hm0 hp0 hq0, ringGraph_bipartite m p q hm0 hp0 hq0,
   ringGraph_noIsolated m p q hm0 hp0 hq0, not_unimodal⟩

end AlikhaniJafariDisproof
