import AJ.Basic

namespace AlikhaniJafariDisproof

section RingClauseGraph

/-- Number of free vertices (`leaf` + `clauseZ` + `clauseA`) for `w = 3, d = 1`. -/
def numFree (m p q : Nat) : Nat := 1 + m * q + m * q * 3 * p

/-- Total number of vertices: `1 (hub) + C (free) + mp (A) + Q (B) + Q (Z)`. -/
def numV (m p q : Nat) : Nat := 1 + (numFree m p q + (m * p + (m * q + m * q)))

/-- Structured vertex type of the ring-clause bipartite graph `G(m, p, q)` (`w = 3, d = 1`). -/
inductive Vtx (m p q : Nat) where
  | hub
  | leaf
  | clauseZ (i : Fin m) (b : Fin q)
  | clauseA (i : Fin m) (b : Fin q) (s : Fin 3) (a : Fin p)
  | varA (i : Fin m) (a : Fin p)
  | varB (i : Fin m) (b : Fin q)
  | varZ (i : Fin m) (b : Fin q)
  deriving DecidableEq

/-- Cyclic backward shift `(i - s) mod m`. -/
def shiftBack (m : Nat) (hm : 0 < m) (i : Fin m) (s : Fin 3) : Fin m :=
  ⟨(i.val + m - s.val % m) % m, Nat.mod_lt _ hm⟩

/-- Flat index inside the `numFree m p q` block (`leaf`, `clauseZ`, `clauseA`). -/
def encClauseZ {m p q : Nat} (i : Fin m) (b : Fin q) : Fin (numFree m p q) :=
  ⟨1 + (i.val * q + b.val), by
    unfold numFree
    have h1 : i.val * q + b.val < m * q := by
      have : i.val + 1 ≤ m := i.isLt
      have hmul : (i.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q this
      rw [Nat.succ_mul] at hmul; omega
    omega⟩

def encClauseA {m p q : Nat} (i : Fin m) (b : Fin q) (s : Fin 3) (a : Fin p) : Fin (numFree m p q) :=
  ⟨1 + m * q + (((i.val * q + b.val) * 3 + s.val) * p + a.val), by
    unfold numFree
    have h1 : i.val * q + b.val < m * q := by
      have hmul : (i.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q i.isLt
      rw [Nat.succ_mul] at hmul; omega
    have h2 : (i.val * q + b.val) * 3 + s.val < m * q * 3 := by
      have hmul : (i.val * q + b.val + 1) * 3 ≤ m * q * 3 := Nat.mul_le_mul_right 3 h1
      rw [Nat.succ_mul] at hmul; omega
    have h3 : ((i.val * q + b.val) * 3 + s.val) * p + a.val < m * q * 3 * p := by
      have hmul : ((i.val * q + b.val) * 3 + s.val + 1) * p ≤ m * q * 3 * p := Nat.mul_le_mul_right p h2
      rw [Nat.succ_mul] at hmul; omega
    omega⟩

/-- Flat index of `varA i a` in `Fin (m * p)`. -/
def encVarA {m p : Nat} (i : Fin m) (a : Fin p) : Fin (m * p) :=
  ⟨i.val * p + a.val, by
    have hmul : (i.val + 1) * p ≤ m * p := Nat.mul_le_mul_right p i.isLt
    rw [Nat.succ_mul] at hmul; omega⟩

/-- Flat index of `(i, b)` in `Fin (m * q)`. -/
def encVarBQ {m q : Nat} (i : Fin m) (b : Fin q) : Fin (m * q) :=
  ⟨i.val * q + b.val, by
    have hmul : (i.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q i.isLt
    rw [Nat.succ_mul] at hmul; omega⟩

/-- Encode `Vtx m p q` into `Fin (numV m p q)` respecting the exact `1 + (C + (mp + (Q + Q)))` layout. -/
def encVtx {m p q : Nat} : Vtx m p q → Fin (numV m p q)
  | .hub => ⟨0, by unfold numV; omega⟩
  | .leaf => ⟨1, by unfold numV numFree; omega⟩
  | .clauseZ i b => ⟨1 + (encClauseZ (p := p) i b).val, by
      unfold numV; have := (encClauseZ (p := p) i b).isLt; omega⟩
  | .clauseA i b s a => ⟨1 + (encClauseA i b s a).val, by
      unfold numV; have := (encClauseA i b s a).isLt; omega⟩
  | .varA i a => ⟨1 + numFree m p q + (encVarA i a).val, by
      unfold numV; have := (encVarA i a).isLt; omega⟩
  | .varB i b => ⟨1 + numFree m p q + m * p + (encVarBQ i b).val, by
      unfold numV; have := (encVarBQ i b).isLt; omega⟩
  | .varZ i b => ⟨1 + numFree m p q + m * p + m * q + (encVarBQ i b).val, by
      unfold numV; have := (encVarBQ i b).isLt; omega⟩

/-- Decode `Fin (numV m p q)` back into `Vtx m p q` (requires `p ≥ 1, q ≥ 1`). -/
def decVtx {m p q : Nat} (hp : 0 < p) (hq : 0 < q) (v : Fin (numV m p q)) : Vtx m p q :=
  if h0 : v.val = 0 then .hub
  else if h1 : v.val = 1 then .leaf
  else if h2 : v.val < 1 + (1 + m * q) then
    let idx := v.val - 2
    .clauseZ ⟨idx / q, (Nat.div_lt_iff_lt_mul hq).mpr (by omega)⟩
      ⟨idx % q, Nat.mod_lt _ hq⟩
  else if h3 : v.val < 1 + numFree m p q then
    let idx := v.val - (1 + (1 + m * q))
    have hidx : idx < m * q * 3 * p := by unfold numFree at h3; omega
    have ht1 : idx / p < m * q * 3 := (Nat.div_lt_iff_lt_mul hp).mpr hidx
    have ht2 : idx / p / 3 < m * q := (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr ht1
    have hi : idx / p / 3 / q < m := (Nat.div_lt_iff_lt_mul hq).mpr ht2
    .clauseA ⟨idx / p / 3 / q, hi⟩ ⟨idx / p / 3 % q, Nat.mod_lt _ hq⟩
      ⟨idx / p % 3, Nat.mod_lt _ (by omega)⟩ ⟨idx % p, Nat.mod_lt _ hp⟩
  else if h4 : v.val < 1 + numFree m p q + m * p then
    let idx := v.val - (1 + numFree m p q)
    .varA ⟨idx / p, (Nat.div_lt_iff_lt_mul hp).mpr (by omega)⟩ ⟨idx % p, Nat.mod_lt _ hp⟩
  else if h5 : v.val < 1 + numFree m p q + m * p + m * q then
    let idx := v.val - (1 + numFree m p q + m * p)
    .varB ⟨idx / q, (Nat.div_lt_iff_lt_mul hq).mpr (by omega)⟩ ⟨idx % q, Nat.mod_lt _ hq⟩
  else
    let idx := v.val - (1 + numFree m p q + m * p + m * q)
    have hidx : idx < m * q := by have := v.isLt; unfold numV at this; omega
    .varZ ⟨idx / q, (Nat.div_lt_iff_lt_mul hq).mpr hidx⟩ ⟨idx % q, Nat.mod_lt _ hq⟩

theorem div_mod_unique {x d r : Nat} (hr : r < d) :
    (x * d + r) / d = x ∧ (x * d + r) % d = r := by
  have hd : 0 < d := by omega
  constructor
  · rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem decVtx_encVtx {m p q : Nat} (hp : 0 < p) (hq : 0 < q) (u : Vtx m p q) :
    decVtx hp hq (encVtx u) = u := by
  cases u with
  | hub => simp [decVtx, encVtx]
  | leaf => simp [decVtx, encVtx]
  | clauseZ i b =>
    have hlt : i.val * q + b.val < m * q := by
      have hmul : (i.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q i.isLt
      rw [Nat.succ_mul] at hmul; omega
    have hdm := div_mod_unique b.isLt (x := i.val)
    simp only [decVtx, encVtx, encClauseZ]
    split <;> try omega
    split <;> try omega
    split
    · have heq : 1 + (1 + (i.val * q + b.val)) - 2 = i.val * q + b.val := by omega
      simp [heq, hdm.1, hdm.2]
    · omega
  | clauseA i b s a =>
    have h1 : i.val * q + b.val < m * q := by
      have hmul : (i.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q i.isLt
      rw [Nat.succ_mul] at hmul; omega
    have h2 : (i.val * q + b.val) * 3 + s.val < m * q * 3 := by
      have hmul : (i.val * q + b.val + 1) * 3 ≤ m * q * 3 := Nat.mul_le_mul_right 3 h1
      rw [Nat.succ_mul] at hmul; omega
    have h3 : ((i.val * q + b.val) * 3 + s.val) * p + a.val < m * q * 3 * p := by
      have hmul : ((i.val * q + b.val) * 3 + s.val + 1) * p ≤ m * q * 3 * p := Nat.mul_le_mul_right p h2
      rw [Nat.succ_mul] at hmul; omega
    have hd1 := div_mod_unique a.isLt (x := (i.val * q + b.val) * 3 + s.val)
    have hd2 := div_mod_unique s.isLt (x := i.val * q + b.val)
    have hd3 := div_mod_unique b.isLt (x := i.val)
    simp only [decVtx, encVtx, encClauseA]
    have hC : numFree m p q = 1 + m * q + m * q * 3 * p := rfl
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split
    · have heq : 1 + (1 + m * q + (((i.val * q + b.val) * 3 + s.val) * p + a.val)) - (1 + (1 + m * q)) =
          ((i.val * q + b.val) * 3 + s.val) * p + a.val := by omega
      simp [heq, hd1.1, hd1.2, hd2.1, hd2.2, hd3.1, hd3.2]
    · omega
  | varA i a =>
    have hlt : i.val * p + a.val < m * p := by
      have hmul : (i.val + 1) * p ≤ m * p := Nat.mul_le_mul_right p i.isLt
      rw [Nat.succ_mul] at hmul; omega
    have hdm := div_mod_unique a.isLt (x := i.val)
    simp only [decVtx, encVtx, encVarA]
    have hC : 1 + m * q ≤ numFree m p q := by unfold numFree; omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split
    · have heq : 1 + numFree m p q + (i.val * p + a.val) - (1 + numFree m p q) = i.val * p + a.val := by omega
      simp [heq, hdm.1, hdm.2]
    · omega
  | varB i b =>
    have hlt : i.val * q + b.val < m * q := by
      have hmul : (i.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q i.isLt
      rw [Nat.succ_mul] at hmul; omega
    have hdm := div_mod_unique b.isLt (x := i.val)
    simp only [decVtx, encVtx, encVarBQ]
    have hC : 1 + m * q ≤ numFree m p q := by unfold numFree; omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split
    · have heq : 1 + numFree m p q + m * p + (i.val * q + b.val) - (1 + numFree m p q + m * p) =
          i.val * q + b.val := by omega
      simp [heq, hdm.1, hdm.2]
    · omega
  | varZ i b =>
    have hlt : i.val * q + b.val < m * q := by
      have hmul : (i.val + 1) * q ≤ m * q := Nat.mul_le_mul_right q i.isLt
      rw [Nat.succ_mul] at hmul; omega
    have hdm := div_mod_unique b.isLt (x := i.val)
    simp only [decVtx, encVtx, encVarBQ]
    have hC : 1 + m * q ≤ numFree m p q := by unfold numFree; omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    · have heq : 1 + numFree m p q + m * p + m * q + (i.val * q + b.val) -
          (1 + numFree m p q + m * p + m * q) = i.val * q + b.val := by omega
      simp [heq, hdm.1, hdm.2]

theorem encVtx_decVtx {m p q : Nat} (hp : 0 < p) (hq : 0 < q) (v : Fin (numV m p q)) :
    encVtx (decVtx hp hq v) = v := by
  apply Fin.ext
  unfold decVtx
  by_cases h0 : v.val = 0
  · simp [h0, encVtx]
  · simp only [h0, ↓reduceDIte]
    by_cases h1 : v.val = 1
    · simp [h1, encVtx]
    · simp only [h1, ↓reduceDIte]
      by_cases h2 : v.val < 1 + (1 + m * q)
      · simp only [h2, ↓reduceDIte, encVtx, encClauseZ]
        have hdm := Nat.div_add_mod (v.val - 2) q
        rw [Nat.mul_comm] at hdm; omega
      · simp only [h2, ↓reduceDIte]
        by_cases h3 : v.val < 1 + numFree m p q
        · simp only [h3, ↓reduceDIte, encVtx, encClauseA]
          have h1' := Nat.div_add_mod (v.val - (1 + (1 + m * q))) p
          have h2' := Nat.div_add_mod ((v.val - (1 + (1 + m * q))) / p) 3
          have h3' := Nat.div_add_mod ((v.val - (1 + (1 + m * q))) / p / 3) q
          rw [Nat.mul_comm] at h1' h2' h3'
          have heq : (((v.val - (1 + (1 + m * q))) / p / 3 / q * q +
                (v.val - (1 + (1 + m * q))) / p / 3 % q) * 3 +
              (v.val - (1 + (1 + m * q))) / p % 3) * p +
              (v.val - (1 + (1 + m * q))) % p = v.val - (1 + (1 + m * q)) := by
            rw [h3', h2', h1']
          rw [heq]
          omega
        · simp only [h3, ↓reduceDIte]
          by_cases h4 : v.val < 1 + numFree m p q + m * p
          · simp only [h4, ↓reduceDIte, encVtx, encVarA]
            have hdm := Nat.div_add_mod (v.val - (1 + numFree m p q)) p
            rw [Nat.mul_comm] at hdm; omega
          · simp only [h4, ↓reduceDIte]
            by_cases h5 : v.val < 1 + numFree m p q + m * p + m * q
            · simp only [h5, ↓reduceDIte, encVtx, encVarBQ]
              have hdm := Nat.div_add_mod (v.val - (1 + numFree m p q + m * p)) q
              rw [Nat.mul_comm] at hdm; omega
            · simp only [h5, ↓reduceDIte, encVtx, encVarBQ]
              have hdm := Nat.div_add_mod (v.val - (1 + numFree m p q + m * p + m * q)) q
              rw [Nat.mul_comm] at hdm; omega

/-- Symmetric, irreflexive, bipartite adjacency on `Vtx m p q` (`w = 3, d = 1`). -/
def vtxAdj {m p q : Nat} (hm : 0 < m) : Vtx m p q → Vtx m p q → Bool
  | .hub, .leaf => true
  | .leaf, .hub => true
  | .hub, .varA _ _ => true
  | .varA _ _, .hub => true
  | .hub, .varB _ _ => true
  | .varB _ _, .hub => true
  | .hub, .varZ _ _ => true
  | .varZ _ _, .hub => true
  | .clauseZ i b, .varB i' b' => (i == i') && (b == b')
  | .varB i' b', .clauseZ i b => (i == i') && (b == b')
  | .clauseZ i b, .varZ i' b' => (i == i') && (b == b')
  | .varZ i' b', .clauseZ i b => (i == i') && (b == b')
  | .clauseA i b _ _, .varB i' b' => (i == i') && (b == b')
  | .varB i' b', .clauseA i b _ _ => (i == i') && (b == b')
  | .clauseA i _ s a, .varA i' a' => (shiftBack m hm i s == i') && (a == a')
  | .varA i' a', .clauseA i _ s a => (shiftBack m hm i s == i') && (a == a')
  | _, _ => false

theorem vtxAdj_symm {m p q : Nat} (hm : 0 < m) (u v : Vtx m p q) :
    vtxAdj hm u v = vtxAdj hm v u := by
  cases u <;> cases v <;> rfl

theorem vtxAdj_loopless {m p q : Nat} (hm : 0 < m) (u : Vtx m p q) :
    vtxAdj hm u u = false := by
  cases u <;> rfl

/-- Proper 2-coloring of `Vtx m p q`: Part 0 = `{hub} ∪ clauses`, Part 1 = `{leaf} ∪ variables`. -/
def vtxColor {m p q : Nat} : Vtx m p q → Bool
  | .hub => true
  | .clauseZ _ _ => true
  | .clauseA _ _ _ _ => true
  | .leaf => false
  | .varA _ _ => false
  | .varB _ _ => false
  | .varZ _ _ => false

theorem vtxAdj_bipartite {m p q : Nat} (hm : 0 < m) (u v : Vtx m p q)
    (h : vtxAdj hm u v = true) : vtxColor u ≠ vtxColor v := by
  cases u <;> cases v <;> simp [vtxAdj, vtxColor] at h ⊢

/-- The explicit finite simple graph `G(m, p, q)` on `Fin (numV m p q)`. -/
def ringGraph (m p q : Nat) (hm : 0 < m) (hp : 0 < p) (hq : 0 < q) : SimpleGraph (numV m p q) where
  adj u v := vtxAdj hm (decVtx hp hq u) (decVtx hp hq v)
  symm _ _ := vtxAdj_symm hm _ _
  loopless _ := vtxAdj_loopless hm _

theorem ringGraph_adj_enc {m p q : Nat} (hm : 0 < m) (hp : 0 < p) (hq : 0 < q)
    (u v : Vtx m p q) :
    (ringGraph m p q hm hp hq).adj (encVtx u) (encVtx v) = vtxAdj hm u v := by
  simp [ringGraph, decVtx_encVtx]

theorem ringGraph_bipartite (m p q : Nat) (hm : 0 < m) (hp : 0 < p) (hq : 0 < q) :
    IsBipartite (ringGraph m p q hm hp hq) := by
  refine ⟨fun u => vtxColor (decVtx hp hq u), fun u v huv => ?_⟩
  exact vtxAdj_bipartite hm _ _ huv

theorem ringGraph_connected (m p q : Nat) (hm : 0 < m) (hp : 0 < p) (hq : 0 < q) :
    IsConnected (ringGraph m p q hm hp hq) := by
  have toHub : ∀ v : Fin (numV m p q), Reachable (ringGraph m p q hm hp hq) v (encVtx .hub) := by
    intro v
    rw [← encVtx_decVtx hp hq v]
    cases decVtx hp hq v with
    | hub => exact .refl _
    | leaf => exact .step (by rw [ringGraph_adj_enc]; rfl) (.refl _)
    | varA i a => exact .step (by rw [ringGraph_adj_enc]; rfl) (.refl _)
    | varB i b => exact .step (by rw [ringGraph_adj_enc]; rfl) (.refl _)
    | varZ i b => exact .step (by rw [ringGraph_adj_enc]; rfl) (.refl _)
    | clauseZ i b =>
      exact .step (v := encVtx (.varB i b))
        (by rw [ringGraph_adj_enc]; simp [vtxAdj])
        (.step (by rw [ringGraph_adj_enc]; rfl) (.refl _))
    | clauseA i b s a =>
      exact .step (v := encVtx (.varB i b))
        (by rw [ringGraph_adj_enc]; simp [vtxAdj])
        (.step (by rw [ringGraph_adj_enc]; rfl) (.refl _))
  intro u v
  exact (toHub u).trans (toHub v).symm

theorem ringGraph_noIsolated (m p q : Nat) (hm : 0 < m) (hp : 0 < p) (hq : 0 < q) :
    HasNoIsolated (ringGraph m p q hm hp hq) := by
  intro v
  rw [← encVtx_decVtx hp hq v]
  cases decVtx hp hq v with
  | hub => exact ⟨encVtx .leaf, by rw [ringGraph_adj_enc]; rfl⟩
  | leaf => exact ⟨encVtx .hub, by rw [ringGraph_adj_enc]; rfl⟩
  | varA i a => exact ⟨encVtx .hub, by rw [ringGraph_adj_enc]; rfl⟩
  | varB i b => exact ⟨encVtx .hub, by rw [ringGraph_adj_enc]; rfl⟩
  | varZ i b => exact ⟨encVtx .hub, by rw [ringGraph_adj_enc]; rfl⟩
  | clauseZ i b => exact ⟨encVtx (.varB i b), by rw [ringGraph_adj_enc]; simp [vtxAdj]⟩
  | clauseA i b s a => exact ⟨encVtx (.varB i b), by rw [ringGraph_adj_enc]; simp [vtxAdj]⟩

end RingClauseGraph

end AlikhaniJafariDisproof
