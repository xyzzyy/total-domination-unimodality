import AJ.Config

/-! # Bridge: total dominating sets of `ringGraph` ↔ structured configurations

OWNER: Bridge agent. Exported theorem statement below is FROZEN. -/

namespace AlikhaniJafariDisproof

namespace BridgeAux

/-! ## Counting via `List.range` -/

/-- Extension of `f : Fin n → Bool` to `Nat` (false outside the range). -/
def ext {n : Nat} (f : Fin n → Bool) (k : Nat) : Bool :=
  if h : k < n then f ⟨k, h⟩ else false

theorem countTrue_eq_range : ∀ {n : Nat} (f : Fin n → Bool),
    countTrue f = (List.range n).countP (ext f)
  | 0, _ => rfl
  | n + 1, f => by
    rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
    simp only [countTrue]
    rw [countTrue_eq_range (finTail f)]
    have h1 : (ext f ∘ Nat.succ) = ext (finTail f) := by
      funext k
      by_cases hk : k < n
      · have hk' : k + 1 < n + 1 := by omega
        simp [ext, hk, hk', finTail]
      · have hk' : ¬ k + 1 < n + 1 := by omega
        simp [ext, hk, hk']
    rw [h1]
    have h0 : ext f 0 = f ⟨0, Nat.zero_lt_succ n⟩ := by simp [ext]
    rw [h0]
    cases f ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega

theorem countP_range_add (a b : Nat) (g : Nat → Bool) :
    (List.range (a + b)).countP g =
      (List.range a).countP g + (List.range b).countP (fun k => g (a + k)) := by
  rw [List.range_add, List.countP_append, List.countP_map]
  rfl

theorem countP_range_mul : ∀ (m p : Nat) (g : Nat → Bool),
    (List.range (m * p)).countP g =
      sumList (finRange m) (fun i => (List.range p).countP (fun a => g (i.val * p + a)))
  | 0, p, g => by simp [finRange, sumList]
  | m + 1, p, g => by
    rw [Nat.succ_mul, Nat.add_comm, countP_range_add, countP_range_mul m p]
    simp only [finRange, sumList_cons, sumList_map]
    congr 1
    · simp
    · apply sumList_congr
      intro i _
      congr 1
      funext a
      congr 1
      simp only [Fin.val_succ, Nat.succ_mul]
      omega

theorem countP_block (m p : Nat) (g : Nat → Bool) (T : Fin m → Fin p → Bool)
    (hT : ∀ (i : Fin m) (a : Fin p), g (i.val * p + a.val) = T i a) :
    (List.range (m * p)).countP g = sumList (finRange m) (fun i => countTrue (T i)) := by
  rw [countP_range_mul]
  apply sumList_congr
  intro i _
  rw [countTrue_eq_range]
  apply countP_congr_mem
  intro a ha
  have ha' : a < p := List.mem_range.mp ha
  simp only [ext, ha', ↓reduceDIte]
  exact hT i ⟨a, ha'⟩

/-! ## Decomposing a vertex subset -/

/-- The free part (leaf, clauseZ, clauseA) of a vertex subset. -/
def freePart {m p q : Nat} (S : Fin (numV m p q) → Bool) : Fin (numFree m p q) → Bool :=
  fun j => S ⟨1 + j.val, by have := j.isLt; unfold numV; omega⟩

/-- The variable part of a vertex subset, as a block configuration. -/
def toCfg {m p q : Nat} (S : Fin (numV m p q) → Bool) : Fin m → Blk p q :=
  fun i => ⟨fun a => S (encVtx (.varA i a)), fun b => S (encVtx (.varB i b)),
    fun b => S (encVtx (.varZ i b))⟩

theorem countTrue_decomp {m p q : Nat} (S : Fin (numV m p q) → Bool) :
    countTrue S = (if S (encVtx .hub) then 1 else 0) + countTrue (freePart S) +
      cfgSize (toCfg S) := by
  rw [countTrue_eq_range]
  show (List.range (1 + (numFree m p q + (m * p + (m * q + m * q))))).countP (ext S) = _
  rw [countP_range_add, countP_range_add, countP_range_add, countP_range_add]
  have h0 : (List.range 1).countP (ext S) = (if S (encVtx .hub) then 1 else 0) := by
    simp only [List.range_succ_eq_map, List.range_zero, List.map_nil, List.countP_cons,
      List.countP_nil]
    have : ext S 0 = S (encVtx .hub) := by
      simp only [ext]; rw [dif_pos (by unfold numV; omega)]; rfl
    rw [this]; cases S (encVtx .hub) <;> rfl
  have h1 : (List.range (numFree m p q)).countP (fun k => ext S (1 + k)) =
      countTrue (freePart S) := by
    rw [countTrue_eq_range]
    apply countP_congr_mem
    intro a ha
    have ha' : a < numFree m p q := List.mem_range.mp ha
    have hb : 1 + a < numV m p q := by unfold numV; omega
    simp only [ext, ha', hb, ↓reduceDIte, freePart]
  have h2 : (List.range (m * p)).countP (fun k => ext S (1 + (numFree m p q + k))) =
      sumList (finRange m) (fun i => countTrue (toCfg S i).A) := by
    apply countP_block
    intro i a
    have hlt := (encVarA i a).isLt
    have hb : 1 + (numFree m p q + (i.val * p + a.val)) < numV m p q := by
      simp only [encVarA] at hlt; unfold numV; omega
    simp only [ext, hb, ↓reduceDIte, toCfg]
    congr 1; apply Fin.ext; simp only [encVtx, encVarA]; omega
  have h3 : (List.range (m * q)).countP
      (fun k => ext S (1 + (numFree m p q + (m * p + k)))) =
      sumList (finRange m) (fun i => countTrue (toCfg S i).B) := by
    apply countP_block
    intro i b
    have hlt := (encVarBQ i b).isLt
    have hb : 1 + (numFree m p q + (m * p + (i.val * q + b.val))) < numV m p q := by
      simp only [encVarBQ] at hlt; unfold numV; omega
    simp only [ext, hb, ↓reduceDIte, toCfg]
    congr 1; apply Fin.ext; simp only [encVtx, encVarBQ]; omega
  have h4 : (List.range (m * q)).countP
      (fun k => ext S (1 + (numFree m p q + (m * p + (m * q + k))))) =
      sumList (finRange m) (fun i => countTrue (toCfg S i).Z) := by
    apply countP_block
    intro i b
    have hlt := (encVarBQ i b).isLt
    have hb : 1 + (numFree m p q + (m * p + (m * q + (i.val * q + b.val)))) < numV m p q := by
      simp only [encVarBQ] at hlt; unfold numV; omega
    simp only [ext, hb, ↓reduceDIte, toCfg]
    congr 1; apply Fin.ext; simp only [encVtx, encVarBQ]; omega
  rw [h0, h1, h2, h3, h4]
  simp only [cfgSize, blkSize, sumList_add]
  omega

/-! ## Characterizing total domination -/

theorem cfgValid_iff {m p q : Nat} (hm : 0 < m) (x : Fin m → Blk p q) :
    cfgValid hm x = true ↔ ∀ (i : Fin m) (b : Fin q),
      ((x i).B b = true ∨ (x i).Z b = true) ∧
      ((x i).B b = true ∨ ∀ (s : Fin 3) (a : Fin p), (x (shiftBack m hm i s)).A a = true) := by
  simp only [cfgValid, allTrue, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · intro h i b
    have h' := h i (mem_finRange i) b (mem_finRange b)
    refine ⟨h'.1, ?_⟩
    rcases h'.2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (fun s a => h2 s (mem_finRange s) a (mem_finRange a))
  · intro h i _ b _
    refine ⟨(h i b).1, ?_⟩
    rcases (h i b).2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (fun s _ a _ => h2 s a)

theorem vtx_tds_iff {m p q : Nat} (hm : 0 < m) (hq : 0 < q) (T : Vtx m p q → Bool) :
    (∀ v, ∃ u, vtxAdj hm v u = true ∧ T u = true) ↔
      T .hub = true ∧ ∀ (i : Fin m) (b : Fin q),
        (T (.varB i b) = true ∨ T (.varZ i b) = true) ∧
        (T (.varB i b) = true ∨ ∀ (s : Fin 3) (a : Fin p),
          T (.varA (shiftBack m hm i s) a) = true) := by
  constructor
  · intro h
    refine ⟨?_, fun i b => ⟨?_, ?_⟩⟩
    · obtain ⟨u, hu, hT⟩ := h .leaf
      cases u <;> simp [vtxAdj] at hu
      exact hT
    · obtain ⟨u, hu, hT⟩ := h (.clauseZ i b)
      cases u <;> simp [vtxAdj] at hu
      · obtain ⟨rfl, rfl⟩ := hu; exact Or.inl hT
      · obtain ⟨rfl, rfl⟩ := hu; exact Or.inr hT
    · by_cases hB : T (.varB i b) = true
      · exact Or.inl hB
      · refine Or.inr (fun s a => ?_)
        obtain ⟨u, hu, hT⟩ := h (.clauseA i b s a)
        cases u <;> simp [vtxAdj] at hu
        · obtain ⟨rfl, rfl⟩ := hu; exact hT
        · obtain ⟨rfl, rfl⟩ := hu; exact absurd hT hB
  · rintro ⟨hhub, hcl⟩ v
    cases v with
    | hub =>
      rcases (hcl ⟨0, hm⟩ ⟨0, hq⟩).1 with h | h
      · exact ⟨.varB ⟨0, hm⟩ ⟨0, hq⟩, rfl, h⟩
      · exact ⟨.varZ ⟨0, hm⟩ ⟨0, hq⟩, rfl, h⟩
    | leaf => exact ⟨.hub, rfl, hhub⟩
    | varA i a => exact ⟨.hub, rfl, hhub⟩
    | varB i b => exact ⟨.hub, rfl, hhub⟩
    | varZ i b => exact ⟨.hub, rfl, hhub⟩
    | clauseZ i b =>
      rcases (hcl i b).1 with h | h
      · exact ⟨.varB i b, by simp [vtxAdj], h⟩
      · exact ⟨.varZ i b, by simp [vtxAdj], h⟩
    | clauseA i b s a =>
      rcases (hcl i b).2 with h | h
      · exact ⟨.varB i b, by simp [vtxAdj], h⟩
      · exact ⟨.varA (shiftBack m hm i s) a, by simp [vtxAdj], h s a⟩

theorem tds_iff {m p q : Nat} (hm : 0 < m) (hp : 0 < p) (hq : 0 < q)
    (S : Fin (numV m p q) → Bool) :
    isTotalDomBool (ringGraph m p q hm hp hq) S = true ↔
      S (encVtx .hub) = true ∧ cfgValid hm (toCfg S) = true := by
  rw [isTotalDomBool_eq_true, cfgValid_iff]
  have hstep : IsTotalDom (ringGraph m p q hm hp hq) S ↔
      ∀ v : Vtx m p q, ∃ u : Vtx m p q, vtxAdj hm v u = true ∧ S (encVtx u) = true := by
    constructor
    · intro h v
      obtain ⟨u', hu', hS⟩ := h (encVtx v)
      refine ⟨decVtx hp hq u', ?_, ?_⟩
      · rw [← ringGraph_adj_enc hm hp hq, encVtx_decVtx]; exact hu'
      · rw [encVtx_decVtx]; exact hS
    · intro h v'
      obtain ⟨u, hu, hS⟩ := h (decVtx hp hq v')
      refine ⟨encVtx u, ?_, hS⟩
      rw [← encVtx_decVtx hp hq v', ringGraph_adj_enc]; exact hu
  rw [hstep, vtx_tds_iff hm hq]
  rfl

/-! ## The inverse map -/

theorem numFree_pos (m p q : Nat) : 0 < numFree m p q := by unfold numFree; omega

/-- Vertex-level assembly of a subset from `(F, x)`. -/
def buildV {m p q : Nat} (F : Fin (numFree m p q) → Bool) (x : Fin m → Blk p q) :
    Vtx m p q → Bool
  | .hub => true
  | .leaf => F ⟨0, numFree_pos m p q⟩
  | .clauseZ i b => F (encClauseZ i b)
  | .clauseA i b s a => F (encClauseA i b s a)
  | .varA i a => (x i).A a
  | .varB i b => (x i).B b
  | .varZ i b => (x i).Z b

/-- Assembly of a subset of `Fin (numV m p q)` from `(F, x)`. -/
def build {m p q : Nat} (hp : 0 < p) (hq : 0 < q) (F : Fin (numFree m p q) → Bool)
    (x : Fin m → Blk p q) : Fin (numV m p q) → Bool :=
  fun v => buildV F x (decVtx hp hq v)

theorem build_enc {m p q : Nat} (hp : 0 < p) (hq : 0 < q) (F : Fin (numFree m p q) → Bool)
    (x : Fin m → Blk p q) (u : Vtx m p q) : build hp hq F x (encVtx u) = buildV F x u := by
  simp only [build, decVtx_encVtx]

theorem buildV_free {m p q : Nat} (F : Fin (numFree m p q) → Bool) (x : Fin m → Blk p q)
    (w : Vtx m p q) (j : Fin (numFree m p q)) (hw : (encVtx w).val = 1 + j.val) :
    buildV F x w = F j := by
  have hj := j.isLt
  cases w with
  | hub => simp [encVtx] at hw; omega
  | leaf =>
    simp only [encVtx] at hw
    simp only [buildV]; congr 1; apply Fin.ext; simp only []; omega
  | clauseZ i b =>
    simp only [encVtx] at hw
    simp only [buildV]; congr 1; apply Fin.ext; omega
  | clauseA i b s a =>
    simp only [encVtx] at hw
    simp only [buildV]; congr 1; apply Fin.ext; omega
  | varA i a => simp only [encVtx] at hw; omega
  | varB i b => simp only [encVtx] at hw; omega
  | varZ i b => simp only [encVtx] at hw; omega

theorem freePart_build {m p q : Nat} (hp : 0 < p) (hq : 0 < q)
    (F : Fin (numFree m p q) → Bool) (x : Fin m → Blk p q) :
    freePart (build hp hq F x) = F := by
  funext j
  simp only [freePart, build]
  apply buildV_free
  rw [encVtx_decVtx]

theorem toCfg_build {m p q : Nat} (hp : 0 < p) (hq : 0 < q)
    (F : Fin (numFree m p q) → Bool) (x : Fin m → Blk p q) :
    toCfg (build hp hq F x) = x := by
  funext i
  simp only [toCfg, build_enc, buildV]

theorem build_hub {m p q : Nat} (hp : 0 < p) (hq : 0 < q)
    (F : Fin (numFree m p q) → Bool) (x : Fin m → Blk p q) :
    build hp hq F x (encVtx .hub) = true := by
  rw [build_enc]; rfl

theorem build_parts {m p q : Nat} (hp : 0 < p) (hq : 0 < q) (S : Fin (numV m p q) → Bool)
    (hS : S (encVtx .hub) = true) :
    build hp hq (freePart S) (toCfg S) = S := by
  funext v
  rw [← encVtx_decVtx hp hq v, build_enc]
  cases decVtx hp hq v with
  | hub => exact hS.symm
  | leaf => simp only [buildV, freePart]; congr 1
  | clauseZ i b => rfl
  | clauseA i b s a => rfl
  | varA i a => rfl
  | varB i b => rfl
  | varZ i b => rfl

end BridgeAux

theorem totalDomCount_eq (m p q : Nat) (hm : 0 < m) (hp : 0 < p) (hq : 0 < q) (k : Nat) :
    totalDomCount (ringGraph m p q hm hp hq) k = cfgCount m p q hm k := by
  unfold totalDomCount cfgCount
  apply countP_eq_of_bij (allBoolVecs_nodup _)
    (listProd_nodup (allBoolVecs_nodup _) (allFuns_nodup (allBlks_nodup p q) m))
    _ _ (fun S => (BridgeAux.freePart S, BridgeAux.toCfg S))
    (fun Fx => BridgeAux.build hp hq Fx.1 Fx.2)
  · intro S _ hS
    refine ⟨mem_listProd.mpr ⟨mem_allBoolVecs _, mem_allFuns _ (fun _ => mem_allBlks _)⟩, ?_⟩
    rw [Bool.and_eq_true, BridgeAux.tds_iff, beq_iff_eq, BridgeAux.countTrue_decomp] at hS
    obtain ⟨⟨hhub, hval⟩, hk⟩ := hS
    rw [hhub] at hk
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hval, by simpa using hk⟩
  · intro Fx _ hFx
    refine ⟨mem_allBoolVecs _, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hFx
    rw [Bool.and_eq_true, BridgeAux.tds_iff, beq_iff_eq, BridgeAux.countTrue_decomp,
      BridgeAux.freePart_build, BridgeAux.toCfg_build, BridgeAux.build_hub]
    exact ⟨⟨rfl, hFx.1⟩, by simpa using hFx.2⟩
  · intro S _ hS
    rw [Bool.and_eq_true, BridgeAux.tds_iff] at hS
    exact BridgeAux.build_parts hp hq S hS.1.1
  · intro Fx _ _
    exact Prod.ext (BridgeAux.freePart_build hp hq _ _) (BridgeAux.toCfg_build hp hq _ _)

end AlikhaniJafariDisproof
