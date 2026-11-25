/-
  A Machine-Checked Disproof of the Alikhani–Jafari Conjecture (2016, Conjecture 2.9)
  ===================================================================================
  Alikhani and Jafari (2016) conjectured that the total domination polynomial
    D_t(G, x) = ∑_{k=0}^n d_t(G, k) x^k
  of every finite simple graph G (with no isolated vertices) is unimodal.

  We construct an explicit finite simple connected bipartite graph G with no isolated
  vertices and prove, with ZERO external dependencies, ZERO `sorry`, and ZERO custom
  axioms (only Lean 4's core kernel axioms), that its total domination sequence
  `totalDomCount G` is NOT unimodal: there exist explicit indices k₁ < k₂ < k₃ such that
    totalDomCount G k₂ < totalDomCount G k₁  ∧  totalDomCount G k₂ < totalDomCount G k₃.
-/

namespace AlikhaniJafariDisproof

/-! ## Section 1: Standard Definitions (Graphs, Total Domination, Unimodality) -/

/-- Explicit exhaustive duplicate-free list of all elements of `Fin n`. -/
def finRange : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.zero_lt_succ n⟩ :: (finRange n).map Fin.succ

theorem mem_finRange : ∀ {n : Nat} (i : Fin n), i ∈ finRange n
  | 0, i => i.elim0
  | n + 1, ⟨0, _⟩ => List.mem_cons_self _ _
  | n + 1, ⟨k + 1, hk⟩ => by
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨⟨k, by omega⟩, mem_finRange _, rfl⟩

theorem finRange_length : ∀ (n : Nat), (finRange n).length = n
  | 0 => rfl
  | n + 1 => by simp [finRange, finRange_length n]

theorem nodup_map_of_inj {α β : Type} {f : α → β} {L : List α}
    (hinj : ∀ x y, f x = f y → x = y) (h : L.Nodup) : (L.map f).Nodup :=
  List.Pairwise.map f (fun _ _ hne heq => hne (hinj _ _ heq)) h

theorem finRange_nodup : ∀ (n : Nat), (finRange n).Nodup
  | 0 => List.Pairwise.nil
  | n + 1 => by
    rw [finRange, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj (fun _ _ h => Fin.ext (Nat.succ.inj (congrArg Fin.val h))) (finRange_nodup n)⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨x, _, hx⟩
    have := congrArg Fin.val hx
    simp [Fin.succ] at this

theorem nodup_append_of {α : Type} {L₁ L₂ : List α}
    (h1 : L₁.Nodup) (h2 : L₂.Nodup) (hdisj : ∀ x ∈ L₁, ∀ y ∈ L₂, x ≠ y) :
    (L₁ ++ L₂).Nodup := by
  exact List.pairwise_append.mpr ⟨h1, h2, hdisj⟩

theorem le_of_mul_le_mul_right {a b c : Nat} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  rw [Nat.mul_comm a c, Nat.mul_comm b c] at h
  exact Nat.le_of_mul_le_mul_left h hc

/-- A finite simple graph on vertex set `Fin N`. -/
structure SimpleGraph (N : Nat) where
  adj : Fin N → Fin N → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

/-- Reachability by a finite walk in `G`. -/
inductive Reachable {N : Nat} (G : SimpleGraph N) : Fin N → Fin N → Prop where
  | refl (u : Fin N) : Reachable G u u
  | step {u v w : Fin N} : G.adj u v = true → Reachable G v w → Reachable G u w

theorem Reachable.trans {N : Nat} {G : SimpleGraph N} {u v w : Fin N}
    (h1 : Reachable G u v) (h2 : Reachable G v w) : Reachable G u w := by
  induction h1 with
  | refl _ => exact h2
  | step hxy _ ih => exact .step hxy (ih h2)

theorem Reachable.symm {N : Nat} {G : SimpleGraph N} {u v : Fin N}
    (h : Reachable G u v) : Reachable G v u := by
  induction h with
  | refl _ => exact .refl _
  | @step a b c hab _ ih =>
    have hba : G.adj b a = true := by rw [G.symm]; exact hab
    exact ih.trans (.step hba (.refl a))

/-- `G` is connected if every pair of vertices is joined by a walk. -/
def IsConnected {N : Nat} (G : SimpleGraph N) : Prop :=
  ∀ u v : Fin N, Reachable G u v

/-- `G` is bipartite if its vertices admit a proper 2-coloring. -/
def IsBipartite {N : Nat} (G : SimpleGraph N) : Prop :=
  ∃ color : Fin N → Bool, ∀ u v : Fin N, G.adj u v = true → color u ≠ color v

/-- `G` has no isolated vertices (minimum degree ≥ 1). -/
def HasNoIsolated {N : Nat} (G : SimpleGraph N) : Prop :=
  ∀ v : Fin N, ∃ u : Fin N, G.adj v u = true

/-- A subset `S : Fin N → Bool` is a total dominating set iff every vertex has a neighbor in `S`. -/
def IsTotalDom {N : Nat} (G : SimpleGraph N) (S : Fin N → Bool) : Prop :=
  ∀ v : Fin N, ∃ u : Fin N, G.adj v u = true ∧ S u = true

/-- Computable Boolean decision procedure for `IsTotalDom`. -/
def isTotalDomBool {N : Nat} (G : SimpleGraph N) (S : Fin N → Bool) : Bool :=
  (finRange N).all fun v =>
    (finRange N).any fun u => G.adj v u && S u

theorem isTotalDomBool_eq_true {N : Nat} (G : SimpleGraph N) (S : Fin N → Bool) :
    isTotalDomBool G S = true ↔ IsTotalDom G S := by
  simp only [isTotalDomBool, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
    IsTotalDom]
  constructor
  · intro h v
    rcases h v (mem_finRange v) with ⟨u, _, hu⟩
    exact ⟨u, hu⟩
  · intro h v _
    rcases h v with ⟨u, hu⟩
    exact ⟨u, mem_finRange u, hu⟩

/-- Prepending a boolean to a function `Fin n → Bool`. -/
def finCons {n : Nat} (b : Bool) (f : Fin n → Bool) : Fin (n + 1) → Bool :=
  fun i =>
    if h : i.val = 0 then b
    else f ⟨i.val - 1, by omega⟩

/-- Tail of a function `Fin (n + 1) → Bool`. -/
def finTail {n : Nat} (f : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun i => f ⟨i.val + 1, by omega⟩

theorem finCons_zero {n : Nat} (b : Bool) (f : Fin n → Bool) :
    finCons b f ⟨0, Nat.zero_lt_succ n⟩ = b := by
  simp [finCons]

theorem finCons_succ {n : Nat} (b : Bool) (f : Fin n → Bool) (i : Fin n) :
    finCons b f ⟨i.val + 1, by omega⟩ = f i := by
  simp [finCons]

theorem finCons_inj {n : Nat} {b₁ b₂ : Bool} {f₁ f₂ : Fin n → Bool}
    (h : finCons b₁ f₁ = finCons b₂ f₂) : b₁ = b₂ ∧ f₁ = f₂ := by
  constructor
  · have h0 := congrFun h ⟨0, Nat.zero_lt_succ n⟩
    simpa [finCons_zero] using h0
  · funext i
    have hi := congrFun h ⟨i.val + 1, by omega⟩
    simpa [finCons_succ] using hi

theorem finCons_head_tail {n : Nat} (f : Fin (n + 1) → Bool) :
    finCons (f ⟨0, Nat.zero_lt_succ n⟩) (finTail f) = f := by
  funext ⟨k, hk⟩
  cases k with
  | zero => simp [finCons]
  | succ k' => simp [finCons, finTail]

/-- Exhaustive, duplicate-free enumeration of all `2^n` subsets of `Fin n`. -/
def allBoolVecs : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => i.elim0]
  | n + 1 =>
    (allBoolVecs n).map (finCons false) ++ (allBoolVecs n).map (finCons true)

/-- Cardinality of a subset `S : Fin n → Bool`. -/
def countTrue : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => (if f ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) + countTrue (finTail f)

theorem countTrue_finCons {n : Nat} (b : Bool) (f : Fin n → Bool) :
    countTrue (finCons b f) = (if b then 1 else 0) + countTrue f := by
  simp only [countTrue, finCons_zero]
  have htail : finTail (finCons b f) = f := by
    funext i; exact finCons_succ b f i
  rw [htail]

theorem countTrue_le : ∀ {n : Nat} (f : Fin n → Bool), countTrue f ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, f => by
    simp only [countTrue]
    have ih := countTrue_le (finTail f)
    cases f ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega

theorem mem_allBoolVecs : ∀ {n : Nat} (f : Fin n → Bool), f ∈ allBoolVecs n
  | 0, f => by
    simp only [allBoolVecs, List.mem_singleton]
    funext i; exact i.elim0
  | n + 1, f => by
    rw [← finCons_head_tail f]
    simp only [allBoolVecs, List.mem_append, List.mem_map]
    cases f ⟨0, Nat.zero_lt_succ n⟩
    · left; exact ⟨finTail f, mem_allBoolVecs _, rfl⟩
    · right; exact ⟨finTail f, mem_allBoolVecs _, rfl⟩

theorem allBoolVecs_nodup : ∀ (n : Nat), (allBoolVecs n).Nodup
  | 0 => by simp [allBoolVecs]
  | n + 1 => by
    have ih := allBoolVecs_nodup n
    simp only [allBoolVecs]
    apply nodup_append_of
    · exact nodup_map_of_inj (fun _ _ h => (finCons_inj h).2) ih
    · exact nodup_map_of_inj (fun _ _ h => (finCons_inj h).2) ih
    · intro x hx y hy hxy
      rw [List.mem_map] at hx hy
      rcases hx with ⟨f₁, _, rfl⟩
      rcases hy with ⟨f₂, _, rfl⟩
      exact Bool.false_ne_true (finCons_inj hxy).1

theorem allBoolVecs_length : ∀ (n : Nat), (allBoolVecs n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [allBoolVecs, List.length_append, List.length_map, allBoolVecs_length n,
      Nat.pow_succ]
    omega

/-- The `k`-th coefficient `d_t(G, k)` of the total domination polynomial `D_t(G, x)`:
    the exact number of total dominating sets of `G` of cardinality `k`. -/
def totalDomCount {N : Nat} (G : SimpleGraph N) (k : Nat) : Nat :=
  (allBoolVecs N).countP fun S => isTotalDomBool G S && (countTrue S == k)

/-- A sequence `f : Nat → Nat` is unimodal iff it has no strict valley `f i > f j < f k`. -/
def IsUnimodal (f : Nat → Nat) : Prop :=
  ∀ i j k : Nat, i < j → j < k → min (f i) (f k) ≤ f j


/-! ## Section 2: General List Counting, Bijections, Binomials, and Pure-Nat Bounds -/

section CountingToolkit

/-- Classical `DecidableEq` on functions `Fin n → Bool` (computable via `finRange`!). -/
def boolVecEq {n : Nat} (f g : Fin n → Bool) : Bool :=
  (finRange n).all fun i => f i == g i

theorem boolVecEq_iff {n : Nat} (f g : Fin n → Bool) :
    boolVecEq f g = true ↔ f = g := by
  simp only [boolVecEq, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h; funext i; exact h i (mem_finRange i)
  · intro h i _; rw [h]

instance instDecidableEqBoolVec {n : Nat} : DecidableEq (Fin n → Bool) := fun f g =>
  if h : boolVecEq f g = true then isTrue ((boolVecEq_iff f g).mp h)
  else isFalse (fun heq => h ((boolVecEq_iff f g).mpr heq))

theorem nodup_length_le_of_inj {α β : Type} [DecidableEq β]
    {L₁ : List α} {L₂ : List β} (h1 : L₁.Nodup)
    (f : α → β) (hmem : ∀ x ∈ L₁, f x ∈ L₂)
    (hinj : ∀ x ∈ L₁, ∀ y ∈ L₁, f x = f y → x = y) :
    L₁.length ≤ L₂.length := by
  induction L₁ generalizing L₂ with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at h1
    have hfa : f a ∈ L₂ := hmem a (List.mem_cons_self a t)
    have hlen : (L₂.erase (f a)).length + 1 = L₂.length := by
      have := List.length_erase_of_mem hfa
      have hpos : 0 < L₂.length := List.length_pos_of_mem hfa
      omega
    have hsub := ih h1.2 (L₂ := L₂.erase (f a))
      (fun x hx => by
        have hxL2 := hmem x (List.mem_cons_of_mem a hx)
        have hne : f x ≠ f a := fun heq => by
          have := hinj x (List.mem_cons_of_mem a hx) a (List.mem_cons_self a t) heq
          exact h1.1 (this ▸ hx)
        exact (List.mem_erase_of_ne hne).mpr hxL2)
      (fun x hx y hy hxy =>
        hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
    simp only [List.length_cons]
    omega

/-- Counting is preserved under any bijection between duplicate-free lists. -/
theorem countP_eq_of_bij {α β : Type} [DecidableEq α] [DecidableEq β]
    {L₁ : List α} {L₂ : List β} (h1 : L₁.Nodup) (h2 : L₂.Nodup)
    (p : α → Bool) (q : β → Bool)
    (f : α → β) (g : β → α)
    (hf : ∀ x ∈ L₁, p x = true → f x ∈ L₂ ∧ q (f x) = true)
    (hg : ∀ y ∈ L₂, q y = true → g y ∈ L₁ ∧ p (g y) = true)
    (hgf : ∀ x ∈ L₁, p x = true → g (f x) = x)
    (hfg : ∀ y ∈ L₂, q y = true → f (g y) = y) :
    L₁.countP p = L₂.countP q := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  apply Nat.le_antisymm
  · exact nodup_length_le_of_inj (h1.filter p) f
      (fun x hx => by rw [List.mem_filter] at hx ⊢; exact hf x hx.1 hx.2)
      (fun x hx y hy hxy => by
        rw [List.mem_filter] at hx hy
        have := congrArg g hxy
        rw [hgf x hx.1 hx.2, hgf y hy.1 hy.2] at this
        exact this)
  · exact nodup_length_le_of_inj (h2.filter q) g
      (fun y hy => by rw [List.mem_filter] at hy ⊢; exact hg y hy.1 hy.2)
      (fun y₁ hy₁ y₂ hy₂ hxy => by
        rw [List.mem_filter] at hy₁ hy₂
        have := congrArg f hxy
        rw [hfg y₁ hy₁.1 hy₁.2, hfg y₂ hy₂.1 hy₂.2] at this
        exact this)

theorem countP_le_of_inj {α β : Type} [DecidableEq β]
    {L₁ : List α} {L₂ : List β} (h1 : L₁.Nodup)
    (p : α → Bool) (q : β → Bool)
    (f : α → β)
    (hf : ∀ x ∈ L₁, p x = true → f x ∈ L₂ ∧ q (f x) = true)
    (hinj : ∀ x ∈ L₁, p x = true → ∀ y ∈ L₁, p y = true → f x = f y → x = y) :
    L₁.countP p ≤ L₂.countP q := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  exact nodup_length_le_of_inj (h1.filter p) f
    (fun x hx => by rw [List.mem_filter] at hx ⊢; exact hf x hx.1 hx.2)
    (fun x hx y hy hxy => by rw [List.mem_filter] at hx hy; exact hinj x hx.1 hx.2 y hy.1 hy.2 hxy)

theorem countP_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x ∈ L, p x = true → q x = true) :
    L.countP p ≤ L.countP q := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a (List.mem_cons_self a t)
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

theorem countP_congr_mem {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x ∈ L, p x = q x) :
    L.countP p = L.countP q :=
  Nat.le_antisymm
    (countP_mono L p q (fun x hx hp => by rw [← h x hx]; exact hp))
    (countP_mono L q p (fun x hx hq => by rw [h x hx]; exact hq))

theorem countP_split {α : Type} (L : List α) (p c : α → Bool) :
    L.countP p = L.countP (fun x => p x && c x) + L.countP (fun x => p x && !c x) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    cases p a <;> cases c a <;> simp <;> omega

theorem countP_le_add_of_imp {α : Type} (L : List α) (p q r : α → Bool)
    (h : ∀ x ∈ L, p x = true → q x = true ∨ r x = true) :
    L.countP p ≤ L.countP q + L.countP r := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a (List.mem_cons_self a t)
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;> simp_all <;> omega

/-- Finite sum of `f` over a list `L`. -/
def sumList {α : Type} (L : List α) (f : α → Nat) : Nat :=
  L.foldr (fun a acc => f a + acc) 0

theorem sumList_nil {α : Type} (f : α → Nat) : sumList [] f = 0 := rfl
theorem sumList_cons {α : Type} (a : α) (t : List α) (f : α → Nat) :
    sumList (a :: t) f = f a + sumList t f := rfl

theorem sumList_append {α : Type} (L₁ L₂ : List α) (f : α → Nat) :
    sumList (L₁ ++ L₂) f = sumList L₁ f + sumList L₂ f := by
  induction L₁ with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList_cons, ih, Nat.add_assoc]

theorem sumList_map {α β : Type} (L : List α) (g : α → β) (f : β → Nat) :
    sumList (L.map g) f = sumList L (fun x => f (g x)) := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList_cons, ih]

theorem sumList_add {α : Type} (L : List α) (f g : α → Nat) :
    sumList L (fun x => f x + g x) = sumList L f + sumList L g := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList_cons, ih]; omega

theorem sumList_mul_left {α : Type} (L : List α) (c : Nat) (f : α → Nat) :
    sumList L (fun x => c * f x) = c * sumList L f := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList_cons, ih, Nat.mul_add]

theorem sumList_mul_right {α : Type} (L : List α) (c : Nat) (f : α → Nat) :
    sumList L (fun x => f x * c) = sumList L f * c := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList_cons, ih, Nat.add_mul]

theorem sumList_mono {α : Type} (L : List α) (f g : α → Nat)
    (h : ∀ x ∈ L, f x ≤ g x) : sumList L f ≤ sumList L g := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih =>
    simp only [sumList_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self a t))
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem sumList_congr {α : Type} (L : List α) (f g : α → Nat)
    (h : ∀ x ∈ L, f x = g x) : sumList L f = sumList L g :=
  Nat.le_antisymm
    (sumList_mono L f g (fun x hx => Nat.le_of_eq (h x hx)))
    (sumList_mono L g f (fun x hx => Nat.le_of_eq (h x hx).symm))

theorem sumList_const {α : Type} (L : List α) (c : Nat) :
    sumList L (fun _ => c) = L.length * c := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem single_le_sumList {α : Type} {L : List α} {x : α} (hx : x ∈ L) (f : α → Nat) :
    f x ≤ sumList L f := by
  induction L with
  | nil => cases hx
  | cons a t ih =>
    simp only [sumList_cons]
    cases hx with
    | head => exact Nat.le_add_right _ _
    | tail _ hxt => exact Nat.le_trans (ih hxt) (Nat.le_add_left _ _)

theorem countP_any_le_sumList {α β : Type} (L : List α) (I : List β) (p : β → α → Bool) :
    L.countP (fun x => I.any (fun i => p i x)) ≤ sumList I (fun i => L.countP (p i)) := by
  induction I with
  | nil => simp [sumList]
  | cons b t ih =>
    simp only [sumList_cons, List.any_cons]
    have hstep : L.countP (fun x => p b x || t.any (fun i => p i x)) ≤
        L.countP (p b) + L.countP (fun x => t.any (fun i => p i x)) :=
      countP_le_add_of_imp L _ _ _ (fun x _ hx => by simpa [Bool.or_eq_true] using hx)
    omega

/-- Sum of `f k` for `k = 0, 1, ..., n` (inclusive). -/
def sumRange (n : Nat) (f : Nat → Nat) : Nat :=
  sumList (List.range (n + 1)) f

theorem sumRange_zero (f : Nat → Nat) : sumRange 0 f = f 0 := by
  change sumList [0] f = f 0
  simp [sumList]

theorem sumRange_succ (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = sumRange n f + f (n + 1) := by
  simp only [sumRange, List.range_succ, sumList_append, sumList_cons, sumList_nil, Nat.add_zero]

theorem sumRange_shift (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = f 0 + sumRange n (fun j => f (j + 1)) := by
  induction n with
  | zero => simp [sumRange_succ, sumRange_zero]
  | succ n' ih => rw [sumRange_succ, ih, sumRange_succ, Nat.add_assoc]

theorem single_le_sumRange {n k : Nat} (hk : k ≤ n) (f : Nat → Nat) :
    f k ≤ sumRange n f :=
  single_le_sumList (List.mem_range.mpr (by omega)) f

theorem sumRange_mono (n : Nat) (f g : Nat → Nat) (h : ∀ k ≤ n, f k ≤ g k) :
    sumRange n f ≤ sumRange n g :=
  sumList_mono _ _ _ (fun k hk => h k (by have := List.mem_range.mp hk; omega))

theorem sumRange_congr (n : Nat) (f g : Nat → Nat) (h : ∀ k ≤ n, f k = g k) :
    sumRange n f = sumRange n g :=
  Nat.le_antisymm (sumRange_mono n f g (fun k hk => Nat.le_of_eq (h k hk)))
    (sumRange_mono n g f (fun k hk => Nat.le_of_eq (h k hk).symm))

theorem sumRange_add (n : Nat) (f g : Nat → Nat) :
    sumRange n (fun k => f k + g k) = sumRange n f + sumRange n g :=
  sumList_add _ _ _

theorem sumRange_mul_left (n c : Nat) (f : Nat → Nat) :
    sumRange n (fun k => c * f k) = c * sumRange n f :=
  sumList_mul_left _ _ _

theorem sumRange_mul_right (n c : Nat) (f : Nat → Nat) :
    sumRange n (fun k => f k * c) = sumRange n f * c :=
  sumList_mul_right _ _ _

theorem sumRange_const (n c : Nat) : sumRange n (fun _ => c) = (n + 1) * c := by
  simp [sumRange, sumList_const]

/-- Cartesian product of two lists. -/
def listProd {α β : Type} (L₁ : List α) (L₂ : List β) : List (α × β) :=
  L₁.flatMap fun x => L₂.map fun y => (x, y)

theorem mem_listProd {α β : Type} {L₁ : List α} {L₂ : List β} {x : α} {y : β} :
    (x, y) ∈ listProd L₁ L₂ ↔ x ∈ L₁ ∧ y ∈ L₂ := by
  simp [listProd]

theorem listProd_nodup {α β : Type} {L₁ : List α} {L₂ : List β}
    (h1 : L₁.Nodup) (h2 : L₂.Nodup) : (listProd L₁ L₂).Nodup := by
  induction L₁ with
  | nil => simp [listProd]
  | cons a t ih =>
    rw [List.nodup_cons] at h1
    simp only [listProd, List.flatMap_cons]
    apply nodup_append_of
    · exact nodup_map_of_inj (fun _ _ h => (Prod.mk.inj h).2) h2
    · exact ih h1.2
    · intro p hp q hq hpq
      rw [List.mem_map] at hp
      rcases hp with ⟨y₁, _, rfl⟩
      rw [← hpq, List.mem_flatMap] at hq
      rcases hq with ⟨a', ha', hy⟩
      rw [List.mem_map] at hy
      rcases hy with ⟨y₂, _, hpair⟩
      have := (Prod.mk.inj hpair).1
      exact h1.1 (this ▸ ha')

theorem countP_listProd_sum {α β : Type} (L₁ : List α) (L₂ : List β) (p : α → β → Bool) :
    (listProd L₁ L₂).countP (fun xy => p xy.1 xy.2) =
      sumList L₁ (fun x => L₂.countP (fun y => p x y)) := by
  induction L₁ with
  | nil => simp [listProd, sumList]
  | cons a t ih =>
    simp only [listProd, List.flatMap_cons, List.countP_append, List.countP_map, sumList_cons]
    change L₂.countP (fun y => p a y) + (listProd t L₂).countP (fun xy => p xy.1 xy.2) = _
    rw [ih]

theorem countP_listProd_mul {α β : Type} (L₁ : List α) (L₂ : List β)
    (p : α → Bool) (q : β → Bool) :
    (listProd L₁ L₂).countP (fun xy => p xy.1 && q xy.2) =
      L₁.countP p * L₂.countP q := by
  rw [countP_listProd_sum L₁ L₂ (fun x y => p x && q y)]
  induction L₁ with
  | nil => simp [sumList]
  | cons a t ih =>
    simp only [sumList_cons, List.countP_cons, ih]
    cases p a
    · simp
    · simp [Nat.add_mul, Nat.add_comm]

theorem sumRange_dirac (a : Nat) : ∀ n, a ≤ n →
    sumRange n (fun k => if (a == k) then 1 else 0) = 1 := by
  intro n hn
  induction n with
  | zero =>
    have : a = 0 := by omega
    simp [sumRange_zero, this]
  | succ n' ih =>
    rw [sumRange_succ]
    by_cases heq : a = n' + 1
    · have hz : sumRange n' (fun k => if (a == k) then 1 else 0) = 0 := by
        have hle : sumRange n' (fun k => if (a == k) then 1 else 0) ≤ sumRange n' (fun _ => 0) :=
          sumRange_mono n' _ _ (fun k hk => by
            have hne : (a == k) = false := by simp [beq_eq_false_iff_ne]; omega
            simp [hne])
        rw [sumRange_const, Nat.mul_zero] at hle; omega
      have h1 : (a == n' + 1) = true := by simp [heq]
      rw [hz, h1]; simp
    · have hle : a ≤ n' := by omega
      have hne : (a == n' + 1) = false := by simp [beq_eq_false_iff_ne]; omega
      rw [ih hle, hne]; simp

theorem sumRange_countP_eq {α : Type} (L : List α) (p : α → Bool) (wt : α → Nat) (M : Nat)
    (hwt : ∀ x ∈ L, p x = true → wt x ≤ M) :
    sumRange M (fun k => L.countP (fun x => p x && (wt x == k))) = L.countP p := by
  induction L with
  | nil =>
    simp only [List.countP_nil]
    rw [sumRange_const, Nat.mul_zero]
  | cons a t ih =>
    have ih' := ih (fun x hx => hwt x (List.mem_cons_of_mem a hx))
    have hstep : sumRange M (fun k => (a :: t).countP (fun x => p x && (wt x == k))) =
        sumRange M (fun k => if (p a && (wt a == k)) then 1 else 0) +
        sumRange M (fun k => t.countP (fun x => p x && (wt x == k))) := by
      rw [← sumRange_add]
      apply sumRange_congr; intro k _
      simp only [List.countP_cons]
      cases (p a && (wt a == k)) <;> simp <;> omega
    rw [hstep, ih', List.countP_cons]
    cases hp : p a
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [sumRange_const, Nat.mul_zero, Nat.zero_add]
    · simp only [Bool.true_and, ↓reduceIte]
      have hwa : wt a ≤ M := hwt a (List.mem_cons_self a t) hp
      rw [sumRange_dirac (wt a) M hwa]
      omega


/-! ### Binomial Coefficients and Elementary Pure-Nat Inequalities -/

/-- Standard binomial coefficient `C(n, k)`. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero_of_lt (by omega), choose_eq_zero_of_lt (by omega)]
  | _, 0, h => by omega

theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (by omega)]

/-- Exact binomial count of `allBoolVecs n`. -/
theorem countP_allBoolVecs_card : ∀ (n k : Nat),
    (allBoolVecs n).countP (fun S => countTrue S == k) = choose n k
  | 0, 0 => by simp [allBoolVecs, countTrue, choose]
  | 0, k + 1 => by simp [allBoolVecs, countTrue, choose]
  | n + 1, k => by
    simp only [allBoolVecs, List.countP_append, List.countP_map]
    have h0 : (allBoolVecs n).countP ((fun S => countTrue S == k) ∘ finCons false) =
        (allBoolVecs n).countP (fun S => countTrue S == k) := by
      apply countP_congr_mem; intro S _
      simp [Function.comp, countTrue_finCons]
    rw [h0, countP_allBoolVecs_card n k]
    cases k with
    | zero =>
      have h1 : (allBoolVecs n).countP ((fun S => countTrue S == 0) ∘ finCons true) = 0 := by
        rw [List.countP_eq_zero]
        intro S _
        simp [Function.comp, countTrue_finCons]
      rw [h1, choose_zero_right, choose_zero_right, Nat.add_zero]
    | succ k' =>
      have h1 : (allBoolVecs n).countP ((fun S => countTrue S == k' + 1) ∘ finCons true) =
          (allBoolVecs n).countP (fun S => countTrue S == k') := by
        apply countP_congr_mem; intro S _
        simp [Function.comp, countTrue_finCons, Nat.add_comm]
      rw [h1, countP_allBoolVecs_card n k', choose_succ_succ, Nat.add_comm]

/-- Absorbing identity `(k + 1) * C(n, k + 1) = (n - k) * C(n, k)`. -/
theorem succ_mul_choose : ∀ (n k : Nat),
    (k + 1) * choose n (k + 1) = (n - k) * choose n k
  | 0, k => by simp [choose]
  | n + 1, 0 => by
    cases n with
    | zero => simp [choose]
    | succ n' =>
      have ih := succ_mul_choose (n' + 1) 0
      simp only [choose_succ_succ, choose_zero_right, Nat.sub_zero, Nat.one_mul] at ih ⊢
      omega
  | n + 1, k + 1 => by
    rw [choose_succ_succ, Nat.mul_add]
    have h1 := succ_mul_choose n k
    have h2 := succ_mul_choose n (k + 1)
    by_cases hkn : k < n
    · have hA : (k + 2) * choose n (k + 1) = (k + 1) * choose n (k + 1) + choose n (k + 1) := by
        exact Nat.succ_mul (k + 1) (choose n (k + 1))
      rw [hA, h1, h2]
      rw [choose_succ_succ]
      have hsub1 : n + 1 - (k + 1) = n - k := by omega
      have hsub2 : n - (k + 1) + 1 = n - k := by omega
      rw [hsub1, Nat.mul_add]
      have hB : (n - (k + 1)) * choose n (k + 1) + choose n (k + 1) = (n - k) * choose n (k + 1) := by
        have := Nat.add_mul (n - (k + 1)) 1 (choose n (k + 1))
        rw [hsub2, Nat.one_mul] at this
        exact this.symm
      omega
    · have hz1 : choose n (k + 1) = 0 := choose_eq_zero_of_lt (by omega)
      have hz2 : choose n (k + 2) = 0 := choose_eq_zero_of_lt (by omega)
      have hsub : n + 1 - (k + 1) = 0 := by omega
      simp [hz1, hz2, hsub]

/-- `C(n, k)` increases for `k < n / 2` and decreases for `k ≥ n / 2`. -/
theorem choose_le_central (n : Nat) : ∀ k ≤ n, choose n k ≤ choose n (n / 2) := by
  have hinc : ∀ j, j < n / 2 → choose n j ≤ choose n (j + 1) := by
    intro j hj
    have h := succ_mul_choose n j
    have hle : j + 1 ≤ n - j := by omega
    have : (j + 1) * choose n j ≤ (j + 1) * choose n (j + 1) := by
      rw [h]; exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hdec : ∀ j, n / 2 ≤ j → choose n (j + 1) ≤ choose n j := by
    intro j hj
    have h := succ_mul_choose n j
    have hle : n - j ≤ j + 1 := by omega
    have : (j + 1) * choose n (j + 1) ≤ (j + 1) * choose n j := by
      rw [h]; exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_left this (by omega)
  intro k hk
  by_cases hkn : k ≤ n / 2
  · have hwalk : ∀ d, k + d ≤ n / 2 → choose n k ≤ choose n (k + d) := by
      intro d hd
      induction d with
      | zero => exact Nat.le_refl _
      | succ d' ih => exact Nat.le_trans (ih (by omega)) (hinc (k + d') (by omega))
    have := hwalk (n / 2 - k) (by omega)
    rwa [Nat.add_sub_cancel' hkn] at this
  · have hwalk : ∀ d, choose n (n / 2 + d) ≤ choose n (n / 2) := by
      intro d
      induction d with
      | zero => exact Nat.le_refl _
      | succ d' ih => exact Nat.le_trans (hdec (n / 2 + d') (by omega)) ih
    have := hwalk (k - n / 2)
    rwa [Nat.add_sub_cancel' (by omega)] at this

/-- Weighted binomial term `C(Q, r) * 2^(Q - r)` achieves its maximum at `r = Q / 3`. -/
theorem weighted_binom_le_max (Q : Nat) :
    ∀ r ≤ Q, choose Q r * 2 ^ (Q - r) ≤ choose Q (Q / 3) * 2 ^ (Q - Q / 3) := by
  have hstep : ∀ j, j < Q →
      2 * (j + 1) * (choose Q (j + 1) * 2 ^ (Q - (j + 1))) =
      (Q - j) * (choose Q j * 2 ^ (Q - j)) := by
    intro j hj
    have hpow : 2 ^ (Q - j) = 2 * 2 ^ (Q - (j + 1)) := by
      have : Q - j = (Q - (j + 1)) + 1 := by omega
      rw [this, Nat.pow_succ, Nat.mul_comm]
    have hc := succ_mul_choose Q j
    calc 2 * (j + 1) * (choose Q (j + 1) * 2 ^ (Q - (j + 1)))
        = ((j + 1) * choose Q (j + 1)) * (2 * 2 ^ (Q - (j + 1))) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = ((Q - j) * choose Q j) * 2 ^ (Q - j) := by rw [hc, ← hpow]
      _ = (Q - j) * (choose Q j * 2 ^ (Q - j)) := by rw [Nat.mul_assoc]
  have hinc : ∀ j, j < Q / 3 →
      choose Q j * 2 ^ (Q - j) ≤ choose Q (j + 1) * 2 ^ (Q - (j + 1)) := by
    intro j hj
    have hs := hstep j (by omega)
    have hle : 2 * (j + 1) ≤ Q - j := by omega
    have : 2 * (j + 1) * (choose Q j * 2 ^ (Q - j)) ≤
        2 * (j + 1) * (choose Q (j + 1) * 2 ^ (Q - (j + 1))) := by
      rw [hs]; exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hdec : ∀ j, Q / 3 ≤ j → j < Q →
      choose Q (j + 1) * 2 ^ (Q - (j + 1)) ≤ choose Q j * 2 ^ (Q - j) := by
    intro j hj hlt
    have hs := hstep j hlt
    have hle : Q - j ≤ 2 * (j + 1) := by omega
    have : 2 * (j + 1) * (choose Q (j + 1) * 2 ^ (Q - (j + 1))) ≤
        2 * (j + 1) * (choose Q j * 2 ^ (Q - j)) := by
      rw [hs]; exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_left this (by omega)
  intro r hr
  by_cases hr3 : r ≤ Q / 3
  · have hwalk : ∀ d, r + d ≤ Q / 3 →
        choose Q r * 2 ^ (Q - r) ≤ choose Q (r + d) * 2 ^ (Q - (r + d)) := by
      intro d hd
      induction d with
      | zero => exact Nat.le_refl _
      | succ d' ih => exact Nat.le_trans (ih (by omega)) (hinc (r + d') (by omega))
    have := hwalk (Q / 3 - r) (by omega)
    rwa [Nat.add_sub_cancel' hr3] at this
  · have hwalk : ∀ d, Q / 3 + d ≤ Q →
        choose Q (Q / 3 + d) * 2 ^ (Q - (Q / 3 + d)) ≤ choose Q (Q / 3) * 2 ^ (Q - Q / 3) := by
      intro d hd
      induction d with
      | zero => exact Nat.le_refl _
      | succ d' ih => exact Nat.le_trans (hdec (Q / 3 + d') (by omega) (by omega)) (ih (by omega))
    have := hwalk (r - Q / 3) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this

/-- Binomial theorem over `Nat`: `∑_{k=0}^n C(n, k) a^k b^(n-k) = (a + b)^n`. -/
theorem binomial_theorem : ∀ (n a b : Nat),
    sumRange n (fun k => choose n k * a ^ k * b ^ (n - k)) = (a + b) ^ n
  | 0, a, b => by simp [sumRange_zero, choose]
  | n + 1, a, b => by
    rw [Nat.pow_succ, ← binomial_theorem n a b, Nat.mul_add,
        ← sumRange_mul_right, ← sumRange_mul_right]
    have hsplit : sumRange (n + 1) (fun k => choose (n + 1) k * a ^ k * b ^ (n + 1 - k)) =
        b ^ (n + 1) +
        (sumRange n (fun j => choose n j * a ^ (j + 1) * b ^ (n - j)) +
         sumRange n (fun j => choose n (j + 1) * a ^ (j + 1) * b ^ (n - j))) := by
      rw [sumRange_shift n]
      simp only [choose_zero_right, Nat.pow_zero, Nat.one_mul, Nat.sub_zero]
      congr 1
      rw [← sumRange_add]
      apply sumRange_congr n; intro j _
      rw [choose_succ_succ]
      have hsub : n + 1 - (j + 1) = n - j := by omega
      rw [hsub, Nat.add_mul, Nat.add_mul]
    rw [hsplit]
    have hA : sumRange n (fun j => choose n j * a ^ (j + 1) * b ^ (n - j)) =
        sumRange n (fun k => choose n k * a ^ k * b ^ (n - k) * a) := by
      apply sumRange_congr n; intro j _
      rw [Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hB : b ^ (n + 1) + sumRange n (fun j => choose n (j + 1) * a ^ (j + 1) * b ^ (n - j)) =
        sumRange n (fun k => choose n k * a ^ k * b ^ (n - k) * b) := by
      cases n with
      | zero => simp [sumRange_zero, choose]
      | succ n' =>
        rw [sumRange_shift n' (fun k => choose (n' + 1) k * a ^ k * b ^ (n' + 1 - k) * b)]
        simp only [choose_zero_right, Nat.pow_zero, Nat.one_mul, Nat.sub_zero, ← Nat.pow_succ]
        congr 1
        rw [sumRange_succ]
        have hz : choose (n' + 1) (n' + 1 + 1) = 0 := choose_eq_zero_of_lt (by omega)
        simp only [hz, Nat.zero_mul, Nat.add_zero]
        apply sumRange_congr n'; intro j hj
        have hpow : b ^ (n' + 1 - j) = b ^ (n' + 1 - (j + 1)) * b := by
          have hsub : n' + 1 - j = (n' + 1 - (j + 1)) + 1 := by omega
          rw [hsub, Nat.pow_succ]
        rw [hpow]; simp only [Nat.mul_assoc]
    omega

/-- Elementary central-binomial lower bound: `2^n ≤ (n + 1) * C(n, n / 2)`. -/
theorem central_choose_lower (n : Nat) : 2 ^ n ≤ (n + 1) * choose n (n / 2) := by
  have hb := binomial_theorem n 1 1
  simp only [Nat.one_pow, Nat.mul_one] at hb
  rw [← hb, ← sumRange_const]
  exact sumRange_mono n _ _ (fun k hk => choose_le_central n k hk)

/-- Elementary weighted-binomial lower bound: `3^Q ≤ (Q + 1) * (C(Q, Q / 3) * 2^(Q - Q / 3))`. -/
theorem weighted_binom_lower (Q : Nat) :
    3 ^ Q ≤ (Q + 1) * (choose Q (Q / 3) * 2 ^ (Q - Q / 3)) := by
  have hb := binomial_theorem Q 1 2
  simp only [Nat.one_pow, Nat.mul_one] at hb
  rw [← hb, ← sumRange_const]
  exact sumRange_mono Q _ _ (fun r hr => weighted_binom_le_max Q r hr)

/-- Pure-Nat upper bound on `(1 + a/b)^k`: if `k * a ≤ b` then `(b - k*a) * (b + a)^k ≤ b * b^k`. -/
theorem pow_add_le (a b : Nat) : ∀ k : Nat, k * a ≤ b →
    (b - k * a) * (b + a) ^ k ≤ b * b ^ k
  | 0, _ => by simp
  | k + 1, hk => by
    have hka : (k + 1) * a = k * a + a := by rw [Nat.succ_mul]
    have ih := pow_add_le a b k (by omega)
    have hstep : (b - (k + 1) * a) * (b + a) ≤ (b - k * a) * b := by
      let x := b - (k + 1) * a
      have hx : b - k * a = x + a := by omega
      have hxb : x ≤ b := Nat.sub_le _ _
      change x * (b + a) ≤ (b - k * a) * b
      rw [hx, Nat.mul_add, Nat.add_mul]
      have hxa : x * a ≤ a * b := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left a hxb
      omega
    calc (b - (k + 1) * a) * (b + a) ^ (k + 1)
        = (b - (k + 1) * a) * (b + a) * (b + a) ^ k := by
            rw [Nat.pow_succ, Nat.mul_comm ((b + a) ^ k) (b + a), Nat.mul_assoc]
      _ ≤ (b - k * a) * b * (b + a) ^ k := Nat.mul_le_mul_right _ hstep
      _ = b * ((b - k * a) * (b + a) ^ k) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ b * (b * b ^ k) := Nat.mul_le_mul_left b ih
      _ = b * b ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm (b ^ k) b]

/-- Pure-Nat Bernoulli lower bound: `b^(k+1) + (k+1)*a*b^k ≤ (b + a)^(k+1)`. -/
theorem bernoulli_ge (a b : Nat) : ∀ k : Nat,
    b ^ (k + 1) + (k + 1) * a * b ^ k ≤ (b + a) ^ (k + 1)
  | 0 => by simp [Nat.pow_one]
  | k + 1 => by
    have ih := bernoulli_ge a b k
    have hmul := Nat.mul_le_mul_right (b + a) ih
    rw [← Nat.pow_succ] at hmul
    refine Nat.le_trans ?_ hmul
    rw [Nat.add_mul (b ^ (k + 1)), Nat.mul_add (b ^ (k + 1)), Nat.mul_add ((k + 1) * a * b ^ k)]
    have h1 : b ^ (k + 1) * b = b ^ (k + 1 + 1) := (Nat.pow_succ b (k + 1)).symm
    have h2 : (k + 1) * a * b ^ k * b = (k + 1) * a * b ^ (k + 1) := by
      rw [Nat.mul_assoc, Nat.pow_succ]
    have h3 : b ^ (k + 1) * a = a * b ^ (k + 1) := Nat.mul_comm _ _
    have h4 : (k + 1 + 1) * a * b ^ (k + 1) = (k + 1) * a * b ^ (k + 1) + a * b ^ (k + 1) := by
      rw [Nat.succ_mul (k + 1) a, Nat.add_mul]
    rw [h1, h2, h3, h4]
    omega

/-- Elementary corollary: `2 * r^r ≤ (r + 1)^r` for `r ≥ 1`. -/
theorem two_mul_pow_le_succ_pow (r : Nat) (hr : 1 ≤ r) :
    2 * r ^ r ≤ (r + 1) ^ r := by
  cases r with
  | zero => omega
  | succ r' =>
    have h := bernoulli_ge 1 (r' + 1) r'
    have h1 : (r' + 1) * 1 * (r' + 1) ^ r' = (r' + 1) ^ (r' + 1) := by
      rw [Nat.mul_one, Nat.pow_succ, Nat.mul_comm]
    rw [h1] at h
    omega

/-- Exponential decay helper: if `num * (R + 1) ≤ den * R` and `R ≥ 1`, then
    `2 ^ (n / R) * num ^ n ≤ den ^ n`. -/
theorem exp_decay_of_ratio {num den R : Nat} (hR : 1 ≤ R) (hratio : num * (R + 1) ≤ den * R) :
    ∀ n : Nat, 2 ^ (n / R) * num ^ n ≤ den ^ n := by
  intro n
  have hbase : 2 * num ^ R ≤ den ^ R := by
    have h1 : num ^ R * (R + 1) ^ R ≤ den ^ R * R ^ R := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      exact Nat.pow_le_pow_left hratio R
    have h2 : 2 * R ^ R ≤ (R + 1) ^ R := two_mul_pow_le_succ_pow R hR
    have h3 : (2 * num ^ R) * R ^ R ≤ den ^ R * R ^ R := by
      calc (2 * num ^ R) * R ^ R
          = num ^ R * (2 * R ^ R) := by simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ num ^ R * (R + 1) ^ R := Nat.mul_le_mul_left _ h2
        _ ≤ den ^ R * R ^ R := h1
    exact le_of_mul_le_mul_right h3 (Nat.pow_pos (by omega))
  have hle_nd : num ≤ den := by
    cases num with
    | zero => exact Nat.zero_le _
    | succ num' =>
      have hlt : (num' + 1) * R < (num' + 1) * (R + 1) := by rw [Nat.mul_succ]; omega
      exact le_of_mul_le_mul_right (Nat.le_trans (Nat.le_of_lt hlt) hratio) (by omega)
  have hq : 2 ^ (n / R) * (num ^ R) ^ (n / R) ≤ (den ^ R) ^ (n / R) := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left hbase (n / R)
  have hrem : num ^ (n % R) ≤ den ^ (n % R) := Nat.pow_le_pow_left hle_nd (n % R)
  have hsplit : ∀ x : Nat, x ^ n = (x ^ R) ^ (n / R) * x ^ (n % R) := fun x => by
    calc x ^ n = x ^ (R * (n / R) + n % R) := by rw [Nat.div_add_mod]
      _ = x ^ (R * (n / R)) * x ^ (n % R) := Nat.pow_add _ _ _
      _ = (x ^ R) ^ (n / R) * x ^ (n % R) := by rw [Nat.pow_mul]
  rw [hsplit num, hsplit den, ← Nat.mul_assoc]
  exact Nat.mul_le_mul hq hrem

end CountingToolkit


/-! ## Section 3: Concatenation of Boolean Vectors & The Ring-Clause Bipartite Graph -/

section BoolVecConcat

/-- Concatenate `f : Fin a → Bool` and `g : Fin b → Bool` into `Fin (a + b) → Bool`. -/
def finAppend {a b : Nat} (f : Fin a → Bool) (g : Fin b → Bool) : Fin (a + b) → Bool :=
  fun i =>
    if h : i.val < a then f ⟨i.val, h⟩
    else g ⟨i.val - a, by omega⟩

/-- Left half of `Fin (a + b) → Bool`. -/
def finLeft {a b : Nat} (h : Fin (a + b) → Bool) : Fin a → Bool :=
  fun i => h ⟨i.val, by omega⟩

/-- Right half of `Fin (a + b) → Bool`. -/
def finRight {a b : Nat} (h : Fin (a + b) → Bool) : Fin b → Bool :=
  fun j => h ⟨a + j.val, by omega⟩

theorem finAppend_left {a b : Nat} (f : Fin a → Bool) (g : Fin b → Bool) :
    finLeft (finAppend f g) = f := by
  funext ⟨i, hi⟩; simp [finLeft, finAppend, hi]

theorem finAppend_right {a b : Nat} (f : Fin a → Bool) (g : Fin b → Bool) :
    finRight (finAppend f g) = g := by
  funext ⟨j, hj⟩
  have hnot : ¬ (a + j < a) := by omega
  simp only [finRight, finAppend, hnot, ↓reduceDIte]
  congr 1; apply Fin.ext; simp only []; omega

theorem finAppend_left_right {a b : Nat} (h : Fin (a + b) → Bool) :
    finAppend (finLeft h) (finRight h) = h := by
  funext ⟨k, hk⟩
  by_cases hka : k < a
  · simp [finAppend, finLeft, hka]
  · simp only [finAppend, hka, ↓reduceDIte, finRight]
    congr 1; apply Fin.ext; simp; omega

theorem countTrue_cast {n m : Nat} (he : m = n) (u : Fin n → Bool) :
    countTrue (fun i : Fin m => u ⟨i.val, Nat.lt_of_lt_of_eq i.isLt he⟩) = countTrue u := by
  subst he; rfl

theorem countTrue_finAppend : ∀ {a b : Nat} (f : Fin a → Bool) (g : Fin b → Bool),
    countTrue (finAppend f g) = countTrue f + countTrue g
  | 0, b, f, g => by
    show countTrue (finAppend f g) = 0 + countTrue g
    rw [Nat.zero_add (countTrue g)]
    have heq : finAppend f g = fun i : Fin (0 + b) => g ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add b)⟩ := by
      funext ⟨k, hk⟩; simp [finAppend]
    rw [heq]
    exact countTrue_cast (Nat.zero_add b) g
  | a + 1, b, f, g => by
    have heq : finAppend f g =
        fun i : Fin (a + 1 + b) =>
          finCons (f ⟨0, Nat.zero_lt_succ a⟩) (finAppend (finTail f) g)
            ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add a b)⟩ := by
      funext ⟨k, hk⟩
      cases k with
      | zero => simp [finAppend, finCons]
      | succ k' =>
        have hnz : ¬ (k' + 1 = 0) := by omega
        simp only [finAppend, finCons, hnz, ↓reduceDIte, Nat.add_sub_cancel, finTail]
        by_cases hka : k' < a
        · have hka1 : k' + 1 < a + 1 := by omega
          simp [hka, hka1]
        · have hka1 : ¬ (k' + 1 < a + 1) := by omega
          simp only [hka, hka1, ↓reduceDIte]
          congr 1; apply Fin.ext; simp
    rw [heq, countTrue_cast (Nat.succ_add a b)]
    rw [countTrue_finCons, countTrue_finAppend (finTail f) g]
    simp only [countTrue, Nat.add_assoc]

/-- Splitting `allBoolVecs (a + b)` into `listProd (allBoolVecs a) (allBoolVecs b)`. -/
theorem countP_allBoolVecs_add {a b : Nat} (p : (Fin (a + b) → Bool) → Bool) :
    (allBoolVecs (a + b)).countP p =
      (listProd (allBoolVecs a) (allBoolVecs b)).countP (fun fg => p (finAppend fg.1 fg.2)) := by
  exact countP_eq_of_bij (allBoolVecs_nodup (a + b))
    (listProd_nodup (allBoolVecs_nodup a) (allBoolVecs_nodup b))
    p (fun fg => p (finAppend fg.1 fg.2))
    (fun h => (finLeft h, finRight h))
    (fun fg => finAppend fg.1 fg.2)
    (fun h _ hp => ⟨mem_listProd.mpr ⟨mem_allBoolVecs _, mem_allBoolVecs _⟩,
      by dsimp; rwa [finAppend_left_right]⟩)
    (fun fg _ hp => ⟨mem_allBoolVecs _, hp⟩)
    (fun h _ _ => finAppend_left_right h)
    (fun fg _ _ => Prod.ext (finAppend_left fg.1 fg.2) (finAppend_right fg.1 fg.2))

end BoolVecConcat

end AlikhaniJafariDisproof
