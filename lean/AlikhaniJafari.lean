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


/-!
# Shared interface: the structured configuration space

FROZEN INTERFACE. Do not change any definition or theorem *statement* in this file.
(All proofs in this file are complete.)

A total dominating set `S` of `ringGraph m p q` is the same thing as
* `S hub = true`,
* an arbitrary assignment `F : Fin (numFree m p q) → Bool` of the free vertices
  (leaf, clauseZ, clauseA), and
* a *valid* block configuration `x : Fin m → Blk p q` of the variable vertices,
with `|S| = 1 + |F| + cfgSize x`.  (This is `Bridge.totalDomCount_eq`.)
-/

namespace AlikhaniJafariDisproof

/-! ## Generic enumeration of functions `Fin n → α` -/

/-- Prepend an element to a function `Fin n → α`. -/
def finConsG {α : Type} {n : Nat} (a : α) (f : Fin n → α) : Fin (n + 1) → α :=
  fun i => if h : i.val = 0 then a else f ⟨i.val - 1, by omega⟩

/-- All functions `Fin n → α` whose values lie in `L` (duplicate-free when `L` is). -/
def allFuns {α : Type} (L : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [fun i => i.elim0]
  | n + 1 => L.flatMap fun a => (allFuns L n).map (finConsG a)

namespace ConfigAux

theorem finConsG_head_tail {α : Type} {n : Nat} (f : Fin (n + 1) → α) :
    finConsG (f ⟨0, Nat.zero_lt_succ n⟩) (fun i : Fin n => f ⟨i.val + 1, by omega⟩) = f := by
  funext ⟨k, hk⟩
  cases k with
  | zero => simp [finConsG]
  | succ k' => simp [finConsG]

theorem finConsG_inj {α : Type} {n : Nat} {a b : α} {f g : Fin n → α}
    (h : finConsG a f = finConsG b g) : a = b ∧ f = g := by
  constructor
  · have := congrFun h ⟨0, Nat.zero_lt_succ n⟩
    simpa [finConsG] using this
  · funext i
    have := congrFun h ⟨i.val + 1, by omega⟩
    simpa [finConsG] using this

theorem nodup_flatMap_of {α β : Type} (f : α → List β) : ∀ (L : List α),
    (∀ a ∈ L, (f a).Nodup) →
    L.Pairwise (fun a b => ∀ x ∈ f a, ∀ y ∈ f b, x ≠ y) → (L.flatMap f).Nodup
  | [], _, _ => List.Pairwise.nil
  | a :: L, h1, h2 => by
    rw [List.flatMap_cons]
    rw [List.pairwise_cons] at h2
    apply nodup_append_of (h1 a (List.mem_cons_self _ _))
      (nodup_flatMap_of f L (fun b hb => h1 b (List.mem_cons_of_mem _ hb)) h2.2)
    intro x hx y hy
    rw [List.mem_flatMap] at hy
    rcases hy with ⟨b, hb, hyb⟩
    exact h2.1 b hb x hx y hyb

end ConfigAux

open ConfigAux in
theorem mem_allFuns {α : Type} {L : List α} :
    ∀ {n : Nat} (f : Fin n → α), (∀ i, f i ∈ L) → f ∈ allFuns L n
  | 0, f, _ => by
    simp only [allFuns, List.mem_singleton]
    funext i; exact i.elim0
  | n + 1, f, hf => by
    rw [← finConsG_head_tail f]
    simp only [allFuns, List.mem_flatMap, List.mem_map]
    exact ⟨_, hf _, _, mem_allFuns _ (fun i => hf _), rfl⟩

open ConfigAux in
theorem allFuns_nodup {α : Type} {L : List α} (hL : L.Nodup) :
    ∀ n : Nat, (allFuns L n).Nodup
  | 0 => by simp [allFuns]
  | n + 1 => by
    simp only [allFuns]
    apply nodup_flatMap_of _ L
      (fun a _ => nodup_map_of_inj (fun _ _ h => (finConsG_inj h).2) (allFuns_nodup hL n))
    refine List.Pairwise.imp ?_ hL
    intro a b hab x hx y hy hxy
    rw [List.mem_map] at hx hy
    rcases hx with ⟨f, _, rfl⟩
    rcases hy with ⟨g, _, rfl⟩
    exact hab (finConsG_inj hxy).1

/-- Decidable equality of functions `Fin n → α` (computable via `finRange`). -/
instance (priority := low) instDecidableEqFinFun {α : Type} [DecidableEq α] {n : Nat} :
    DecidableEq (Fin n → α) := fun f g =>
  if h : (finRange n).all (fun i => decide (f i = g i)) = true then
    isTrue (by
      funext i
      have := List.all_eq_true.mp h i (mem_finRange i)
      simpa using this)
  else
    isFalse (fun heq => h (List.all_eq_true.mpr (fun i _ => by simp [heq])))

/-! ## Blocks -/

/-- The variable vertices of block `i`: its `A`-row (`p` bits), `B`-row and `Z`-row (`q` bits each). -/
structure Blk (p q : Nat) where
  A : Fin p → Bool
  B : Fin q → Bool
  Z : Fin q → Bool

instance instDecidableEqBlk {p q : Nat} : DecidableEq (Blk p q) := fun x y =>
  if h : x.A = y.A ∧ x.B = y.B ∧ x.Z = y.Z then
    isTrue (by cases x; cases y; simp only at h; rcases h with ⟨rfl, rfl, rfl⟩; rfl)
  else
    isFalse (fun heq => h (by subst heq; exact ⟨rfl, rfl, rfl⟩))

/-- All `2^(p + 2q)` block configurations. -/
def allBlks (p q : Nat) : List (Blk p q) :=
  (allBoolVecs p).flatMap fun A =>
    (allBoolVecs q).flatMap fun B =>
      (allBoolVecs q).map fun Z => (⟨A, B, Z⟩ : Blk p q)

theorem mem_allBlks {p q : Nat} (β : Blk p q) : β ∈ allBlks p q := by
  cases β with
  | mk A B Z =>
    simp only [allBlks, List.mem_flatMap, List.mem_map]
    exact ⟨A, mem_allBoolVecs A, B, mem_allBoolVecs B, Z, mem_allBoolVecs Z, rfl⟩

open ConfigAux in
theorem allBlks_nodup (p q : Nat) : (allBlks p q).Nodup := by
  unfold allBlks
  apply nodup_flatMap_of _ _
  · intro A _
    apply nodup_flatMap_of _ _
    · intro B _
      exact nodup_map_of_inj (fun Z Z' h => by cases h; rfl) (allBoolVecs_nodup q)
    · refine List.Pairwise.imp ?_ (allBoolVecs_nodup q)
      intro B B' hB x hx y hy hxy
      rw [List.mem_map] at hx hy
      rcases hx with ⟨Z, _, rfl⟩
      rcases hy with ⟨Z', _, rfl⟩
      exact hB (congrArg Blk.B hxy)
  · refine List.Pairwise.imp ?_ (allBoolVecs_nodup p)
    intro A A' hA x hx y hy hxy
    rw [List.mem_flatMap] at hx hy
    rcases hx with ⟨B, _, hx⟩
    rcases hy with ⟨B', _, hy⟩
    rw [List.mem_map] at hx hy
    rcases hx with ⟨Z, _, rfl⟩
    rcases hy with ⟨Z', _, rfl⟩
    exact hA (congrArg Blk.A hxy)

/-! ## Sizes, validity, and the counts -/

/-- `true` iff every coordinate is `true`. -/
def allTrue {n : Nat} (f : Fin n → Bool) : Bool := (finRange n).all f

/-- Number of chosen vertices in one block. -/
def blkSize {p q : Nat} (β : Blk p q) : Nat :=
  countTrue β.A + countTrue β.B + countTrue β.Z

/-- Number of chosen variable vertices in a configuration. -/
def cfgSize {m p q : Nat} (x : Fin m → Blk p q) : Nat :=
  sumList (finRange m) fun i => blkSize (x i)

/-- Validity = the clause constraints:
  `clauseZ i b` needs `B i b ∨ Z i b`;
  `clauseA i b s a` needs `B i b ∨ A (i - s mod m) a` for all `s < 3`, `a < p`. -/
def cfgValid {m p q : Nat} (hm : 0 < m) (x : Fin m → Blk p q) : Bool :=
  (finRange m).all fun i => (finRange q).all fun b =>
    ((x i).B b || (x i).Z b) &&
    ((x i).B b || (finRange 3).all fun s => allTrue (x (shiftBack m hm i s)).A)

/-- `cfgCount m p q hm k` = number of pairs `(F, x)` with `x` valid and `1 + |F| + |x| = k`.
    By `Bridge.totalDomCount_eq` this is `d_t(ringGraph m p q, k)`. -/
def cfgCount (m p q : Nat) (hm : 0 < m) (k : Nat) : Nat :=
  (listProd (allBoolVecs (numFree m p q)) (allFuns (allBlks p q) m)).countP
    fun Fx => cfgValid hm Fx.2 && (1 + countTrue Fx.1 + cfgSize Fx.2 == k)

/-- Every `B` vertex chosen. -/
def allBOnes {m p q : Nat} (x : Fin m → Blk p q) : Bool :=
  (finRange m).all fun i => allTrue (x i).B

/-- Every `A` vertex chosen. -/
def allAOnes {m p q : Nat} (x : Fin m → Blk p q) : Bool :=
  (finRange m).all fun i => allTrue (x i).A

/-- Valid configurations that are neither "all `B`" nor "all `A`" (of any size). -/
def mixedCount (m p q : Nat) (hm : 0 < m) : Nat :=
  (allFuns (allBlks p q) m).countP fun x => cfgValid hm x && !allBOnes x && !allAOnes x

end AlikhaniJafariDisproof


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


/-! # Families: peak lower bounds and the valley decomposition

OWNER: Families agent. The four exported theorem statements below are FROZEN.
The *definition* of `fam2Count` may be changed by the owner (only Families.lean uses its body). -/

namespace AlikhaniJafariDisproof

namespace FamAux

/-! ## Block ↔ flat vectors -/

theorem blk_idx_lt {m r i j : Nat} (hi : i < m) (hj : j < r) : i * r + j < m * r := by
  have h : (i + 1) * r ≤ m * r := Nat.mul_le_mul_right r hi
  rw [Nat.succ_mul] at h; omega

theorem pos_of_lt_mul {m r k : Nat} (h : k < m * r) : 0 < r := by
  cases r with
  | zero => rw [Nat.mul_zero] at h; omega
  | succ r => omega

/-- Split a flat vector of length `m * r` into `m` rows of length `r`. -/
def toBlocks {m r : Nat} (f : Fin (m * r) → Bool) (i : Fin m) : Fin r → Bool :=
  fun j => f ⟨i.val * r + j.val, blk_idx_lt i.isLt j.isLt⟩

/-- Flatten `m` rows of length `r` into one vector of length `m * r`. -/
def fromBlocks {m r : Nat} (g : Fin m → Fin r → Bool) (k : Fin (m * r)) : Bool :=
  g ⟨k.val / r, (Nat.div_lt_iff_lt_mul (pos_of_lt_mul k.isLt)).mpr k.isLt⟩
    ⟨k.val % r, Nat.mod_lt _ (pos_of_lt_mul k.isLt)⟩

theorem toBlocks_fromBlocks {m r : Nat} (g : Fin m → Fin r → Bool) :
    toBlocks (fromBlocks g) = g := by
  funext i j
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have h1 : (i.val * r + j.val) / r = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have h2 : (i.val * r + j.val) % r = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  simp only [toBlocks, fromBlocks]
  congr 1
  · exact Fin.ext h1
  · exact Fin.ext h2

theorem fromBlocks_toBlocks {m r : Nat} (f : Fin (m * r) → Bool) :
    fromBlocks (toBlocks f) = f := by
  funext k
  simp only [toBlocks, fromBlocks]
  congr 1
  apply Fin.ext
  have := Nat.div_add_mod k.val r
  simp only [Nat.mul_comm r] at this
  exact this

theorem toBlocks_inj {m r : Nat} {f g : Fin (m * r) → Bool} (h : toBlocks f = toBlocks g) :
    f = g := by
  rw [← fromBlocks_toBlocks f, ← fromBlocks_toBlocks g, h]

theorem fromBlocks_inj {m r : Nat} {f g : Fin m → Fin r → Bool} (h : fromBlocks f = fromBlocks g) :
    f = g := by
  rw [← toBlocks_fromBlocks f, ← toBlocks_fromBlocks g, h]

/-- Number of `true`s of `g` on `[lo, lo + n)`. -/
def cntN (g : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | lo, n + 1 => (if g lo then 1 else 0) + cntN g (lo + 1) n

theorem countTrue_eq_cntN : ∀ {n : Nat} (f : Fin n → Bool) (g : Nat → Bool) (lo : Nat),
    (∀ k (h : k < n), g (lo + k) = f ⟨k, h⟩) → countTrue f = cntN g lo n
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, lo, h => by
    simp only [countTrue, cntN]
    have h0 : g lo = f ⟨0, Nat.zero_lt_succ n⟩ := h 0 (Nat.zero_lt_succ n)
    rw [h0, countTrue_eq_cntN (finTail f) g (lo + 1) (fun k hk => by
      have := h (k + 1) (by omega)
      rw [show lo + 1 + k = lo + (k + 1) by omega, this]; rfl)]

theorem cntN_add (g : Nat → Bool) : ∀ (a b lo : Nat),
    cntN g lo (a + b) = cntN g lo a + cntN g (lo + a) b
  | 0, b, lo => by simp [cntN]
  | a + 1, b, lo => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [cntN]
    rw [cntN_add g a b (lo + 1), show lo + 1 + a = lo + (a + 1) by omega, Nat.add_assoc]

theorem sum_cntN (g : Nat → Bool) (r : Nat) : ∀ (m lo : Nat),
    sumList (finRange m) (fun i => cntN g (lo + i.val * r) r) = cntN g lo (m * r)
  | 0, lo => by simp [finRange, sumList, cntN]
  | m + 1, lo => by
    simp only [finRange, sumList_cons, sumList_map]
    have hc : sumList (finRange m) (fun i => cntN g (lo + (Fin.succ i).val * r) r) =
        sumList (finRange m) (fun i => cntN g ((lo + r) + i.val * r) r) := by
      apply sumList_congr; intro i _
      rw [Fin.val_succ, Nat.succ_mul, show lo + (i.val * r + r) = lo + r + i.val * r by omega]
    rw [hc, sum_cntN g r m (lo + r), Nat.succ_mul, Nat.add_comm (m * r) r, cntN_add]
    simp

/-- Extension of a vector to `Nat` (false outside). -/
def extN {n : Nat} (f : Fin n → Bool) (k : Nat) : Bool :=
  if h : k < n then f ⟨k, h⟩ else false

theorem countTrue_toBlocks_sum {m r : Nat} (f : Fin (m * r) → Bool) :
    sumList (finRange m) (fun i => countTrue (toBlocks f i)) = countTrue f := by
  have h1 : countTrue f = cntN (extN f) 0 (m * r) :=
    countTrue_eq_cntN f _ 0 (fun k hk => by simp [extN, hk])
  have h2 : ∀ i : Fin m, countTrue (toBlocks f i) = cntN (extN f) (0 + i.val * r) r := by
    intro i
    apply countTrue_eq_cntN
    intro k hk
    have hlt : 0 + i.val * r + k < m * r := by
      have := blk_idx_lt i.isLt hk; omega
    simp only [extN, hlt, ↓reduceDIte, toBlocks]
    congr 1; apply Fin.ext; simp
  rw [h1, ← sum_cntN]
  exact sumList_congr _ _ _ (fun i _ => h2 i)

theorem countTrue_fromBlocks {m r : Nat} (g : Fin m → Fin r → Bool) :
    countTrue (fromBlocks g) = sumList (finRange m) (fun i => countTrue (g i)) := by
  rw [← countTrue_toBlocks_sum (fromBlocks g), toBlocks_fromBlocks]

/-! ## Small facts about rows, blocks and configurations -/

theorem countTrue_const_true : ∀ (n : Nat), countTrue (fun _ : Fin n => true) = n
  | 0 => rfl
  | n + 1 => by
    simp only [countTrue, ↓reduceIte]
    rw [show (finTail fun _ : Fin (n + 1) => true) = (fun _ : Fin n => true) from rfl,
      countTrue_const_true n, Nat.add_comm]

theorem countTrue_of_all {n : Nat} (f : Fin n → Bool) (h : ∀ i, f i = true) :
    countTrue f = n := by
  have : f = fun _ => true := funext h
  rw [this, countTrue_const_true]

theorem allTrue_iff {n : Nat} (f : Fin n → Bool) : allTrue f = true ↔ ∀ i, f i = true := by
  simp only [allTrue, List.all_eq_true]
  exact ⟨fun h i => h i (mem_finRange i), fun h i _ => h i⟩

theorem allTrue_const_true (n : Nat) : allTrue (fun _ : Fin n => true) = true :=
  (allTrue_iff _).mpr (fun _ => rfl)

theorem allBOnes_iff {m p q : Nat} (x : Fin m → Blk p q) :
    allBOnes x = true ↔ ∀ i b, (x i).B b = true := by
  simp only [allBOnes, List.all_eq_true, allTrue_iff]
  exact ⟨fun h i => h i (mem_finRange i), fun h i _ => h i⟩

theorem allAOnes_iff {m p q : Nat} (x : Fin m → Blk p q) :
    allAOnes x = true ↔ ∀ i a, (x i).A a = true := by
  simp only [allAOnes, List.all_eq_true, allTrue_iff]
  exact ⟨fun h i => h i (mem_finRange i), fun h i _ => h i⟩

theorem cfgValid_iff {m p q : Nat} (hm : 0 < m) (x : Fin m → Blk p q) :
    cfgValid hm x = true ↔ ∀ i b, ((x i).B b || (x i).Z b) = true ∧
      ((x i).B b || (finRange 3).all fun s => allTrue (x (shiftBack m hm i s)).A) = true := by
  simp only [cfgValid, List.all_eq_true, Bool.and_eq_true]
  exact ⟨fun h i b => h i (mem_finRange i) b (mem_finRange b),
    fun h i _ b _ => h i b⟩

theorem blk_ext {p q : Nat} {β γ : Blk p q} (hA : β.A = γ.A) (hB : β.B = γ.B) (hZ : β.Z = γ.Z) :
    β = γ := by
  cases β; cases γ; simp only at hA hB hZ; subst hA; subst hB; subst hZ; rfl

theorem cfgSize_eq {m p q : Nat} (x : Fin m → Blk p q) :
    cfgSize x = sumList (finRange m) (fun i => countTrue (x i).A) +
      sumList (finRange m) (fun i => countTrue (x i).B) +
      sumList (finRange m) (fun i => countTrue (x i).Z) := by
  unfold cfgSize blkSize
  rw [sumList_add _ (fun i => countTrue (x i).A + countTrue (x i).B) (fun i => countTrue (x i).Z),
    sumList_add]

theorem sum_const_finRange (m c : Nat) : sumList (finRange m) (fun _ => c) = m * c := by
  rw [sumList_const, finRange_length]

theorem mem_cfgs {m p q : Nat} (x : Fin m → Blk p q) : x ∈ allFuns (allBlks p q) m :=
  mem_allFuns x (fun i => mem_allBlks (x i))

theorem cfgs_nodup (m p q : Nat) : (allFuns (allBlks p q) m).Nodup :=
  allFuns_nodup (allBlks_nodup p q) m

theorem mem_prod_cfgs {C m p q : Nat} (F : Fin C → Bool) (x : Fin m → Blk p q) :
    (F, x) ∈ listProd (allBoolVecs C) (allFuns (allBlks p q) m) :=
  mem_listProd.mpr ⟨mem_allBoolVecs F, mem_cfgs x⟩

theorem prod_cfgs_nodup (C m p q : Nat) :
    (listProd (allBoolVecs C) (allFuns (allBlks p q) m)).Nodup :=
  listProd_nodup (allBoolVecs_nodup C) (cfgs_nodup m p q)

theorem beq_congr {a b c d : Nat} (h : a = b ↔ c = d) : (a == b) = (c == d) := by
  cases h1 : (a == b) <;> cases h2 : (c == d) <;> simp_all

/-! ## Covering pairs `(B, Z)` with `B ∨ Z` pointwise -/

/-- All pairs `(B, Z)` of length `n` with `B j ∨ Z j` for every `j`. -/
def pairVecs : (n : Nat) → List ((Fin n → Bool) × (Fin n → Bool))
  | 0 => [(fun i => i.elim0, fun i => i.elim0)]
  | n + 1 =>
    (pairVecs n).map (fun bz => (finCons true bz.1, finCons false bz.2)) ++
    (pairVecs n).map (fun bz => (finCons false bz.1, finCons true bz.2)) ++
    (pairVecs n).map (fun bz => (finCons true bz.1, finCons true bz.2))

theorem mem_pairVecs : ∀ {n : Nat} (B Z : Fin n → Bool),
    (B, Z) ∈ pairVecs n ↔ ∀ j, (B j || Z j) = true
  | 0, B, Z => by
    simp only [pairVecs, List.mem_singleton]
    constructor
    · intro _ j; exact j.elim0
    · intro _; congr <;> funext j <;> exact j.elim0
  | n + 1, B, Z => by
    constructor
    · intro h j
      simp only [pairVecs, List.mem_append, List.mem_map] at h
      rcases h with ((⟨⟨B', Z'⟩, hm, he⟩ | ⟨⟨B', Z'⟩, hm, he⟩) | ⟨⟨B', Z'⟩, hm, he⟩) <;>
      · have ih := (mem_pairVecs B' Z').mp hm
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        rcases j with ⟨k, hk⟩
        cases k with
        | zero => simp [finCons]
        | succ k =>
          have := ih ⟨k, by omega⟩
          simpa [finCons] using this
    · intro h
      rw [← finCons_head_tail B, ← finCons_head_tail Z]
      have ht : (finTail B, finTail Z) ∈ pairVecs n :=
        (mem_pairVecs _ _).mpr (fun j => h ⟨j.val + 1, by omega⟩)
      have h0 := h ⟨0, Nat.zero_lt_succ n⟩
      simp only [pairVecs, List.mem_append, List.mem_map]
      cases hb : B ⟨0, Nat.zero_lt_succ n⟩ <;> cases hz : Z ⟨0, Nat.zero_lt_succ n⟩ <;>
        rw [hb, hz] at h0
      · simp at h0
      · exact Or.inl (Or.inr ⟨_, ht, rfl⟩)
      · exact Or.inl (Or.inl ⟨_, ht, rfl⟩)
      · exact Or.inr ⟨_, ht, rfl⟩

theorem pairVecs_nodup : ∀ (n : Nat), (pairVecs n).Nodup
  | 0 => by simp [pairVecs]
  | n + 1 => by
    have ih := pairVecs_nodup n
    have inj : ∀ (b c : Bool), ∀ x y : (Fin n → Bool) × (Fin n → Bool),
        (finCons b x.1, finCons c x.2) = (finCons b y.1, finCons c y.2) → x = y := by
      intro b c x y h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (finCons_inj h.1).2 (finCons_inj h.2).2
    simp only [pairVecs]
    apply nodup_append_of
    · apply nodup_append_of
      · exact nodup_map_of_inj (inj true false) ih
      · exact nodup_map_of_inj (inj false true) ih
      · intro x hx y hy hxy
        rw [List.mem_map] at hx hy
        rcases hx with ⟨a, _, rfl⟩
        rcases hy with ⟨b, _, rfl⟩
        simp only [Prod.mk.injEq] at hxy
        exact Bool.noConfusion (finCons_inj hxy.1).1
    · exact nodup_map_of_inj (inj true true) ih
    · intro x hx y hy hxy
      rw [List.mem_append, List.mem_map, List.mem_map] at hx
      rw [List.mem_map] at hy
      rcases hy with ⟨b, _, rfl⟩
      rcases hx with (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) <;> simp only [Prod.mk.injEq] at hxy
      · exact Bool.noConfusion (finCons_inj hxy.2).1
      · exact Bool.noConfusion (finCons_inj hxy.1).1

/-- Number of covering pairs of length `n` with `|B| + |Z| = t`. -/
def pairCount (n t : Nat) : Nat :=
  (pairVecs n).countP fun bz => countTrue bz.1 + countTrue bz.2 == t

theorem pairCount_lower : ∀ (n r : Nat), choose n r * 2 ^ (n - r) ≤ pairCount n (n + r)
  | 0, 0 => by decide
  | 0, r + 1 => by rw [choose_zero_succ, Nat.zero_mul]; exact Nat.zero_le _
  | n + 1, r => by
    have hsplit : pairCount (n + 1) (n + 1 + r) =
        pairCount n (n + r) + pairCount n (n + r) +
        (pairVecs n).countP (fun bz => countTrue bz.1 + countTrue bz.2 + 1 == n + r) := by
      simp only [pairCount, pairVecs, List.countP_append, List.countP_map]
      congr 1; congr 1
      · apply countP_congr_mem; intro bz _
        simp only [Function.comp, countTrue_finCons, ↓reduceIte, Bool.false_eq_true]
        apply beq_congr; omega
      · apply countP_congr_mem; intro bz _
        simp only [Function.comp, countTrue_finCons, ↓reduceIte, Bool.false_eq_true]
        apply beq_congr; omega
      · apply countP_congr_mem; intro bz _
        simp only [Function.comp, countTrue_finCons, ↓reduceIte, Bool.false_eq_true]
        apply beq_congr; omega
    rw [hsplit]
    cases r with
    | zero =>
      have ih := pairCount_lower n 0
      simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero, Nat.add_zero] at ih ⊢
      rw [Nat.pow_succ]; omega
    | succ r =>
      have ih1 := pairCount_lower n r
      have ih2 := pairCount_lower n (r + 1)
      have h3 : (pairVecs n).countP (fun bz => countTrue bz.1 + countTrue bz.2 + 1 == n + (r + 1)) =
          pairCount n (n + r) := by
        apply countP_congr_mem; intro bz _; apply beq_congr; omega
      rw [h3, show n + (r + 1) = n + r + 1 by omega] at *
      rw [choose_succ_succ, show n + 1 - (r + 1) = n - r by omega, Nat.add_mul]
      have h4 : choose n (r + 1) * 2 ^ (n - r) ≤ 2 * (choose n (r + 1) * 2 ^ (n - (r + 1))) := by
        by_cases hr : r < n
        · rw [show n - r = (n - (r + 1)) + 1 by omega, Nat.pow_succ]
          simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.le_refl]
        · rw [choose_eq_zero_of_lt (by omega), Nat.zero_mul]; exact Nat.zero_le _
      omega

/-! ## Weighted sums (generating functions) -/

theorem sumList_listProd_mul {α β : Type} (L₁ : List α) (L₂ : List β) (f : α → Nat) (g : β → Nat) :
    sumList (listProd L₁ L₂) (fun t => f t.1 * g t.2) = sumList L₁ f * sumList L₂ g := by
  induction L₁ with
  | nil => simp [listProd, sumList]
  | cons a t ih =>
    simp only [listProd, List.flatMap_cons, sumList_append, sumList_map, sumList_cons] at ih ⊢
    rw [ih, sumList_mul_left, Nat.add_mul]

theorem countP_mul_le_sumList {α : Type} (L : List α) (p : α → Bool) (c : Nat) (f : α → Nat)
    (h : ∀ x ∈ L, p x = true → c ≤ f x) : L.countP p * c ≤ sumList L f := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.countP_cons, sumList_cons]
    cases hp : p a
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
    · simp only [↓reduceIte]
      have := h a (List.mem_cons_self a t) hp
      rw [Nat.add_mul, Nat.one_mul]; omega

theorem wsum_boolVecs (α β : Nat) : ∀ (n : Nat),
    sumList (allBoolVecs n) (fun F => α ^ countTrue F * β ^ (n - countTrue F)) = (α + β) ^ n
  | 0 => by simp [allBoolVecs, sumList, countTrue]
  | n + 1 => by
    simp only [allBoolVecs, sumList_append, sumList_map, countTrue_finCons, ↓reduceIte,
      Bool.false_eq_true, Nat.zero_add]
    have h1 : sumList (allBoolVecs n)
        (fun F => α ^ countTrue F * β ^ (n + 1 - countTrue F)) =
        sumList (allBoolVecs n) (fun F => α ^ countTrue F * β ^ (n - countTrue F)) * β := by
      rw [← sumList_mul_right]; apply sumList_congr; intro F _
      have := countTrue_le F
      rw [show n + 1 - countTrue F = (n - countTrue F) + 1 by omega, Nat.pow_succ, Nat.mul_assoc]
    have h2 : sumList (allBoolVecs n)
        (fun F => α ^ (1 + countTrue F) * β ^ (n + 1 - (1 + countTrue F))) =
        sumList (allBoolVecs n) (fun F => α ^ countTrue F * β ^ (n - countTrue F)) * α := by
      rw [← sumList_mul_right]; apply sumList_congr; intro F _
      rw [show n + 1 - (1 + countTrue F) = n - countTrue F by omega, Nat.add_comm 1, Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [h1, h2, wsum_boolVecs α β n, Nat.pow_succ, Nat.mul_add, Nat.add_comm (_ * β)]

theorem pairVecs_le {n : Nat} (bz : (Fin n → Bool) × (Fin n → Bool)) :
    countTrue bz.1 + countTrue bz.2 ≤ 2 * n := by
  have := countTrue_le bz.1; have := countTrue_le bz.2; omega

theorem wsum_pairVecs (α β : Nat) : ∀ (n : Nat),
    sumList (pairVecs n) (fun bz => α ^ (countTrue bz.1 + countTrue bz.2) *
      β ^ (2 * n - (countTrue bz.1 + countTrue bz.2))) = (α * (α + 2 * β)) ^ n
  | 0 => by simp [pairVecs, sumList, countTrue]
  | n + 1 => by
    simp only [pairVecs, sumList_append, sumList_map, countTrue_finCons, ↓reduceIte,
      Bool.false_eq_true, Nat.zero_add]
    let S := sumList (pairVecs n) (fun bz => α ^ (countTrue bz.1 + countTrue bz.2) *
      β ^ (2 * n - (countTrue bz.1 + countTrue bz.2)))
    have h1 : sumList (pairVecs n) (fun bz => α ^ (1 + countTrue bz.1 + countTrue bz.2) *
        β ^ (2 * (n + 1) - (1 + countTrue bz.1 + countTrue bz.2))) = S * (α * β) := by
      rw [← sumList_mul_right]; apply sumList_congr; intro bz _
      have := pairVecs_le bz
      rw [show 2 * (n + 1) - (1 + countTrue bz.1 + countTrue bz.2) =
          (2 * n - (countTrue bz.1 + countTrue bz.2)) + 1 by omega,
        show 1 + countTrue bz.1 + countTrue bz.2 = (countTrue bz.1 + countTrue bz.2) + 1 by omega,
        Nat.pow_succ, Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h2 : sumList (pairVecs n) (fun bz => α ^ (countTrue bz.1 + (1 + countTrue bz.2)) *
        β ^ (2 * (n + 1) - (countTrue bz.1 + (1 + countTrue bz.2)))) = S * (α * β) := by
      rw [← h1]; apply sumList_congr; intro bz _
      rw [show countTrue bz.1 + (1 + countTrue bz.2) = 1 + countTrue bz.1 + countTrue bz.2 by omega]
    have h3 : sumList (pairVecs n) (fun bz => α ^ (1 + countTrue bz.1 + (1 + countTrue bz.2)) *
        β ^ (2 * (n + 1) - (1 + countTrue bz.1 + (1 + countTrue bz.2)))) = S * (α * α) := by
      rw [← sumList_mul_right]; apply sumList_congr; intro bz _
      have := pairVecs_le bz
      rw [show 2 * (n + 1) - (1 + countTrue bz.1 + (1 + countTrue bz.2)) =
          2 * n - (countTrue bz.1 + countTrue bz.2) by omega,
        show 1 + countTrue bz.1 + (1 + countTrue bz.2) = (countTrue bz.1 + countTrue bz.2) + 1 + 1
          by omega, Nat.pow_succ, Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hS : S = (α * (α + 2 * β)) ^ n := wsum_pairVecs α β n
    rw [h1, h2, h3, hS, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_mul, Nat.two_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega

/-! ## Splitting vectors -/

theorem countTrue_split {a b : Nat} (g : Fin (a + b) → Bool) :
    countTrue g = countTrue (finLeft g) + countTrue (finRight g) := by
  rw [← countTrue_finAppend, finAppend_left_right]

theorem eq_of_left_right {a b : Nat} {g h : Fin (a + b) → Bool}
    (h1 : finLeft g = finLeft h) (h2 : finRight g = finRight h) : g = h := by
  rw [← finAppend_left_right g, ← finAppend_left_right h, h1, h2]

theorem finAppend_inj {a b : Nat} {f₁ f₂ : Fin a → Bool} {g₁ g₂ : Fin b → Bool}
    (h : finAppend f₁ g₁ = finAppend f₂ g₂) : f₁ = f₂ ∧ g₁ = g₂ := by
  constructor
  · have := congrArg finLeft h; rwa [finAppend_left, finAppend_left] at this
  · have := congrArg finRight h; rwa [finAppend_right, finAppend_right] at this

end FamAux

open FamAux

/-- Number of pairs `(F, (B, Z))` with `F` arbitrary, `(B, Z)` covering (`B ∨ Z` pointwise, length `mq`),
    and `|F| + |B| + |Z| = s`.  (These are exactly the valid all-`A` configurations, with the `A`-part
    — always of size `mp` — dropped.) -/
def fam2Count (m p q : Nat) (_hm : 0 < m) (s : Nat) : Nat :=
  (listProd (allBoolVecs (numFree m p q)) (pairVecs (m * q))).countP
    fun t => countTrue t.1 + (countTrue t.2.1 + countTrue t.2.2) == s

/-- Chernoff-type bound for the all-`A` family:
    `[x^s] (1+x)^C (x(2+x))^Q` evaluated with weights `α^s β^(C+2Q-s)`. -/
theorem fam2_chernoff (m p q : Nat) (hm : 0 < m) (s α β : Nat)
    (hs : s ≤ numFree m p q + 2 * (m * q)) :
    fam2Count m p q hm s * (α ^ s * β ^ (numFree m p q + 2 * (m * q) - s)) ≤
      (α + β) ^ numFree m p q * (α * (α + 2 * β)) ^ (m * q) := by
  rw [← wsum_boolVecs, ← wsum_pairVecs, ← sumList_listProd_mul]
  unfold fam2Count
  apply countP_mul_le_sumList
  intro t _ ht
  have hw : countTrue t.1 + (countTrue t.2.1 + countTrue t.2.2) = s := by simpa using ht
  have h1 := countTrue_le t.1
  have h2 := pairVecs_le t.2
  have hb : β ^ (numFree m p q + 2 * (m * q) - s) =
      β ^ (numFree m p q - countTrue t.1) * β ^ (2 * (m * q) - (countTrue t.2.1 + countTrue t.2.2)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have ha : α ^ s = α ^ countTrue t.1 * α ^ (countTrue t.2.1 + countTrue t.2.2) := by
    rw [← Nat.pow_add, hw]
  rw [ha, hb]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.le_refl]


/-- Peak 1 (all `B` chosen): `C(N₁, ⌊N₁/2⌋) ≤ d_t(k₁)` with `N₁ = C + mp + mq`, `k₁ = 1 + mq + ⌊N₁/2⌋`. -/
theorem lb_peak1 (m p q : Nat) (hm : 0 < m) :
    choose (numFree m p q + m * p + m * q) ((numFree m p q + m * p + m * q) / 2) ≤
      cfgCount m p q hm (1 + m * q + (numFree m p q + m * p + m * q) / 2) := by
  rw [← countP_allBoolVecs_card]
  unfold cfgCount
  apply countP_le_of_inj (allBoolVecs_nodup _) _ _
    (fun g => (finLeft (finLeft g), fun i => (⟨toBlocks (finRight (finLeft g)) i, fun _ => true,
      toBlocks (finRight g) i⟩ : Blk p q)))
  · intro g _ hg
    refine ⟨mem_prod_cfgs _ _, ?_⟩
    have hgw : countTrue g = (numFree m p q + m * p + m * q) / 2 := by simpa using hg
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨(cfgValid_iff hm _).mpr (fun i b => by simp), ?_⟩
    rw [cfgSize_eq]
    dsimp only
    rw [countTrue_toBlocks_sum, countTrue_toBlocks_sum, countTrue_const_true, sum_const_finRange]
    rw [countTrue_split g, countTrue_split (finLeft g)] at hgw
    omega
  · intro g₁ _ _ g₂ _ _ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨hF, hx⟩
    have hA : toBlocks (finRight (finLeft g₁)) = toBlocks (finRight (finLeft g₂)) := by
      funext i; exact congrArg Blk.A (congrFun hx i)
    have hZ : toBlocks (finRight g₁) = toBlocks (finRight g₂) := by
      funext i; exact congrArg Blk.Z (congrFun hx i)
    exact eq_of_left_right (eq_of_left_right hF (toBlocks_inj hA)) (toBlocks_inj hZ)

/-- Peak 2 (all `A` chosen): `C(C, ⌊C/2⌋) · C(Q, ⌊Q/3⌋) · 2^(Q - ⌊Q/3⌋) ≤ d_t(k₃)`. -/
theorem lb_peak3 (m p q : Nat) (hm : 0 < m) :
    choose (numFree m p q) (numFree m p q / 2) *
        (choose (m * q) (m * q / 3) * 2 ^ (m * q - m * q / 3)) ≤
      cfgCount m p q hm (1 + m * p + m * q + numFree m p q / 2 + m * q / 3) := by
  refine Nat.le_trans (Nat.mul_le_mul_left _ (pairCount_lower (m * q) (m * q / 3))) ?_
  rw [← countP_allBoolVecs_card, pairCount, ← countP_listProd_mul]
  unfold cfgCount
  apply countP_le_of_inj (listProd_nodup (allBoolVecs_nodup _) (pairVecs_nodup _)) _ _
    (fun t => (t.1, fun i => (⟨fun _ => true, toBlocks t.2.1 i, toBlocks t.2.2 i⟩ : Blk p q)))
  · rintro ⟨F, B, Z⟩ hmem ht
    refine ⟨mem_prod_cfgs _ _, ?_⟩
    have hBZ := (mem_pairVecs B Z).mp (mem_listProd.mp hmem).2
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨(cfgValid_iff hm _).mpr (fun i b => ⟨hBZ _, by simp [allTrue_const_true]⟩), ?_⟩
    rw [cfgSize_eq]
    dsimp only
    rw [countTrue_toBlocks_sum, countTrue_toBlocks_sum, countTrue_const_true, sum_const_finRange]
    omega
  · rintro ⟨F₁, B₁, Z₁⟩ _ _ ⟨F₂, B₂, Z₂⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨hF, hx⟩
    have hB : toBlocks B₁ = toBlocks B₂ := by
      funext i; exact congrArg Blk.B (congrFun hx i)
    have hZ : toBlocks Z₁ = toBlocks Z₂ := by
      funext i; exact congrArg Blk.Z (congrFun hx i)
    rw [hF, toBlocks_inj hB, toBlocks_inj hZ]

/-- Valley decomposition: every valid configuration is all-`B`, all-`A`, or mixed. -/
theorem ub_valley (m p q : Nat) (hm : 0 < m) (k : Nat) (hk : 1 + m * p + m * q ≤ k) :
    cfgCount m p q hm k ≤
      choose (numFree m p q + m * p + m * q) (k - 1 - m * q) +
      fam2Count m p q hm (k - 1 - m * p) +
      2 ^ numFree m p q * mixedCount m p q hm := by
  unfold cfgCount
  let L := listProd (allBoolVecs (numFree m p q)) (allFuns (allBlks p q) m)
  let q1 : (Fin (numFree m p q) → Bool) × (Fin m → Blk p q) → Bool := fun Fx =>
    cfgValid hm Fx.2 && allBOnes Fx.2 && (1 + countTrue Fx.1 + cfgSize Fx.2 == k)
  let q2 : (Fin (numFree m p q) → Bool) × (Fin m → Blk p q) → Bool := fun Fx =>
    cfgValid hm Fx.2 && allAOnes Fx.2 && (1 + countTrue Fx.1 + cfgSize Fx.2 == k)
  let q3 : (Fin (numFree m p q) → Bool) × (Fin m → Blk p q) → Bool := fun Fx =>
    (fun _ => true) Fx.1 && (fun x => cfgValid hm x && !allBOnes x && !allAOnes x) Fx.2
  have step1 := countP_le_add_of_imp L
    (fun Fx => cfgValid hm Fx.2 && (1 + countTrue Fx.1 + cfgSize Fx.2 == k)) q1
    (fun Fx => q2 Fx || q3 Fx) (by
      intro Fx _ h
      simp only [q1, q2, q3, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
      cases hb : allBOnes Fx.2 <;> cases ha : allAOnes Fx.2 <;> simp_all)
  have step2 := countP_le_add_of_imp L (fun Fx => q2 Fx || q3 Fx) q2 q3 (by
      intro Fx _ h; simpa [Bool.or_eq_true] using h)
  have b3 : L.countP q3 = 2 ^ numFree m p q * mixedCount m p q hm := by
    have h := countP_listProd_mul (allBoolVecs (numFree m p q)) (allFuns (allBlks p q) m)
      (fun _ => true) (fun x => cfgValid hm x && !allBOnes x && !allAOnes x)
    rw [List.countP_true, allBoolVecs_length] at h
    exact h
  have b1 : L.countP q1 ≤ choose (numFree m p q + m * p + m * q) (k - 1 - m * q) := by
    rw [← countP_allBoolVecs_card]
    apply countP_le_of_inj (prod_cfgs_nodup _ _ _ _) _ _
      (fun Fx => finAppend (finAppend Fx.1 (fromBlocks fun i => (Fx.2 i).A))
        (fromBlocks fun i => (Fx.2 i).Z))
    · rintro ⟨F, x⟩ _ h
      refine ⟨mem_allBoolVecs _, ?_⟩
      simp only [q1, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨_, hB⟩, hs⟩
      have hB' := (allBOnes_iff x).mp hB
      simp only [beq_iff_eq]
      rw [countTrue_finAppend, countTrue_finAppend, countTrue_fromBlocks, countTrue_fromBlocks]
      rw [cfgSize_eq] at hs
      have hBs : sumList (finRange m) (fun i => countTrue (x i).B) = m * q := by
        rw [← sum_const_finRange]
        exact sumList_congr _ _ _ (fun i _ => countTrue_of_all _ (hB' i))
      omega
    · rintro ⟨F₁, x₁⟩ _ h₁ ⟨F₂, x₂⟩ _ h₂ h
      simp only [q1, Bool.and_eq_true] at h₁ h₂
      have hB₁ := (allBOnes_iff x₁).mp h₁.1.2
      have hB₂ := (allBOnes_iff x₂).mp h₂.1.2
      rcases finAppend_inj h with ⟨h12, hZ⟩
      rcases finAppend_inj h12 with ⟨hF, hA⟩
      have hA' := fromBlocks_inj hA
      have hZ' := fromBlocks_inj hZ
      refine Prod.ext hF (funext fun i => blk_ext (congrFun hA' i) ?_ (congrFun hZ' i))
      funext b; rw [hB₁ i b, hB₂ i b]
  have b2 : L.countP q2 ≤ fam2Count m p q hm (k - 1 - m * p) := by
    unfold fam2Count
    apply countP_le_of_inj (prod_cfgs_nodup _ _ _ _) _ _
      (fun Fx => (Fx.1, (fromBlocks fun i => (Fx.2 i).B, fromBlocks fun i => (Fx.2 i).Z)))
    · rintro ⟨F, x⟩ _ h
      simp only [q2, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨hv, hA⟩, hs⟩
      have hA' := (allAOnes_iff x).mp hA
      have hv' := (cfgValid_iff hm x).mp hv
      refine ⟨mem_listProd.mpr ⟨mem_allBoolVecs _, (mem_pairVecs _ _).mpr (fun j => ?_)⟩, ?_⟩
      · simp only [fromBlocks]; exact (hv' _ _).1
      · simp only [beq_iff_eq]
        rw [countTrue_fromBlocks, countTrue_fromBlocks]
        rw [cfgSize_eq] at hs
        have hAs : sumList (finRange m) (fun i => countTrue (x i).A) = m * p := by
          rw [← sum_const_finRange]
          exact sumList_congr _ _ _ (fun i _ => countTrue_of_all _ (hA' i))
        omega
    · rintro ⟨F₁, x₁⟩ _ h₁ ⟨F₂, x₂⟩ _ h₂ h
      simp only [q2, Bool.and_eq_true] at h₁ h₂
      have hA₁ := (allAOnes_iff x₁).mp h₁.1.2
      have hA₂ := (allAOnes_iff x₂).mp h₂.1.2
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨hF, hB, hZ⟩
      have hB' := fromBlocks_inj hB
      have hZ' := fromBlocks_inj hZ
      refine Prod.ext hF (funext fun i => blk_ext ?_ (congrFun hB' i) (congrFun hZ' i))
      funext a; rw [hA₁ i a, hA₂ i a]
  have : L.countP (fun Fx => cfgValid hm Fx.2 && (1 + countTrue Fx.1 + cfgSize Fx.2 == k)) ≤
      L.countP q1 + L.countP q2 + L.countP q3 := by omega
  rw [b3] at this
  show L.countP (fun Fx => cfgValid hm Fx.2 && (1 + countTrue Fx.1 + cfgSize Fx.2 == k)) ≤ _
  omega

end AlikhaniJafariDisproof


/-! # Mixed configurations: a transfer-matrix (Peierls) bound

OWNER: Mixed agent. Exported theorem statement below is FROZEN. -/

namespace AlikhaniJafariDisproof

namespace MixAux

/-! ### Generic list / `allFuns` counting -/

theorem countP_flatMap' {α β : Type} (L : List α) (g : α → List β) (P : β → Bool) :
    (L.flatMap g).countP P = sumList L (fun a => (g a).countP P) := by
  induction L with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, List.countP_append, sumList_cons, ih]

theorem countP_allFuns_succ {α : Type} (L : List α) (n : Nat) (P : (Fin (n + 1) → α) → Bool) :
    (allFuns L (n + 1)).countP P =
      sumList L (fun a => (allFuns L n).countP (fun f => P (finConsG a f))) := by
  show (L.flatMap fun a => (allFuns L n).map (finConsG a)).countP P = _
  rw [countP_flatMap']
  apply sumList_congr
  intro a _
  rw [List.countP_map]
  rfl

theorem countP_allFuns_true {α : Type} (L : List α) :
    ∀ n, (allFuns L n).countP (fun _ => true) = L.length ^ n
  | 0 => rfl
  | n + 1 => by
    rw [countP_allFuns_succ, sumList_congr L _ (fun _ => L.length ^ n)
      (fun a _ => countP_allFuns_true L n), sumList_const, Nat.pow_succ, Nat.mul_comm]

theorem finConsG_zero {α : Type} {n : Nat} (a : α) (f : Fin n → α) :
    finConsG a f ⟨0, Nat.zero_lt_succ n⟩ = a := by
  simp [finConsG]

theorem finConsG_succ {α : Type} {n : Nat} (a : α) (f : Fin n → α) (j : Fin n) :
    finConsG a f j.succ = f j := by
  simp [finConsG, Fin.succ]

theorem countP_const_and {α : Type} (L : List α) (K : Bool) (Q : α → Bool) :
    L.countP (fun x => K && Q x) = if K then L.countP Q else 0 := by
  cases K <;> simp

theorem sumList_ite {α : Type} (L : List α) (K : α → Bool) (c : Nat) :
    sumList L (fun a => if K a then c else 0) = L.countP K * c := by
  induction L with
  | nil => simp [sumList]
  | cons a t ih =>
    rw [sumList_cons, ih, List.countP_cons]
    cases K a <;> simp [Nat.add_mul] <;> omega

theorem le_length_of_inj {α β : Type} [DecidableEq β] {L₁ : List α} {L₂ : List β}
    (h1 : L₁.Nodup) (P : α → Bool) (f : α → β)
    (hf : ∀ x ∈ L₁, P x = true → f x ∈ L₂)
    (hinj : ∀ x ∈ L₁, P x = true → ∀ y ∈ L₁, P y = true → f x = f y → x = y) :
    L₁.countP P ≤ L₂.length := by
  have := countP_le_of_inj h1 P (fun _ => true) f (fun x hx hp => ⟨hf x hx hp, rfl⟩) hinj
  rwa [List.countP_true] at this

theorem listProd_length {α β : Type} (L₁ : List α) (L₂ : List β) :
    (listProd L₁ L₂).length = L₁.length * L₂.length := by
  have := countP_listProd_mul L₁ L₂ (fun _ => true) (fun _ => true)
  simp only [Bool.and_self, List.countP_true] at this
  exact this

theorem allTrue_iff {n : Nat} (f : Fin n → Bool) : allTrue f = true ↔ ∀ i, f i = true := by
  simp only [allTrue, List.all_eq_true]
  exact ⟨fun h i => h i (mem_finRange i), fun h i _ => h i⟩

theorem allTrue_eq {n : Nat} {f g : Fin n → Bool} (hf : allTrue f = true) (hg : allTrue g = true) :
    f = g := by
  funext i
  rw [(allTrue_iff f).1 hf i, (allTrue_iff g).1 hg i]

theorem exists_false_of_allTrue_false {n : Nat} {f : Fin n → Bool} (h : allTrue f = false) :
    ∃ i, f i = false := by
  apply Classical.byContradiction
  intro hne
  have : allTrue f = true := (allTrue_iff f).2 (fun i => by
    cases hf : f i
    · exact absurd ⟨i, hf⟩ hne
    · rfl)
  rw [h] at this
  cases this

/-! ### Block types and local constraints -/

variable {p q : Nat}

theorem blk_ext {a b : Blk p q} (hA : a.A = b.A) (hB : a.B = b.B) (hZ : a.Z = b.Z) : a = b := by
  cases a; cases b; simp only at hA hB hZ; subst hA hB hZ; rfl

/-- Type of a block: `true` iff its `B`-row is not all true. -/
def ty (β : Blk p q) : Bool := !allTrue β.B
/-- `B ∨ Z` pointwise. -/
def bz (β : Blk p q) : Bool := allTrue fun b => β.B b || β.Z b
/-- Local constraint of a block given the type of its successor. -/
def okT (β : Blk p q) (t' : Bool) : Bool :=
  (!ty β || (allTrue β.A && bz β)) && (!t' || allTrue β.A)
def ok (β β' : Blk p q) : Bool := okT β (ty β')
/-- End-of-path condition (`S(false,true)`). -/
def endB (β : Blk p q) : Bool := allTrue β.A && allTrue β.B

theorem ty_false {β : Blk p q} (h : ty β = false) : allTrue β.B = true := by
  simpa [ty] using h

theorem okT_true {β : Blk p q} (h : okT β true = true) : allTrue β.A = true := by
  revert h; cases h1 : allTrue β.A <;> simp [okT, h1]

theorem okT_ty {β : Blk p q} {t' : Bool} (hty : ty β = true) (h : okT β t' = true) :
    allTrue β.A = true ∧ bz β = true := by
  revert h; simp only [okT, hty]
  cases h1 : allTrue β.A <;> cases h2 : bz β <;> simp

/-- Path condition on `n + 1` blocks: consecutive `ok`, last block in `S(false,true)`. -/
def pathOK : (n : Nat) → (Fin (n + 1) → Blk p q) → Bool
  | 0, y => endB (y ⟨0, Nat.zero_lt_succ 0⟩)
  | n + 1, y => ok (y ⟨0, by omega⟩) (y ⟨1, by omega⟩) && pathOK n (fun j => y j.succ)

theorem pathOK_cons (n : Nat) (a : Blk p q) (f : Fin (n + 1) → Blk p q) :
    pathOK (n + 1) (finConsG a f) = (ok a (f ⟨0, Nat.zero_lt_succ n⟩) && pathOK n f) := by
  have h1 : (fun j : Fin (n + 1) => finConsG a f j.succ) = f := funext (finConsG_succ a f)
  have h2 : finConsG a f ⟨1, by omega⟩ = f ⟨0, Nat.zero_lt_succ n⟩ :=
    finConsG_succ a f ⟨0, Nat.zero_lt_succ n⟩
  show (ok (finConsG a f ⟨0, _⟩) (finConsG a f ⟨1, _⟩) &&
    pathOK n (fun j => finConsG a f j.succ)) = _
  rw [h1, h2, finConsG_zero]

theorem pathOK_of : ∀ (n : Nat) (y : Fin (n + 1) → Blk p q),
    (∀ j (h : j < n), ok (y ⟨j, by omega⟩) (y ⟨j + 1, by omega⟩) = true) →
    endB (y ⟨n, by omega⟩) = true → pathOK n y = true
  | 0, y, _, he => he
  | n + 1, y, hs, he => by
    show (ok (y ⟨0, _⟩) (y ⟨1, _⟩) && pathOK n (fun j => y j.succ)) = true
    rw [Bool.and_eq_true]
    exact ⟨hs 0 (by omega), pathOK_of n _ (fun j h => hs (j + 1) (by omega)) he⟩

/-! ### Transfer-matrix counts -/

/-- Number of paths of `n + 1` blocks whose first block has type `t`. -/
def gc (p q n : Nat) (t : Bool) : Nat :=
  (allFuns (allBlks p q) (n + 1)).countP fun y =>
    (ty (y ⟨0, Nat.zero_lt_succ n⟩) == t) && pathOK n y

/-- `|S(t, t')|`. -/
def Nc (p q : Nat) (t t' : Bool) : Nat :=
  (allBlks p q).countP fun a => (ty a == t) && okT a t'

theorem gc_succ (n : Nat) (t : Bool) :
    gc p q (n + 1) t = Nc p q t true * gc p q n true + Nc p q t false * gc p q n false := by
  have key : ∀ a : Blk p q, (allFuns (allBlks p q) (n + 1)).countP
      (fun f => (ty (finConsG a f ⟨0, Nat.zero_lt_succ (n + 1)⟩) == t) &&
        pathOK (n + 1) (finConsG a f)) =
      (if (ty a == t) && okT a true then gc p q n true else 0) +
      (if (ty a == t) && okT a false then gc p q n false else 0) := by
    intro a
    rw [countP_split _ _ (fun f => ty (f ⟨0, Nat.zero_lt_succ n⟩))]
    have e1 : (allFuns (allBlks p q) (n + 1)).countP
        (fun f => ((ty (finConsG a f ⟨0, Nat.zero_lt_succ (n + 1)⟩) == t) &&
          pathOK (n + 1) (finConsG a f)) && ty (f ⟨0, Nat.zero_lt_succ n⟩)) =
        (allFuns (allBlks p q) (n + 1)).countP
        (fun f => ((ty a == t) && okT a true) &&
          ((ty (f ⟨0, Nat.zero_lt_succ n⟩) == true) && pathOK n f)) := by
      apply countP_congr_mem
      intro f _
      rw [finConsG_zero, pathOK_cons]
      unfold ok
      cases h : ty (f ⟨0, Nat.zero_lt_succ n⟩) <;> simp [Bool.and_assoc]
    have e2 : (allFuns (allBlks p q) (n + 1)).countP
        (fun f => ((ty (finConsG a f ⟨0, Nat.zero_lt_succ (n + 1)⟩) == t) &&
          pathOK (n + 1) (finConsG a f)) && !ty (f ⟨0, Nat.zero_lt_succ n⟩)) =
        (allFuns (allBlks p q) (n + 1)).countP
        (fun f => ((ty a == t) && okT a false) &&
          ((ty (f ⟨0, Nat.zero_lt_succ n⟩) == false) && pathOK n f)) := by
      apply countP_congr_mem
      intro f _
      rw [finConsG_zero, pathOK_cons]
      unfold ok
      cases h : ty (f ⟨0, Nat.zero_lt_succ n⟩) <;> simp [Bool.and_assoc]
    rw [e1, e2, countP_const_and, countP_const_and]
    rfl
  show (allFuns (allBlks p q) (n + 1 + 1)).countP _ = _
  rw [countP_allFuns_succ, sumList_congr _ _ _ (fun a _ => key a), sumList_add,
    sumList_ite, sumList_ite]
  rfl

theorem Nc_ff : Nc p q false false ≤ 2 ^ (p + q) := by
  unfold Nc
  have := le_length_of_inj (allBlks_nodup p q) (fun a => (ty a == false) && okT a false)
    (fun a : Blk p q => (a.A, a.Z))
    (L₂ := listProd (allBoolVecs p) (allBoolVecs q))
    (fun a _ _ => mem_listProd.mpr ⟨mem_allBoolVecs _, mem_allBoolVecs _⟩)
    (fun a _ ha b _ hb hab => by
      simp only [Bool.and_eq_true, beq_iff_eq] at ha hb
      have h1 := Prod.mk.inj hab
      exact blk_ext h1.1 (allTrue_eq (ty_false ha.1) (ty_false hb.1)) h1.2)
  rwa [listProd_length, allBoolVecs_length, allBoolVecs_length, ← Nat.pow_add] at this

theorem Nc_ft : Nc p q false true ≤ 2 ^ q := by
  unfold Nc
  have := le_length_of_inj (allBlks_nodup p q) (fun a => (ty a == false) && okT a true)
    (fun a : Blk p q => a.Z)
    (L₂ := allBoolVecs q)
    (fun a _ _ => mem_allBoolVecs _)
    (fun a _ ha b _ hb hab => by
      simp only [Bool.and_eq_true, beq_iff_eq] at ha hb
      exact blk_ext (allTrue_eq (okT_true ha.2) (okT_true hb.2))
        (allTrue_eq (ty_false ha.1) (ty_false hb.1)) hab)
  rwa [allBoolVecs_length] at this

/-- The three admissible `(B, Z)` values at a coordinate when `B ∨ Z`. -/
def trip : List (Bool × Bool) := [(true, false), (false, true), (true, true)]

theorem Nc_t (t' : Bool) : Nc p q true t' ≤ 3 ^ q := by
  unfold Nc
  have := le_length_of_inj (allBlks_nodup p q) (fun a => (ty a == true) && okT a t')
    (fun a : Blk p q => fun b : Fin q => (a.B b, a.Z b))
    (L₂ := allFuns trip q)
    (fun a _ ha => by
      simp only [Bool.and_eq_true, beq_iff_eq] at ha
      have hbz := (allTrue_iff _).1 (okT_ty ha.1 ha.2).2
      apply mem_allFuns
      intro b
      have hb := hbz b
      revert hb
      cases h1 : a.B b <;> cases h2 : a.Z b <;> simp [trip, h1, h2])
    (fun a _ ha b _ hb hab => by
      simp only [Bool.and_eq_true, beq_iff_eq] at ha hb
      refine blk_ext (allTrue_eq (okT_ty ha.1 ha.2).1 (okT_ty hb.1 hb.2).1) ?_ ?_
      · funext i; exact (Prod.mk.inj (congrFun hab i)).1
      · funext i; exact (Prod.mk.inj (congrFun hab i)).2)
  rwa [← List.countP_true, countP_allFuns_true] at this

theorem gc_zero (t : Bool) : gc p q 0 t ≤ 2 ^ q := by
  unfold gc
  have := le_length_of_inj (allFuns_nodup (allBlks_nodup p q) 1)
    (fun y => (ty (y ⟨0, Nat.zero_lt_succ 0⟩) == t) && pathOK 0 y)
    (fun y : Fin 1 → Blk p q => (y ⟨0, by omega⟩).Z)
    (L₂ := allBoolVecs q)
    (fun _ _ _ => mem_allBoolVecs _)
    (fun y _ hy y' _ hy' hyy => by
      simp only [Bool.and_eq_true] at hy hy'
      have e : endB (y ⟨0, by omega⟩) = true := hy.2
      have e' : endB (y' ⟨0, by omega⟩) = true := hy'.2
      simp only [endB, Bool.and_eq_true] at e e'
      have h0 : y ⟨0, by omega⟩ = y' ⟨0, by omega⟩ :=
        blk_ext (allTrue_eq e.1 e'.1) (allTrue_eq e.2 e'.2) hyy
      funext i
      have hi : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      rw [hi]; exact h0)
  rwa [allBoolVecs_length] at this

theorem arith (a b c d X L Ln K1 K2 : Nat) (ha : a ≤ K1) (hb : b ≤ K2)
    (hc : c * Ln ≤ X * L) (hd : d * Ln ≤ X) :
    (a * c + b * d) * (Ln * L) ≤ X * ((K1 * L + K2) * L) := by
  have e1 : (a * c + b * d) * (Ln * L) = (a * (c * Ln) + b * (d * Ln)) * L := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have e2 : X * ((K1 * L + K2) * L) = (K1 * (X * L) + K2 * X) * L := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [e1, e2]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.mul_le_mul ha hc) (Nat.mul_le_mul hb hd))

theorem gc_bound (L Λ : Nat) (hL : 1 ≤ L)
    (h0 : (2 ^ (p + q) + 2 ^ q * L) * L ≤ Λ) (h1 : 3 ^ q * (L + 1) ≤ Λ) :
    ∀ n, gc p q n false * L ^ n ≤ 2 ^ q * Λ ^ n ∧ gc p q n true * L ^ n ≤ 2 ^ q * Λ ^ n * L
  | 0 => by
    simp only [Nat.pow_zero, Nat.mul_one]
    exact ⟨gc_zero false, Nat.le_trans (gc_zero true) (Nat.le_mul_of_pos_right _ hL)⟩
  | n + 1 => by
    obtain ⟨ihF, ihT⟩ := gc_bound L Λ hL h0 h1 n
    rw [gc_succ, gc_succ, Nat.pow_succ, Nat.pow_succ]
    constructor
    · have := arith _ _ _ _ (2 ^ q * Λ ^ n) L (L ^ n) (2 ^ q) (2 ^ (p + q)) (Nc_ft (p := p)) Nc_ff ihT ihF
      refine Nat.le_trans this ?_
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      have : (2 ^ q * L + 2 ^ (p + q)) * L = (2 ^ (p + q) + 2 ^ q * L) * L := by
        rw [Nat.add_comm]
      rw [this]; exact Nat.mul_le_mul_left _ h0
    · have := arith _ _ _ _ (2 ^ q * Λ ^ n) L (L ^ n) (3 ^ q) (3 ^ q) (Nc_t (p := p) true) (Nc_t (p := p) false)
        ihT ihF
      refine Nat.le_trans this ?_
      have e : 2 ^ q * (Λ ^ n * Λ) * L = 2 ^ q * Λ ^ n * (Λ * L) := by
        simp only [Nat.mul_assoc]
      rw [e]
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_right
      have : 3 ^ q * L + 3 ^ q = 3 ^ q * (L + 1) := by rw [Nat.mul_add, Nat.mul_one]
      rw [this]; exact h1

/-! ### Cyclic structure: validity ⇒ local constraints; mixed ⇒ a cut -/

/-- Cyclic successor. -/
def cs {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

theorem shiftBack_zero (m : Nat) (hm : 0 < m) (i : Fin m) :
    shiftBack m hm i ⟨0, by omega⟩ = i := by
  apply Fin.ext
  show (i.val + m - 0 % m) % m = i.val
  rw [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem shiftBack_one (m : Nat) (hm : 0 < m) (h2 : 2 ≤ m) (i : Fin m) :
    shiftBack m hm (cs hm i) ⟨1, by omega⟩ = i := by
  apply Fin.ext
  show ((i.val + 1) % m + m - 1 % m) % m = i.val
  rw [Nat.mod_eq_of_lt (show 1 < m by omega)]
  have hi := i.isLt
  by_cases h : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt h, show i.val + 1 + m - 1 = i.val + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · have he : i.val + 1 = m := by omega
    rw [he, Nat.mod_self, show 0 + m - 1 = m - 1 by omega, Nat.mod_eq_of_lt (by omega)]
    omega

theorem valid_at {m : Nat} {hm : 0 < m} {x : Fin m → Blk p q} (hv : cfgValid hm x = true)
    (i : Fin m) (b : Fin q) :
    ((x i).B b || (x i).Z b) = true ∧
      ((x i).B b = false → ∀ s : Fin 3, allTrue (x (shiftBack m hm i s)).A = true) := by
  unfold cfgValid at hv
  rw [List.all_eq_true] at hv
  have h := hv i (mem_finRange i)
  rw [List.all_eq_true] at h
  have h' := h b (mem_finRange b)
  rw [Bool.and_eq_true] at h'
  refine ⟨h'.1, fun hB s => ?_⟩
  have h2 := h'.2
  rw [hB, Bool.false_or, List.all_eq_true] at h2
  exact h2 s (mem_finRange s)

theorem valid_ok {m : Nat} {hm : 0 < m} (h2 : 2 ≤ m) {x : Fin m → Blk p q}
    (hv : cfgValid hm x = true) (i : Fin m) : ok (x i) (x (cs hm i)) = true := by
  unfold ok okT
  rw [Bool.and_eq_true]
  constructor
  · cases hty : ty (x i)
    · rfl
    · obtain ⟨b, hb⟩ := exists_false_of_allTrue_false
        (show allTrue (x i).B = false by simpa [ty] using hty)
      have hA := (valid_at hv i b).2 hb ⟨0, by omega⟩
      rw [shiftBack_zero] at hA
      have hbz : bz (x i) = true := (allTrue_iff _).2 (fun b' => (valid_at hv i b').1)
      simp [hA, hbz]
  · cases hty : ty (x (cs hm i))
    · rfl
    · obtain ⟨b, hb⟩ := exists_false_of_allTrue_false
        (show allTrue (x (cs hm i)).B = false by simpa [ty] using hty)
      have hA := (valid_at hv (cs hm i) b).2 hb ⟨1, by omega⟩
      rw [shiftBack_one m hm h2] at hA
      simp [hA]

theorem exists_cut {m : Nat} (hm : 0 < m) (x : Fin m → Blk p q)
    (hV : ∀ i, ok (x i) (x (cs hm i)) = true)
    (i0 : Fin m) (h0 : ty (x i0) = true) (i1 : Fin m) (h1 : allTrue (x i1).A = false) :
    ∃ i, ty (x i) = false ∧ ty (x (cs hm i)) = true := by
  apply Classical.byContradiction
  intro hne
  have step : ∀ i, ty (x i) = false → ty (x (cs hm i)) = false := by
    intro i hi
    cases h : ty (x (cs hm i))
    · rfl
    · exact absurd ⟨i, hi, h⟩ hne
  have hi1 : ty (x i1) = false := by
    cases h : ty (x i1)
    · rfl
    · have := okT_ty h (hV i1)
      rw [this.1] at h1; cases h1
  have hk : ∀ k, ty (x ⟨(i1.val + k) % m, Nat.mod_lt _ hm⟩) = false := by
    intro k
    induction k with
    | zero =>
      have : (⟨(i1.val + 0) % m, Nat.mod_lt _ hm⟩ : Fin m) = i1 :=
        Fin.ext (by show (i1.val + 0) % m = i1.val; rw [Nat.add_zero, Nat.mod_eq_of_lt i1.isLt])
      rw [this]; exact hi1
    | succ k ih =>
      have : (⟨(i1.val + (k + 1)) % m, Nat.mod_lt _ hm⟩ : Fin m) =
          cs hm ⟨(i1.val + k) % m, Nat.mod_lt _ hm⟩ := by
        apply Fin.ext
        show (i1.val + (k + 1)) % m = ((i1.val + k) % m + 1) % m
        rw [Nat.mod_add_mod, Nat.add_assoc]
      rw [this]; exact step _ ih
  have := hk (i0.val + m - i1.val)
  have e : (⟨(i1.val + (i0.val + m - i1.val)) % m, Nat.mod_lt _ hm⟩ : Fin m) = i0 := by
    apply Fin.ext
    show (i1.val + (i0.val + m - i1.val)) % m = i0.val
    rw [show i1.val + (i0.val + m - i1.val) = i0.val + m by have := i1.isLt; omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt i0.isLt]
  rw [e, h0] at this
  cases this

/-! ### Cutting the cycle at a fixed position -/

/-- Rotation starting right after position `i`. -/
def rotY {n : Nat} (i : Fin (n + 1)) (x : Fin (n + 1) → Blk p q) : Fin (n + 1) → Blk p q :=
  fun j => x ⟨(j.val + i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- A cut at `i`: block `i` of type `false`, block `i+1` of type `true`, all local constraints. -/
def Qc {n : Nat} (hm : 0 < n + 1) (i : Fin (n + 1)) (x : Fin (n + 1) → Blk p q) : Bool :=
  !ty (x i) && ty (x (cs hm i)) && allTrue (fun j => ok (x j) (x (cs hm j)))

theorem Qc_le (n : Nat) (hm : 0 < n + 1) (i : Fin (n + 1)) :
    (allFuns (allBlks p q) (n + 1)).countP (Qc hm i) ≤ gc p q n true := by
  unfold gc
  apply countP_le_of_inj (allFuns_nodup (allBlks_nodup p q) (n + 1)) _ _ (rotY i)
  · intro x _ hx
    refine ⟨mem_allFuns _ (fun _ => mem_allBlks _), ?_⟩
    simp only [Qc, Bool.and_eq_true, Bool.not_eq_true'] at hx
    obtain ⟨⟨hti, htc⟩, hall⟩ := hx
    have hall' := (allTrue_iff _).1 hall
    rw [Bool.and_eq_true]
    constructor
    · have e : (⟨(0 + i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) =
          cs hm i := Fin.ext (by
            show (0 + i.val + 1) % (n + 1) = (i.val + 1) % (n + 1)
            rw [Nat.zero_add])
      show (ty (x ⟨(0 + i.val + 1) % (n + 1), _⟩) == true) = true
      rw [e, htc]; rfl
    · apply pathOK_of
      · intro j hj
        have e : (⟨(j + 1 + i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) =
            cs hm ⟨(j + i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ := by
          apply Fin.ext
          show (j + 1 + i.val + 1) % (n + 1) = ((j + i.val + 1) % (n + 1) + 1) % (n + 1)
          rw [Nat.mod_add_mod, show j + i.val + 1 + 1 = j + 1 + i.val + 1 by omega]
        show ok (x ⟨(j + i.val + 1) % (n + 1), _⟩) (x ⟨(j + 1 + i.val + 1) % (n + 1), _⟩) = true
        rw [e]; exact hall' _
      · have e : (⟨(n + i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) = i := by
          apply Fin.ext
          show (n + i.val + 1) % (n + 1) = i.val
          rw [show n + i.val + 1 = i.val + (n + 1) by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt i.isLt]
        show endB (x ⟨(n + i.val + 1) % (n + 1), _⟩) = true
        rw [e]
        have hok := hall' i
        unfold ok at hok; rw [htc] at hok
        simp only [endB, Bool.and_eq_true]
        exact ⟨okT_true hok, ty_false hti⟩
  · intro x _ _ x' _ _ hxx
    funext k
    have hk := k.isLt
    have e : (⟨((k.val + (n - i.val)) % (n + 1) + i.val + 1) % (n + 1),
        Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) = k := by
      apply Fin.ext
      show ((k.val + (n - i.val)) % (n + 1) + i.val + 1) % (n + 1) = k.val
      rw [Nat.add_assoc, Nat.mod_add_mod,
        show k.val + (n - i.val) + (i.val + 1) = k.val + (n + 1) by have := i.isLt; omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hk]
    have h := congrFun hxx ⟨(k.val + (n - i.val)) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
    have h' : x ⟨((k.val + (n - i.val)) % (n + 1) + i.val + 1) % (n + 1),
        Nat.mod_lt _ (Nat.succ_pos n)⟩ =
        x' ⟨((k.val + (n - i.val)) % (n + 1) + i.val + 1) % (n + 1),
        Nat.mod_lt _ (Nat.succ_pos n)⟩ := h
    rw [e] at h'
    exact h'

end MixAux

open MixAux in
/-- Mixed configurations are exponentially rare:
    `mixed · L^(m-1) ≤ m · 2^q · L · Λ^(m-1)` whenever the eigenvector conditions hold. -/
theorem mixed_bound (m p q : Nat) (hm : 0 < m) (h3 : 3 ≤ m) (L Λ : Nat) (hL : 1 ≤ L)
    (h0 : (2 ^ (p + q) + 2 ^ q * L) * L ≤ Λ) (h1 : 3 ^ q * (L + 1) ≤ Λ) :
    mixedCount m p q hm * L ^ (m - 1) ≤ m * 2 ^ q * L * Λ ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : 2 ≤ n + 1 := by omega
  have hcount : mixedCount (n + 1) p q hm ≤ (n + 1) * gc p q n true := by
    unfold mixedCount
    calc _ ≤ (allFuns (allBlks p q) (n + 1)).countP
          (fun x => (finRange (n + 1)).any (fun i => Qc hm i x)) := by
          apply countP_mono
          intro x _ hx
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
          obtain ⟨⟨hv, hB⟩, hA⟩ := hx
          have hV := valid_ok h2 hv
          obtain ⟨i0, hi0⟩ := exists_false_of_allTrue_false (f := fun i => allTrue (x i).B) hB
          obtain ⟨i1, hi1⟩ := exists_false_of_allTrue_false (f := fun i => allTrue (x i).A) hA
          obtain ⟨i, hi, hc⟩ := exists_cut hm x hV i0 (by simp [ty, hi0]) i1 hi1
          rw [List.any_eq_true]
          refine ⟨i, mem_finRange i, ?_⟩
          simp only [Qc, hi, hc, Bool.not_false, Bool.true_and]
          exact (allTrue_iff _).2 hV
      _ ≤ sumList (finRange (n + 1))
          (fun i => (allFuns (allBlks p q) (n + 1)).countP (Qc hm i)) :=
          countP_any_le_sumList _ _ _
      _ ≤ sumList (finRange (n + 1)) (fun _ => gc p q n true) :=
          sumList_mono _ _ _ (fun i _ => Qc_le n hm i)
      _ = (n + 1) * gc p q n true := by rw [sumList_const, finRange_length]
  have hg := (gc_bound L Λ hL h0 h1 n).2
  calc mixedCount (n + 1) p q hm * L ^ n ≤ (n + 1) * gc p q n true * L ^ n :=
        Nat.mul_le_mul_right _ hcount
    _ = (n + 1) * (gc p q n true * L ^ n) := Nat.mul_assoc _ _ _
    _ ≤ (n + 1) * (2 ^ q * Λ ^ n * L) := Nat.mul_le_mul_left _ hg
    _ = (n + 1) * 2 ^ q * L * Λ ^ n := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end AlikhaniJafariDisproof


/-! # Numerics for the concrete parameters `m = 18000, p = 210, q = 359`

OWNER: Numerics agent. Exported definitions and theorem statements below are FROZEN
(except that `k2`, `α`, `β` may be retuned if needed; tell the coordinator).

`k2` was retuned from `2050725001` to `2050722001 = 1 + Q + m * (113549 + 21)`, so that
`k2 - 1 - Q` and `k2 - 1 - P` are exact multiples of `m`.

Strategy: every huge quantity is written as `(small const) * (per-block base)^m`; the
per-block ratio is bounded by a modest rational `num/den` (via `pow_add_le`), and
`exp_decay_of_ratio` turns it into a factor `2^(m/R)`. All generic lemmas are stated
over variables; only modest concrete facts are checked with `decide`. -/

namespace AlikhaniJafariDisproof

namespace NumAux

theorem choose_term_le (n s a b : Nat) (hs : s ≤ n) :
    choose n s * a ^ s * b ^ (n - s) ≤ (a + b) ^ n := by
  rw [← binomial_theorem n a b]
  exact single_le_sumRange hs (fun k => choose n k * a ^ k * b ^ (n - k))

theorem pw (x n k : Nat) : x ^ (n * k) = (x ^ k) ^ n := by
  rw [Nat.mul_comm, Nat.pow_mul]

/-- Combining a per-block certificate with exponential decay. -/
theorem decay_combine {U V num den R n c1 c2 : Nat} (hR : 1 ≤ R) (hnum : 0 < num)
    (hUV : U * den ≤ V * num) (hratio : num * (R + 1) ≤ den * R)
    (hc : c1 ≤ c2 * 2 ^ (n / R)) : c1 * U ^ n ≤ c2 * V ^ n := by
  have h1 := exp_decay_of_ratio hR hratio n
  have h2 : U ^ n * den ^ n ≤ V ^ n * num ^ n := by
    rw [← Nat.mul_pow, ← Nat.mul_pow]; exact Nat.pow_le_pow_left hUV n
  have h3 : (U ^ n * 2 ^ (n / R)) * num ^ n ≤ V ^ n * num ^ n := by
    calc (U ^ n * 2 ^ (n / R)) * num ^ n = U ^ n * (2 ^ (n / R) * num ^ n) := by
          rw [Nat.mul_assoc]
      _ ≤ U ^ n * den ^ n := Nat.mul_le_mul_left _ h1
      _ ≤ _ := h2
  have h4 : U ^ n * 2 ^ (n / R) ≤ V ^ n := le_of_mul_le_mul_right h3 (Nat.pow_pos hnum)
  calc c1 * U ^ n ≤ (c2 * 2 ^ (n / R)) * U ^ n := Nat.mul_le_mul_right _ hc
    _ = c2 * (U ^ n * 2 ^ (n / R)) := by
        rw [Nat.mul_assoc, Nat.mul_comm (2 ^ (n / R))]
    _ ≤ c2 * V ^ n := Nat.mul_le_mul_left _ h4

/-- Bound on the far-from-center binomial coefficient (family 1). -/
theorem X_bound (K n g d u v t a A b R N s : Nat)
    (hN : N = 2 * (n * g) + 1) (hs : s = n * u) (hNs : N - s = n * v + 1) (hsN : s ≤ N)
    (hu : u = g + d) (hv : g = v + d)
    (hA : a + t = A) (hAA : A * A = b + 1) (hb : 4 * a * t = b) (hgb : g ≤ b)
    (ht : 0 < t) (ha : 0 < a) (hbpos : 0 < b) (hR : 1 ≤ R)
    (hratio : b * t ^ d * (R + 1) ≤ (b - g) * a ^ d * R)
    (hc : K * A ≤ 2 * t * 2 ^ (n / R)) :
    K * choose N s ≤ 2 ^ N := by
  have hterm := choose_term_le N s a t hsN
  rw [hA] at hterm
  have hnum : 0 < b * t ^ d := Nat.mul_pos hbpos (Nat.pow_pos ht)
  have hUV : (b + 1) ^ g * ((b - g) * a ^ d) ≤ (4 ^ g * a ^ u * t ^ v) * (b * t ^ d) := by
    have hpal := pow_add_le 1 b g (by omega)
    rw [Nat.mul_one] at hpal
    have e1 : (b + 1) ^ g * ((b - g) * a ^ d) = ((b - g) * (b + 1) ^ g) * a ^ d := by
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have h1 : a ^ u = a ^ g * a ^ d := by rw [hu, Nat.pow_add]
    have h2 : t ^ v * t ^ d = t ^ g := by rw [← Nat.pow_add, ← hv]
    have h3 : b ^ g = 4 ^ g * a ^ g * t ^ g := by rw [← hb, Nat.mul_pow, Nat.mul_pow]
    have e2 : (4 ^ g * a ^ u * t ^ v) * (b * t ^ d) = (b * b ^ g) * a ^ d := by
      rw [h1, h3]
      calc 4 ^ g * (a ^ g * a ^ d) * t ^ v * (b * t ^ d)
          = b * (4 ^ g * a ^ g * (t ^ v * t ^ d)) * a ^ d := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ = _ := by rw [h2]
    rw [e1, e2]
    exact Nat.mul_le_mul_right _ hpal
  have hdec := decay_combine (n := n) (c1 := K * A) (c2 := 2 * t) hR hnum hUV hratio hc
  have hAN : A ^ N = A * ((b + 1) ^ g) ^ n := by
    rw [hN, Nat.pow_succ, Nat.pow_mul, Nat.pow_two, hAA, pw, Nat.mul_comm]
  have h22 : (2 : Nat) ^ 2 = 4 := rfl
  have hRHS : 2 ^ N * (a ^ s * t ^ (N - s)) = 2 * t * (4 ^ g * a ^ u * t ^ v) ^ n := by
    rw [hNs, hs, hN, Nat.pow_succ, Nat.pow_succ, Nat.pow_mul, h22, pw, pw, pw,
      Nat.mul_pow, Nat.mul_pow]
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hD : 0 < a ^ s * t ^ (N - s) := Nat.mul_pos (Nat.pow_pos ha) (Nat.pow_pos ht)
  apply le_of_mul_le_mul_right _ hD
  calc K * choose N s * (a ^ s * t ^ (N - s)) = K * (choose N s * a ^ s * t ^ (N - s)) := by
        simp only [Nat.mul_assoc]
    _ ≤ K * A ^ N := Nat.mul_le_mul_left K hterm
    _ = K * A * ((b + 1) ^ g) ^ n := by rw [hAN, Nat.mul_assoc]
    _ ≤ 2 * t * (4 ^ g * a ^ u * t ^ v) ^ n := hdec
    _ = 2 ^ N * (a ^ s * t ^ (N - s)) := hRHS.symm

/-- Bound on the family-2 count from its Chernoff certificate. -/
theorem Y_bound (K n c q' e f a2 b2 n1 r al be w z b R C Q s N Y : Nat)
    (hY : Y * (al ^ s * be ^ (C + 2 * Q - s)) ≤ w ^ C * (al * z) ^ Q)
    (hC : C = n * c + 1) (hQ : Q = n * q') (hs : s = n * a2) (hs2 : C + 2 * Q - s = n * b2 + 1)
    (hN : N = n * n1 + 1)
    (hcf : c + f = 2 * e) (ha2 : a2 = e + q') (hb2 : b2 + f = e + q') (hn1 : n1 + f = 2 * e + r)
    (hb : 4 * al * be = b) (hww : w * w = b + 1) (heb : e ≤ b)
    (hal : 0 < al) (hbe : 0 < be) (hz : 0 < z) (hbpos : 0 < b) (hR : 1 ≤ R)
    (hratio : b * z ^ q' * (2 * be) ^ f * (R + 1) ≤ (b - e) * w ^ f * 2 ^ r * be ^ q' * R)
    (hc : K * w ≤ 2 * be * 2 ^ (n / R)) :
    K * Y ≤ 2 ^ N := by
  have hnum : 0 < b * z ^ q' * (2 * be) ^ f :=
    Nat.mul_pos (Nat.mul_pos hbpos (Nat.pow_pos hz)) (Nat.pow_pos (by omega))
  -- per-block certificate
  have hUV : (w ^ c * (al * z) ^ q') * ((b - e) * w ^ f * 2 ^ r * be ^ q') ≤
      (2 ^ n1 * al ^ a2 * be ^ b2) * (b * z ^ q' * (2 * be) ^ f) := by
    have hpal := pow_add_le 1 b e (by omega)
    rw [Nat.mul_one] at hpal
    have hw2 : w ^ c * w ^ f = (b + 1) ^ e := by
      rw [← Nat.pow_add, hcf, Nat.pow_mul, Nat.pow_two, hww]
    have h2 : 2 ^ n1 * 2 ^ f = 4 ^ e * 2 ^ r := by
      rw [← Nat.pow_add, hn1, Nat.pow_add, Nat.pow_mul]
    have hbb : be ^ b2 * be ^ f = be ^ e * be ^ q' := by
      rw [← Nat.pow_add, hb2, Nat.pow_add]
    have hal2 : al ^ a2 = al ^ e * al ^ q' := by rw [ha2, Nat.pow_add]
    have h3 : b ^ e = 4 ^ e * al ^ e * be ^ e := by rw [← hb, Nat.mul_pow, Nat.mul_pow]
    have e1 : (w ^ c * (al * z) ^ q') * ((b - e) * w ^ f * 2 ^ r * be ^ q') =
        ((b - e) * (w ^ c * w ^ f)) * (al ^ q' * z ^ q' * 2 ^ r * be ^ q') := by
      rw [Nat.mul_pow]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have e2 : (2 ^ n1 * al ^ a2 * be ^ b2) * (b * z ^ q' * (2 * be) ^ f) =
        (b * ((2 ^ n1 * 2 ^ f) * al ^ a2 * (be ^ b2 * be ^ f))) * z ^ q' := by
      rw [Nat.mul_pow]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have e3 : b * ((4 ^ e * 2 ^ r) * (al ^ e * al ^ q') * (be ^ e * be ^ q')) * z ^ q' =
        (b * (4 ^ e * al ^ e * be ^ e)) * (al ^ q' * z ^ q' * 2 ^ r * be ^ q') := by
      simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    rw [e1, e2, h2, hal2, hbb, e3, hw2, ← h3]
    exact Nat.mul_le_mul_right _ hpal
  have hdec := decay_combine (n := n) (c1 := K * w) (c2 := 2 * be) hR hnum hUV hratio hc
  have hL : w ^ C * (al * z) ^ Q = w * (w ^ c * (al * z) ^ q') ^ n := by
    rw [hC, hQ, Nat.pow_succ, pw, pw, Nat.mul_pow (w ^ c) ((al * z) ^ q') n]
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hRHS : 2 ^ N * (al ^ s * be ^ (C + 2 * Q - s)) = 2 * be * (2 ^ n1 * al ^ a2 * be ^ b2) ^ n := by
    rw [hs2, hs, hN, Nat.pow_succ, Nat.pow_succ, pw, pw, pw, Nat.mul_pow, Nat.mul_pow]
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hD : 0 < al ^ s * be ^ (C + 2 * Q - s) := Nat.mul_pos (Nat.pow_pos hal) (Nat.pow_pos hbe)
  apply le_of_mul_le_mul_right _ hD
  calc K * Y * (al ^ s * be ^ (C + 2 * Q - s)) = K * (Y * (al ^ s * be ^ (C + 2 * Q - s))) := by
        rw [Nat.mul_assoc]
    _ ≤ K * (w ^ C * (al * z) ^ Q) := Nat.mul_le_mul_left K hY
    _ = K * w * (w ^ c * (al * z) ^ q') ^ n := by rw [hL, Nat.mul_assoc]
    _ ≤ 2 * be * (2 ^ n1 * al ^ a2 * be ^ b2) ^ n := hdec
    _ = 2 ^ N * (al ^ s * be ^ (C + 2 * Q - s)) := hRHS.symm

/-- Bound on the mixed term `2^C * M`. -/
theorem Z_bound (K n C N r qq L Λ M j t0 : Nat)
    (hM : M * L ^ (n - 1) ≤ n * 2 ^ qq * L * Λ ^ (n - 1))
    (hΛ : Λ = 3 ^ qq * (L + 1)) (hN : N = C + n * r) (hn : 1 ≤ n) (hlt : n - 1 < L)
    (hj : (3 ^ qq) ^ j ≤ 2 ^ (r * j + 1)) (hnj : n = j * t0) (hE : (r * j + 1) * t0 = n * r + t0)
    (hc : K * n * 2 ^ qq * L * L * 2 ^ t0 ≤ (L - (n - 1)) * 3 ^ qq) :
    K * (2 ^ C * M) ≤ 2 ^ N := by
  have hpa := pow_add_le 1 L (n - 1) (by omega)
  rw [Nat.mul_one] at hpa
  have h1 : M * (L - (n - 1)) * L ^ (n - 1) ≤
      (n * 2 ^ qq * L * (3 ^ qq) ^ (n - 1) * L) * L ^ (n - 1) := by
    calc M * (L - (n - 1)) * L ^ (n - 1) = (M * L ^ (n - 1)) * (L - (n - 1)) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ (n * 2 ^ qq * L * Λ ^ (n - 1)) * (L - (n - 1)) := Nat.mul_le_mul_right _ hM
      _ = (n * 2 ^ qq * L * (3 ^ qq) ^ (n - 1)) * ((L - (n - 1)) * (L + 1) ^ (n - 1)) := by
          rw [hΛ, Nat.mul_pow]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ (n * 2 ^ qq * L * (3 ^ qq) ^ (n - 1)) * (L * L ^ (n - 1)) := Nat.mul_le_mul_left _ hpa
      _ = (n * 2 ^ qq * L * (3 ^ qq) ^ (n - 1) * L) * L ^ (n - 1) := by
          simp only [Nat.mul_assoc]
  have h2 := le_of_mul_le_mul_right h1 (Nat.pow_pos (by omega))
  have h3n : (3 ^ qq) ^ n ≤ 2 ^ (n * r) * 2 ^ t0 := by
    rw [hnj, Nat.pow_mul, ← Nat.pow_add, ← hnj, ← hE, Nat.pow_mul]
    exact Nat.pow_le_pow_left hj t0
  have h3s : (3 ^ qq) ^ (n - 1) * 3 ^ qq = (3 ^ qq) ^ n := by
    rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  have hG : 0 < (L - (n - 1)) * 3 ^ qq := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  apply le_of_mul_le_mul_right _ hG
  calc K * (2 ^ C * M) * ((L - (n - 1)) * 3 ^ qq)
      = (2 ^ C * K * 3 ^ qq) * (M * (L - (n - 1))) := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (2 ^ C * K * 3 ^ qq) * (n * 2 ^ qq * L * (3 ^ qq) ^ (n - 1) * L) :=
        Nat.mul_le_mul_left _ h2
    _ = (2 ^ C * (K * n * 2 ^ qq * L * L)) * ((3 ^ qq) ^ (n - 1) * 3 ^ qq) := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    _ = (2 ^ C * (K * n * 2 ^ qq * L * L)) * (3 ^ qq) ^ n := by rw [h3s]
    _ ≤ (2 ^ C * (K * n * 2 ^ qq * L * L)) * (2 ^ (n * r) * 2 ^ t0) := Nat.mul_le_mul_left _ h3n
    _ = (2 ^ C * 2 ^ (n * r)) * (K * n * 2 ^ qq * L * L * 2 ^ t0) := by
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (2 ^ C * 2 ^ (n * r)) * ((L - (n - 1)) * 3 ^ qq) := Nat.mul_le_mul_left _ hc
    _ = 2 ^ N * ((L - (n - 1)) * 3 ^ qq) := by rw [hN, Nat.pow_add]

theorem lb1 (N K : Nat) (hK : N + 1 ≤ K) : 2 ^ N ≤ K * choose N (N / 2) :=
  Nat.le_trans (central_choose_lower N) (Nat.mul_le_mul_right _ hK)

theorem lb3 (C P Q N n p q : Nat) (hN : N = C + (P + Q)) (hPQ : P + Q = n * (p + q))
    (hQ : Q = n * q) (hpq : 2 ^ (p + q) ≤ 3 ^ q) :
    2 ^ N ≤ ((C + 1) * (Q + 1)) * (choose C (C / 2) * (choose Q (Q / 3) * 2 ^ (Q - Q / 3))) := by
  have h1 := central_choose_lower C
  have h2 := weighted_binom_lower Q
  have h3 : 2 ^ (P + Q) ≤ 3 ^ Q := by
    rw [hPQ, hQ, pw, pw]; exact Nat.pow_le_pow_left hpq n
  rw [hN, Nat.pow_add]
  calc 2 ^ C * 2 ^ (P + Q)
      ≤ ((C + 1) * choose C (C / 2)) * ((Q + 1) * (choose Q (Q / 3) * 2 ^ (Q - Q / 3))) :=
        Nat.mul_le_mul h1 (Nat.le_trans h3 h2)
    _ = _ := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

theorem combine {X Y Z LB K B : Nat} (hX : 4 * K * X ≤ B) (hY : 4 * K * Y ≤ B)
    (hZ : 4 * K * Z ≤ B) (hB : 0 < B) (hLB : B ≤ K * LB) : X + Y + Z < LB := by
  have h4 : 4 * B ≤ 4 * K * LB := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 4 hLB
  have h : 4 * K * (X + Y + Z) < 4 * K * LB := by
    rw [Nat.mul_add, Nat.mul_add]
    generalize 4 * K * X = x at *
    generalize 4 * K * Y = y at *
    generalize 4 * K * Z = z at *
    generalize 4 * K * LB = l at *
    omega
  exact Nat.lt_of_mul_lt_mul_left h

end NumAux

namespace Params

def m : Nat := 18000
def p : Nat := 210
def q : Nat := 359
/-- `numFree m p q`, written out (the Graph module's `numFree` is `1 + m*q + m*q*3*p`). -/
def C : Nat := 1 + m * q + m * q * 3 * p
def P : Nat := m * p
def Q : Nat := m * q
def N1 : Nat := C + P + Q
def k1 : Nat := 1 + Q + N1 / 2
def k3 : Nat := 1 + P + Q + C / 2 + Q / 3
def k2 : Nat := 2050722001
def α : Nat := 2374
def β : Nat := 2375
def L : Nat := 2 ^ 18
def Λ : Nat := 3 ^ q * (L + 1)

theorem k_order : k1 < k2 ∧ k2 < k3 ∧ 1 + P + Q ≤ k2 := by
  decide

set_option exponentiation.threshold 1000 in
theorem mix_h0 : (2 ^ (p + q) + 2 ^ q * L) * L ≤ Λ := by
  decide

theorem mix_h1 : 3 ^ q * (L + 1) ≤ Λ := Nat.le_refl _

set_option exponentiation.threshold 400000 in
theorem numeric_valley (Y M : Nat)
    (hY : Y * (α ^ (k2 - 1 - P) * β ^ (C + 2 * Q - (k2 - 1 - P))) ≤
      (α + β) ^ C * (α * (α + 2 * β)) ^ Q)
    (hM : M * L ^ (m - 1) ≤ m * 2 ^ q * L * Λ ^ (m - 1)) :
    choose N1 (k2 - 1 - Q) + Y + 2 ^ C * M < choose N1 (N1 / 2) ∧
    choose N1 (k2 - 1 - Q) + Y + 2 ^ C * M <
      choose C (C / 2) * (choose Q (Q / 3) * 2 ^ (Q - Q / 3)) := by
  have hX : 4 * ((C + 1) * (Q + 1)) * choose N1 (k2 - 1 - Q) ≤ 2 ^ N1 :=
    NumAux.X_bound (4 * ((C + 1) * (Q + 1))) m 113549 21 113570 113528 3000 3001 6001 36012000 260
      N1 (k2 - 1 - Q) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hY' : 4 * ((C + 1) * (Q + 1)) * Y ≤ 2 ^ N1 :=
    NumAux.Y_bound (4 * ((C + 1) * (Q + 1))) m 226529 359 113360 191 113719 113528 227098 569
      α β (α + β) (α + 2 * β) 22553000 246 C Q (k2 - 1 - P) N1 Y hY
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hZ : 4 * ((C + 1) * (Q + 1)) * (2 ^ C * M) ≤ 2 ^ N1 :=
    NumAux.Z_bound (4 * ((C + 1) * (Q + 1))) m C N1 569 q L Λ M 600 30 hM
      rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hB : 0 < 2 ^ N1 := Nat.pow_pos (by decide)
  have hL1 : 2 ^ N1 ≤ ((C + 1) * (Q + 1)) * choose N1 (N1 / 2) :=
    NumAux.lb1 N1 _ (by decide)
  have hL3 := NumAux.lb3 C P Q N1 m p q (Nat.add_assoc C P Q) (by decide) (by decide) (by decide)
  exact ⟨NumAux.combine hX hY' hZ hB hL1, NumAux.combine hX hY' hZ hB hL3⟩

end Params
end AlikhaniJafariDisproof


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

