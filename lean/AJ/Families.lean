import AJ.Config

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
