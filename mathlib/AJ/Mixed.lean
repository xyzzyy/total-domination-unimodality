import AJ.Config

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
