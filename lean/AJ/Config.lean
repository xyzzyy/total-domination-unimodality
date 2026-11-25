import AJ.Graph

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
