import AJ.Basic

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
