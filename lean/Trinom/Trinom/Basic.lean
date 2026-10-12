/-
Copyright (c) 2026 Otaxon Kenjayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otaxon Kenjayev
-/
import Mathlib

/-!
# Main-branch sequence for `P = 1 + a X^b + X^k`

Setting: real `a` with `0 < a < 1`, naturals `b ≥ 1`, `k > b`.

The main-branch sequence `q : ℕ → ℝ` is
`q n = r n - a * q (n - b) - q (n - k)`, where terms with negative index are `0`,
`r 0 = 1`, and for `n ≥ 1`, `r n = 0` if both partners `q (n - b)` and `q (n - k)` are zero
(negative index counts as zero), else `r n = 1`.
-/

open Finset

namespace Trinom

/-- The main-branch sequence. Partners with negative index are `0`. -/
noncomputable def q (a : ℝ) (b k : ℕ) : ℕ → ℝ
  | n =>
    let pb : ℝ := if _h : 0 < b ∧ b ≤ n then q a b k (n - b) else 0
    let pk : ℝ := if _h : 0 < k ∧ k ≤ n then q a b k (n - k) else 0
    let r : ℝ := if n = 0 then 1 else if pb = 0 ∧ pk = 0 then 0 else 1
    r - a * pb - pk
termination_by n => n
decreasing_by all_goals omega

/-- Partner value `q (n - d)`, or `0` when the index `n - d` is negative. -/
noncomputable def P (a : ℝ) (b k d n : ℕ) : ℝ :=
  if 0 < d ∧ d ≤ n then q a b k (n - d) else 0

/-- Partial geometric sum `∑_{t ≤ i} (-a)^t`. -/
noncomputable def S (a : ℝ) (i : ℕ) : ℝ := ∑ t ∈ range (i + 1), (-a) ^ t

theorem q_unfold (a : ℝ) (b k n : ℕ) :
    q a b k n =
      (if n = 0 then 1 else if P a b k b n = 0 ∧ P a b k k n = 0 then 0 else 1)
        - a * P a b k b n - P a b k k n := by
  rw [q]
  simp only [P, dite_eq_ite]
  split_ifs <;> rfl

theorem P_of_le {a : ℝ} {b k d n : ℕ} (hd : 0 < d) (h : d ≤ n) :
    P a b k d n = q a b k (n - d) := by
  simp [P, hd, h]

theorem P_of_lt {a : ℝ} {b k d n : ℕ} (h : n < d) : P a b k d n = 0 := by
  simp [P]
  omega

theorem S_zero (a : ℝ) : S a 0 = 1 := by simp [S]

theorem S_succ (a : ℝ) (i : ℕ) : S a (i + 1) = 1 - a * S a i := by
  unfold S
  rw [sum_range_succ', pow_zero]
  have h : ∑ t ∈ range (i + 1), (-a) ^ (t + 1) = (-a) * ∑ t ∈ range (i + 1), (-a) ^ t := by
    rw [mul_sum]
    exact sum_congr rfl (fun t _ => pow_succ' (-a) t)
  rw [h]
  ring

theorem S_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (i : ℕ) : 0 < S a i ∧ S a i ≤ 1 := by
  induction i with
  | zero => simp [S_zero]
  | succ i ih =>
    rw [S_succ]
    obtain ⟨h1, h2⟩ := ih
    constructor <;> nlinarith

/-- Core invariant below `k`: `q n = S (n / b)` if `b ∣ n`, else `0`. -/
theorem q_below_k {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 0 < b) :
    ∀ n, n < k → q a b k n = if b ∣ n then S a (n / b) else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [q_unfold, P_of_lt (d := k) hn]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [P_of_lt (d := b) hb]
      simp [S_zero]
    · have hn0 : n ≠ 0 := by omega
      rcases lt_or_ge n b with hlt | hge
      · rw [P_of_lt (d := b) hlt]
        have hnd : ¬ b ∣ n := fun hd => absurd (Nat.le_of_dvd hpos hd) (by omega)
        simp [hn0, hnd]
      · rw [P_of_le hb hge, ih (n - b) (by omega) (by omega)]
        have hiff : b ∣ n - b ↔ b ∣ n := by
          have e : n = (n - b) + b := by omega
          constructor
          · intro h; rw [e]; exact dvd_add h dvd_rfl
          · intro h; rw [e] at h; exact (Nat.dvd_add_left (dvd_refl b)).mp h
        by_cases hd : b ∣ n
        · obtain ⟨m, rfl⟩ := hd
          have hm : 1 ≤ m := by
            rcases Nat.eq_zero_or_pos m with hm | hm
            · subst hm; simp at hn0
            · exact hm
          have hsub : b * m - b = b * (m - 1) := by rw [Nat.mul_sub_one]
          have hdiv : (b * m - b) / b = m - 1 := by
            rw [hsub, Nat.mul_div_cancel_left _ hb]
          have hdvd : b ∣ b * m - b := hiff.mpr (dvd_mul_right b m)
          have hSpos := (S_bounds ha0 ha1 (m - 1)).1
          have hm' : m = (m - 1) + 1 := by omega
          rw [ite_eq_left hdvd, hdiv, ite_eq_left (dvd_mul_right b m), Nat.mul_div_cancel_left _ hb]
          rw [ite_eq_right hn0, ite_eq_right (by intro h; exact (ne_of_gt hSpos) h.1)]
          conv_rhs => rw [hm', S_succ]
          ring
        · have hd' : ¬ b ∣ n - b := fun h => hd (hiff.mp h)
          simp [hn0, hd, hd']

/-! ## L1 : the case `b = 1` -/

/-- (L1a) For `b = 1` and every `n < k` (in particular `1 ≤ n < k`): `0 < q n ≤ 1`. -/
theorem L1_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k n : ℕ} (hn : n < k) :
    0 < q a 1 k n ∧ q a 1 k n ≤ 1 := by
  rw [q_below_k ha0 ha1 Nat.one_pos n hn]
  simpa using S_bounds ha0 ha1 n

/-- (L1b) For `b = 1`, `k > 1`: `q k = -a * q (k-1)` and `q k < 0`. -/
theorem L1_qk {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k : ℕ} (hk : 1 < k) :
    q a 1 k k = -a * q a 1 k (k - 1) ∧ q a 1 k k < 0 := by
  have hpos := (L1_pos ha0 ha1 (k := k) (n := k - 1) (by omega)).1
  have hq0 : q a 1 k 0 = 1 := by
    rw [q_below_k ha0 ha1 Nat.one_pos 0 (by omega)]; simp [S_zero]
  have hk0 : k ≠ 0 := by omega
  have hP1 : P a 1 k 1 k = q a 1 k (k - 1) := P_of_le Nat.one_pos (by omega)
  have hPk : P a 1 k k k = 1 := by rw [P_of_le (by omega) le_rfl, Nat.sub_self, hq0]
  have heq : q a 1 k k = -a * q a 1 k (k - 1) := by
    rw [q_unfold, hP1, hPk, ite_eq_right hk0, ite_eq_right (by norm_num)]
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  nlinarith

/-! ## L2 : Lemma A_b for general `b` -/

/-- (L2a) For `n < k`: `q n ≠ 0 ↔ b ∣ n`. -/
theorem L2_support {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 0 < b) {n : ℕ}
    (hn : n < k) : q a b k n ≠ 0 ↔ b ∣ n := by
  rw [q_below_k ha0 ha1 hb n hn]
  by_cases hd : b ∣ n
  · simp only [hd, ite_true, iff_true]
    exact ne_of_gt (S_bounds ha0 ha1 _).1
  · simp [hd]

/-- (L2b) For `i * b < k`: `q (i * b) = ∑_{t ≤ i} (-a)^t`. -/
theorem L2_mult {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 0 < b) {i : ℕ}
    (hi : i * b < k) : q a b k (i * b) = ∑ t ∈ range (i + 1), (-a) ^ t := by
  rw [q_below_k ha0 ha1 hb _ hi, ite_eq_left (dvd_mul_left b i), Nat.mul_div_cancel _ hb]
  rfl

/-- (L2c) `q b = 1 - a` (for `0 < b < k`). -/
theorem L2_qb {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 0 < b) (hbk : b < k) :
    q a b k b = 1 - a := by
  have := L2_mult ha0 ha1 hb (i := 1) (k := k) (by simpa using hbk)
  simp only [one_mul] at this
  rw [this]
  simp [sum_range_succ]
  ring

theorem L2_q2b {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 0 < b) (h2bk : 2 * b < k) :
    q a b k (2 * b) = 1 - a + a ^ 2 := by
  have := L2_mult ha0 ha1 hb (i := 2) (k := k) h2bk
  rw [this]
  simp [sum_range_succ]
  ring

/-- (L2d) `q k = 0` when `2 ≤ b < k` and `gcd(b, k) = 1`. -/
theorem L2_qk {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 2 ≤ b) (hbk : b < k)
    (hcop : Nat.Coprime b k) : q a b k k = 0 := by
  have hb0 : 0 < b := by omega
  have hndk : ¬ b ∣ k := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hcop h; omega
  have hnd : ¬ b ∣ k - b := fun h => hndk (by
    have e : k = (k - b) + b := by omega
    rw [e]; exact dvd_add h dvd_rfl)
  have hqkb : q a b k (k - b) = 0 := by
    rw [q_below_k ha0 ha1 hb0 _ (by omega), ite_eq_right hnd]
  have hq0 : q a b k 0 = 1 := by
    rw [q_below_k ha0 ha1 hb0 0 (by omega)]; simp [S_zero]
  have hk0 : k ≠ 0 := by omega
  rw [q_unfold, P_of_le hb0 hbk.le, hqkb, P_of_le (by omega) le_rfl, Nat.sub_self, hq0,
    ite_eq_right hk0, ite_eq_right (by norm_num)]
  ring

/-- (L2e) `q (k + b) = a`. -/
theorem L2_qkb {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 2 ≤ b) (hbk : b < k)
    (hcop : Nat.Coprime b k) : q a b k (k + b) = a := by
  have hb0 : 0 < b := by omega
  have hqk := L2_qk ha0 ha1 hb hbk hcop
  have hqb := L2_qb ha0 ha1 hb0 hbk
  have hn0 : k + b ≠ 0 := by omega
  rw [q_unfold, P_of_le hb0 (by omega), P_of_le (by omega : 0 < k) (by omega),
    Nat.add_sub_cancel, Nat.add_sub_cancel_left, hqk, hqb, ite_eq_right hn0,
    ite_eq_right (by intro h; have := h.2; linarith)]
  ring

/-- (L2f) `q (k + 2b) = a - 2a²` (needs `2b < k`). -/
theorem L2_qk2b {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {b k : ℕ} (hb : 2 ≤ b) (h2bk : 2 * b < k)
    (hcop : Nat.Coprime b k) : q a b k (k + 2 * b) = a - 2 * a ^ 2 := by
  have hb0 : 0 < b := by omega
  have hqkb := L2_qkb ha0 ha1 hb (by omega) hcop
  have hq2b := L2_q2b ha0 ha1 hb0 h2bk
  have hn0 : k + 2 * b ≠ 0 := by omega
  have e1 : k + 2 * b - b = k + b := by omega
  rw [q_unfold, P_of_le hb0 (by omega), P_of_le (by omega : 0 < k) (by omega), e1,
    Nat.add_sub_cancel_left, hqkb, hq2b, ite_eq_right hn0,
    ite_eq_right (by intro h; have := h.1; linarith)]
  ring

/-- (L2g) Hence `q (k + 2b) < 0` when `a > 1/2`. -/
theorem L2_qk2b_neg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hahalf : 1 / 2 < a) {b k : ℕ}
    (hb : 2 ≤ b) (h2bk : 2 * b < k) (hcop : Nat.Coprime b k) : q a b k (k + 2 * b) < 0 := by
  rw [L2_qk2b ha0 ha1 hb h2bk hcop]
  nlinarith

/-! ## L3 : reciprocity -/

open Polynomial

theorem L3_natDegree (a : ℝ) {b k : ℕ} (hbk : b < k) :
    (1 + C a * X ^ b + X ^ k : ℝ[X]).natDegree = k := by
  have h1 : (C a * X ^ b + 1 : ℝ[X]).natDegree < k := by
    calc (C a * X ^ b + 1 : ℝ[X]).natDegree
        ≤ max (C a * X ^ b : ℝ[X]).natDegree (1 : ℝ[X]).natDegree := natDegree_add_le _ _
      _ ≤ b := by
        rw [natDegree_one]
        exact max_le (natDegree_C_mul_X_pow_le a b) (Nat.zero_le _)
      _ < k := hbk
  have e : (1 + C a * X ^ b + X ^ k : ℝ[X]) = X ^ k + (C a * X ^ b + 1) := by ring
  rw [e, natDegree_add_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]

/-- (L3a) `reverse (1 + a X^b + X^k) = 1 + a X^(k-b) + X^k`. -/
theorem L3_reverse_P (a : ℝ) {b k : ℕ} (hbk : b < k) :
    (1 + C a * X ^ b + X ^ k : ℝ[X]).reverse = 1 + C a * X ^ (k - b) + X ^ k := by
  rw [reverse, L3_natDegree a hbk, reflect_add, reflect_add, reflect_C_mul_X_pow,
    reflect_monomial, revAt_le hbk.le, revAt_le le_rfl, Nat.sub_self, pow_zero]
  have h1 : reflect k (1 : ℝ[X]) = X ^ k := by
    rw [← C_1, reflect_C, C_1, one_mul]
  rw [h1]
  ring

/-- (L3b) If `R = P * Q` with `P = 1 + a X^b + X^k`, then
`reverse R = reverse P * reverse Q = (1 + a X^(k-b) + X^k) * reverse Q`. -/
theorem L3_reverse_R (a : ℝ) {b k : ℕ} (hbk : b < k) (Q R : ℝ[X])
    (hR : R = (1 + C a * X ^ b + X ^ k) * Q) :
    R.reverse = (1 + C a * X ^ b + X ^ k : ℝ[X]).reverse * Q.reverse ∧
      R.reverse = (1 + C a * X ^ (k - b) + X ^ k) * Q.reverse := by
  rw [hR, reverse_mul_of_domain, L3_reverse_P a hbk]
  exact ⟨rfl, rfl⟩

end Trinom
