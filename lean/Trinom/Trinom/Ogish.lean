/-
Copyright (c) 2026 Otaxon Kenjayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otaxon Kenjayev
-/
import Trinom.Basic

/-!
# All branches ("og'ish shoxlari") for `P = 1 + a X^b + X^k`

`Basic.lean` treats only the *main* branch.  Here we treat an **arbitrary** branch:
any `q r : ℕ → ℝ` with

* `r n ∈ {0, 1}` for every `n`,
* `q n + a * q (n - b) + q (n - k) = r n` (negative indices count as `0`),
* `q 0 = 1` (normalisation: the lowest coefficient of `Q`).

This is exactly the coefficient recursion of `P * Q = R` with `R` a `0/1` polynomial.
Nonnegativity of `q` is always an explicit *finite-range* hypothesis, so every theorem
below says "no branch stays nonnegative up to index `N`".

The rule "`r n = 0` ⇒ both partners vanish" is **not** assumed: it follows from
nonnegativity (`IsRec.partners_zero`).

Main results:
* `E1`              — Lemma E1: if the class `n ≡ k (mod b)` starts at some `s < k`
                      (`r s = 1`), the branch dies at `n = k`.
* `E_bm1`           — Lemma E(b−1): if the class `n + k ≡ 0 (mod b)` starts at `s < k`,
                      the branch dies at `n = s + k`.
* `A_b_star`        — Lemma A_b*: for `1/2 < a < 1`, `2b < k`, no branch is nonnegative on
                      `0 … k + 2b`.  (No coprimality hypothesis is needed.)
* `A_b_star_coprime`— the same with the `gcd(b, k) = 1` hypothesis of `ISBOT.md`.
* `dies_of_dvd`     — if `b ∣ k`, every branch dies at `n = k`.
* `R_reduce`        — Lemma R(i), sequence form: for `d ∣ b`, `d ∣ k`, every residue
                      subsequence `m ↦ q (i + d m)` satisfies the recursion of
                      `1 + a X^(b/d) + X^(k/d)`; the residue `0` is again a branch.
* `main_isBranch`   — the main branch of `Basic.lean` is a branch in this sense.
-/

namespace Trinom.Ogish

/-- Partner value `q (n - d)`; `0` when the index `n - d` is negative. -/
def Pd (q : ℕ → ℝ) (d n : ℕ) : ℝ := if d ≤ n then q (n - d) else 0

theorem Pd_of_le {q : ℕ → ℝ} {d n : ℕ} (h : d ≤ n) : Pd q d n = q (n - d) := by
  simp [Pd, h]

theorem Pd_of_lt {q : ℕ → ℝ} {d n : ℕ} (h : n < d) : Pd q d n = 0 := by
  simp only [Pd, ite_eq_right_iff]
  intro h'
  omega

/-- The recursion `q n + a q (n-b) + q (n-k) = r n` with `r n ∈ {0,1}`. -/
structure IsRec (a : ℝ) (b k : ℕ) (q r : ℕ → ℝ) : Prop where
  r01 : ∀ n, r n = 0 ∨ r n = 1
  eq : ∀ n, q n + a * Pd q b n + Pd q k n = r n

/-- A branch: the recursion together with the normalisation `q 0 = 1`. -/
structure IsBranch (a : ℝ) (b k : ℕ) (q r : ℕ → ℝ) : Prop extends IsRec a b k q r where
  q0 : q 0 = 1

variable {a : ℝ} {b k : ℕ} {q r : ℕ → ℝ}

theorem IsRec.r_le_one (h : IsRec a b k q r) (n : ℕ) : r n ≤ 1 := by
  rcases h.r01 n with h | h <;> simp [h]

/-- Partners of an index `n ≤ N` are nonnegative when `q` is nonnegative below `N`. -/
theorem Pd_nonneg {N d n : ℕ} (hnn : ∀ m < N, 0 ≤ q m) (hd : 0 < d) (hn : n ≤ N) :
    0 ≤ Pd q d n := by
  unfold Pd
  split_ifs with h
  · exact hnn _ (by omega)
  · exact le_rfl

/-- `r n = 0` forces `q n` and both partners to vanish (from nonnegativity). -/
theorem IsRec.partners_zero (h : IsRec a b k q r) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    {N n : ℕ} (hnn : ∀ m < N, 0 ≤ q m) (hn : n < N) (hr : r n = 0) :
    q n = 0 ∧ Pd q b n = 0 ∧ Pd q k n = 0 := by
  have h1 := h.eq n
  have hPb := Pd_nonneg hnn hb hn.le
  have hPk := Pd_nonneg hnn hk hn.le
  have hab := mul_nonneg ha.le hPb
  have hq := hnn n hn
  rw [hr] at h1
  have hab0 : a * Pd q b n = 0 := by linarith
  exact ⟨by linarith, (mul_eq_zero.mp hab0).resolve_left ha.ne', by linarith⟩

/-- Below the nonnegativity range, `q n ≤ r n ≤ 1`. -/
theorem IsRec.q_le_one (h : IsRec a b k q r) (ha : 0 ≤ a) (hb : 0 < b) (hk : 0 < k)
    {N n : ℕ} (hnn : ∀ m < N, 0 ≤ q m) (hn : n ≤ N) : q n ≤ 1 := by
  have h1 := h.eq n
  have hPb := Pd_nonneg hnn hb hn
  have hPk := Pd_nonneg hnn hk hn
  have hab := mul_nonneg ha hPb
  linarith [h.r_le_one n]

/-- `r n ≠ 0` (hence `r n = 1`) as soon as `q n ≥ 0` and the partner sum is positive. -/
theorem IsRec.r_eq_one (h : IsRec a b k q r) {n : ℕ} (hq : 0 ≤ q n)
    (hpos : 0 < a * Pd q b n + Pd q k n) : r n = 1 := by
  rcases h.r01 n with h0 | h1
  · have := h.eq n
    linarith
  · exact h1

theorem mod_sub_self {n b : ℕ} (h : b ≤ n) : (n - b) % b = n % b := by
  conv_rhs => rw [show n = (n - b) + b by omega]
  rw [Nat.add_mod_right]

/-! ## Lemma E1 -/

/-- **Lemma E1.** Let `0 < a < 1`. If the class `n ≡ k (mod b)` starts below `k`
(some `s < k`, `s ≡ k [MOD b]`, `r s = 1`), then a branch that is nonnegative on
`0 … k-1` has `q k < 0`.  In particular no such branch is nonnegative up to `k`. -/
theorem E1 (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hB : IsBranch a b k q r) {s : ℕ}
    (hsk : s < k) (hmod : s ≡ k [MOD b]) (hrs : r s = 1) (hnn : ∀ n < k, 0 ≤ q n) :
    q k < 0 := by
  have hk : 0 < k := by omega
  have hR := hB.toIsRec
  -- the chain `s, s + b, …` below `k` stays positive
  have chain : ∀ n, n < k → s ≤ n → n ≡ s [MOD b] → 0 < q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hsn hns
      have hPk : Pd q k n = 0 := Pd_of_lt hn
      have hPb0 : 0 ≤ Pd q b n := Pd_nonneg hnn hb hn.le
      have hPb1 : Pd q b n ≤ 1 := by
        unfold Pd
        split_ifs with h
        · exact hR.q_le_one ha0.le hb hk hnn (by omega)
        · norm_num
      have hrn : r n = 1 := by
        rcases Nat.eq_or_lt_of_le hsn with h | h
        · subst h
          exact hrs
        · have hdvd : b ∣ n - s := (Nat.modEq_iff_dvd' hsn).mp hns.symm
          have hbns : b ≤ n - s := Nat.le_of_dvd (by omega) hdvd
          have hm : n - b ≡ s [MOD b] := by
            unfold Nat.ModEq
            rw [mod_sub_self (by omega)]
            exact hns
          have hpos : 0 < q (n - b) := ih (n - b) (by omega) (by omega) (by omega) hm
          apply hR.r_eq_one (hnn n hn)
          rw [Pd_of_le (by omega), hPk]
          have := mul_pos ha0 hpos
          linarith
      have h1 := hR.eq n
      rw [hrn, hPk] at h1
      have : a * Pd q b n ≤ a := by nlinarith
      linarith
  have hdvd : b ∣ k - s := (Nat.modEq_iff_dvd' hsk.le).mp hmod
  have hbks : b ≤ k - s := Nat.le_of_dvd (by omega) hdvd
  have hm : k - b ≡ s [MOD b] := by
    unfold Nat.ModEq
    rw [mod_sub_self (by omega)]
    exact hmod.symm
  have hkb : 0 < q (k - b) := chain (k - b) (by omega) (by omega) hm
  have h1 := hR.eq k
  rw [Pd_of_le (by omega), Pd_of_le le_rfl, Nat.sub_self, hB.q0] at h1
  have := mul_pos ha0 hkb
  linarith [hR.r_le_one k]

/-- If `b ∣ k` (in particular `b = 1`), every branch dies at `n = k`. -/
theorem dies_of_dvd (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hbk : b ≤ k) (hdvd : b ∣ k)
    (hB : IsBranch a b k q r) (hnn : ∀ n < k, 0 ≤ q n) : q k < 0 := by
  have hr0 : r 0 = 1 := by
    have h1 := hB.eq 0
    rw [Pd_of_lt hb, Pd_of_lt (by omega : 0 < k), hB.q0] at h1
    linarith
  refine E1 ha0 ha1 hb hB (s := 0) (by omega) ?_ hr0 hnn
  unfold Nat.ModEq
  rw [Nat.zero_mod, Nat.mod_eq_zero_of_dvd hdvd]

/-! ## Lemma E(b−1) -/

/-- **Lemma E(b−1).** Let `0 < a < 1`. Let `s < k` start the class `t + k ≡ 0 (mod b)`:
`r s = 1` and `r t = 0` for every earlier `t` of that class.  Then a branch that is
nonnegative on `0 … s+k-1` has `q (s + k) < 0`. -/
theorem E_bm1 (ha0 : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hB : IsBranch a b k q r) {s : ℕ}
    (hsk : s < k) (hcls : b ∣ s + k) (hrs : r s = 1)
    (hfirst : ∀ t < s, b ∣ t + k → r t = 0) (hnn : ∀ n < s + k, 0 ≤ q n) :
    q (s + k) < 0 := by
  have hk : 0 < k := by omega
  have hR := hB.toIsRec
  -- earlier members of the class vanish
  have early : ∀ t < s, b ∣ t + k → q t = 0 := fun t ht hd =>
    (hR.partners_zero ha0 hb hk hnn (by omega) (hfirst t ht hd)).1
  -- the class `0 (mod b)` is positive below `s + k`
  have zero_cls : ∀ n, n < s + k → b ∣ n → 0 < q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hd
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [hB.q0]
        norm_num
      · have hbn : b ≤ n := Nat.le_of_dvd hpos hd
        have hd' : b ∣ n - b := (Nat.dvd_sub_iff_left hbn (dvd_refl b)).mpr hd
        have hprev : 0 < q (n - b) := ih (n - b) (by omega) (by omega) hd'
        have hprev1 : q (n - b) ≤ 1 := hR.q_le_one ha0.le hb hk hnn (by omega)
        have hPk : Pd q k n = 0 := by
          unfold Pd
          split_ifs with h
          · apply early (n - k) (by omega)
            rwa [show n - k + k = n by omega]
          · rfl
        have hrn : r n = 1 := by
          apply hR.r_eq_one (hnn n hn)
          rw [Pd_of_le hbn, hPk]
          have := mul_pos ha0 hprev
          linarith
        have h1 := hR.eq n
        rw [hrn, hPk, Pd_of_le hbn] at h1
        have : a * q (n - b) ≤ a := by nlinarith
        linarith
  -- `q s = 1`
  have hqs : q s = 1 := by
    have h1 := hR.eq s
    have hPb : Pd q b s = 0 := by
      unfold Pd
      split_ifs with h
      · apply early (s - b) (by omega)
        exact (Nat.dvd_add_right (dvd_refl b)).mp (by rwa [show b + (s - b + k) = s + k by omega])
      · rfl
    rw [hPb, Pd_of_lt hsk, hrs] at h1
    linarith
  have hbsk : b ≤ s + k := Nat.le_of_dvd (by omega) hcls
  have hd' : b ∣ s + k - b := (Nat.dvd_sub_iff_left hbsk (dvd_refl b)).mpr hcls
  have hpos : 0 < q (s + k - b) := zero_cls (s + k - b) (by omega) hd'
  have h1 := hR.eq (s + k)
  rw [Pd_of_le hbsk, Pd_of_le (by omega), Nat.add_sub_cancel, hqs] at h1
  have := mul_pos ha0 hpos
  linarith [hR.r_le_one (s + k)]

/-! ## Lemma A_b* -/

/-- **Lemma A_b*.** For `1/2 < a < 1`, `0 < b`, `2b < k`: no branch is nonnegative on
`0 … k + 2b`.  (Coprimality of `b, k` is not needed.) -/
theorem A_b_star (hahalf : 1 / 2 < a) (ha1 : a < 1) (hb : 0 < b) (h2b : 2 * b < k)
    (hB : IsBranch a b k q r) : ¬ ∀ n ≤ k + 2 * b, 0 ≤ q n := by
  intro hnn'
  have hnn : ∀ n < k + 2 * b + 1, 0 ≤ q n := fun n hn => hnn' n (by omega)
  have ha0 : 0 < a := by linarith
  have hk : 0 < k := by omega
  have hR := hB.toIsRec
  by_cases hs : ∃ s, s < k ∧ s ≡ k [MOD b] ∧ r s = 1
  · -- (i) the class of `k` starts below `k`: Lemma E1
    obtain ⟨s, hsk, hmod, hrs⟩ := hs
    have := E1 ha0 ha1 hb hB hsk hmod hrs (fun n hn => hnn n (by omega))
    linarith [hnn k (by omega)]
  · -- (ii) the class of `k` is empty below `k`
    push Not at hs
    have hkb : q (k - b) = 0 := by
      have hr : r (k - b) = 0 := by
        rcases hB.r01 (k - b) with h | h
        · exact h
        · refine absurd h (hs (k - b) (by omega) ?_)
          unfold Nat.ModEq
          exact mod_sub_self (by omega)
      exact (hR.partners_zero ha0 hb hk hnn (by omega) hr).1
    -- `q b = 1 - a`
    have hqb : q b = 1 - a := by
      have h1 := hR.eq b
      rw [Pd_of_le le_rfl, Nat.sub_self, hB.q0, Pd_of_lt (by omega : b < k)] at h1
      have := hnn b (by omega)
      rcases hB.r01 b with h | h <;> rw [h] at h1
      · exfalso
        linarith
      · linarith
    -- `q (2b) = 1 - a + a²`
    have hq2b : q (2 * b) = 1 - a + a ^ 2 := by
      have h1 := hR.eq (2 * b)
      rw [Pd_of_le (by omega), show 2 * b - b = b by omega, hqb, Pd_of_lt h2b] at h1
      have := hnn (2 * b) (by omega)
      have hpos : 0 < a * (1 - a) := mul_pos ha0 (by linarith)
      rcases hB.r01 (2 * b) with h | h <;> rw [h] at h1
      · exfalso
        linarith
      · linarith
    -- `q k = 0`
    have hqk : q k = 0 := by
      have h1 := hR.eq k
      rw [Pd_of_le (by omega), hkb, Pd_of_le le_rfl, Nat.sub_self, hB.q0] at h1
      have := hnn k (by omega)
      rcases hB.r01 k with h | h <;> rw [h] at h1
      · exfalso
        linarith
      · linarith
    -- `q (k + b) = a`
    have hqkb : q (k + b) = a := by
      have h1 := hR.eq (k + b)
      rw [Pd_of_le (by omega), Nat.add_sub_cancel, hqk, Pd_of_le (by omega),
        Nat.add_sub_cancel_left, hqb] at h1
      have := hnn (k + b) (by omega)
      rcases hB.r01 (k + b) with h | h <;> rw [h] at h1
      · exfalso
        linarith
      · linarith
    -- `q (k + 2b) ≤ a - 2a² < 0`
    have h1 := hR.eq (k + 2 * b)
    rw [Pd_of_le (by omega), show k + 2 * b - b = k + b by omega, hqkb, Pd_of_le (by omega),
      Nat.add_sub_cancel_left, hq2b] at h1
    have hneg : a * (1 - 2 * a) < 0 := mul_neg_of_pos_of_neg ha0 (by linarith)
    have := hnn (k + 2 * b) (by omega)
    nlinarith [hR.r_le_one (k + 2 * b)]

/-- Lemma A_b* exactly as stated in `ISBOT.md` (with `gcd(b, k) = 1`). -/
theorem A_b_star_coprime (hahalf : 1 / 2 < a) (ha1 : a < 1) (hb : 0 < b) (h2b : 2 * b < k)
    (_hcop : Nat.Coprime b k) (hB : IsBranch a b k q r) : ¬ ∀ n ≤ k + 2 * b, 0 ≤ q n :=
  A_b_star hahalf ha1 hb h2b hB

/-! ## Lemma R(i) : reduction by `d = gcd(b, k)` (sequence form) -/

theorem Pd_scale {q : ℕ → ℝ} {d e i m : ℕ} (hi : i < d) :
    Pd q (d * e) (i + d * m) = Pd (fun m => q (i + d * m)) e m := by
  unfold Pd
  by_cases h : e ≤ m
  · have h1 : d * e ≤ d * m := Nat.mul_le_mul_left d h
    have h2 : d * (m - e) = d * m - d * e := Nat.mul_sub d m e
    have h3 : d * e ≤ i + d * m := by omega
    simp only [h3, h, ite_true]
    congr 1
    omega
  · have h1 : d * (m + 1) ≤ d * e := Nat.mul_le_mul_left d (by omega)
    have h2 : d * (m + 1) = d * m + d := by ring
    have h3 : ¬ d * e ≤ i + d * m := by omega
    simp only [h3, h, ite_false]

/-- **Lemma R(i)** (sequence form).  If `d ∣ b` and `d ∣ k`, then for each residue `i < d`
the subsequence `m ↦ q (i + d m)` satisfies the recursion of `1 + a X^(b/d) + X^(k/d)`
with the same `0/1` right-hand side. -/
theorem R_reduce_residue {d : ℕ} (hd : 0 < d) (hdb : d ∣ b) (hdk : d ∣ k)
    (hR : IsRec a b k q r) {i : ℕ} (hi : i < d) :
    IsRec a (b / d) (k / d) (fun m => q (i + d * m)) (fun m => r (i + d * m)) := by
  obtain ⟨b', rfl⟩ := hdb
  obtain ⟨k', rfl⟩ := hdk
  rw [Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd]
  refine ⟨fun m => hR.r01 _, fun m => ?_⟩
  have := hR.eq (i + d * m)
  rwa [Pd_scale hi, Pd_scale hi] at this

/-- **Lemma R(i)**, residue `0`: the subsequence `m ↦ q (d m)` is again a branch
(with `q 0 = 1`) for `1 + a X^(b/d) + X^(k/d)`, and it inherits nonnegativity. -/
theorem R_reduce {d : ℕ} (hd : 0 < d) (hdb : d ∣ b) (hdk : d ∣ k) (hB : IsBranch a b k q r) :
    IsBranch a (b / d) (k / d) (fun m => q (d * m)) (fun m => r (d * m)) := by
  have h := R_reduce_residue hd hdb hdk hB.toIsRec (i := 0) hd
  simp only [zero_add] at h
  exact ⟨h, by simpa using hB.q0⟩

/-! ## The main branch of `Basic.lean` is a branch -/

/-- The right-hand side `r` of the main branch. -/
noncomputable def mainR (a : ℝ) (b k : ℕ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else if P a b k b n = 0 ∧ P a b k k n = 0 then 0 else 1

theorem P_eq_Pd {a : ℝ} {b k d : ℕ} (hd : 0 < d) (n : ℕ) :
    P a b k d n = Pd (Trinom.q a b k) d n := by
  unfold P Pd
  simp [hd]

theorem main_isBranch (hb : 0 < b) (hk : 0 < k) :
    IsBranch a b k (Trinom.q a b k) (mainR a b k) := by
  refine ⟨⟨fun n => ?_, fun n => ?_⟩, ?_⟩
  · unfold mainR
    split_ifs <;> simp
  · have h := q_unfold a b k n
    rw [P_eq_Pd hb, P_eq_Pd hk] at h
    unfold mainR
    rw [P_eq_Pd hb, P_eq_Pd hk]
    linarith
  · rw [q_unfold, P_of_lt (d := b) hb, P_of_lt (d := k) hk]
    simp

end Trinom.Ogish
