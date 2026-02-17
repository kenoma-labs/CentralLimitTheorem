/-
Copyright (c) 2026 Kenoma Labs LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brandon Bell
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Exponential bounds for characteristic function Taylor expansion

We prove pointwise bounds on `exp(iy) - polynomial` for ALL real `y` (not just `|y| ≤ 1`).
These are used in the dominated convergence argument for the charFun Taylor expansion.

## Main results

* `norm_cexp_mul_I_sub_one_sub_le` : `‖exp(iy) - 1 - iy‖ ≤ y²` for `|y| ≤ 1`
* `norm_cexp_mul_I_sub_one_sub_le_sq` : `‖exp(iy) - 1 - iy‖ ≤ 3 * y²` for all `y`
* `norm_cexp_mul_I_taylor2_le` : `‖exp(iy) - 1 - iy + y²/2‖ ≤ 4 * y²` for all `y`
-/

open Complex

private lemma norm_ofReal_mul_I (y : ℝ) : ‖(y : ℂ) * I‖ = |y| := by
  rw [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]

/-- For `|y| ≤ 1`, `‖exp(iy) - 1 - iy‖ ≤ y²`.
This follows from `norm_exp_sub_one_sub_id_le` applied to `x = y * I`. -/
lemma norm_cexp_mul_I_sub_one_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp (y * I) - 1 - y * I‖ ≤ y ^ 2 := by
  have h1 : ‖(y : ℂ) * I‖ ≤ 1 := by rw [norm_ofReal_mul_I]; exact hy
  calc ‖cexp ((y : ℂ) * I) - 1 - (y : ℂ) * I‖
      ≤ ‖(y : ℂ) * I‖ ^ 2 := norm_exp_sub_one_sub_id_le h1
    _ = y ^ 2 := by rw [norm_ofReal_mul_I, sq_abs]

/-- For all `y : ℝ`, `‖exp(iy) - 1 - iy‖ ≤ 3 * y²`.
Case split: the refined bound for `|y| ≤ 1`, triangle inequality for `|y| > 1`. -/
lemma norm_cexp_mul_I_sub_one_sub_le_sq (y : ℝ) :
    ‖cexp (y * I) - 1 - y * I‖ ≤ 3 * y ^ 2 := by
  by_cases hy : |y| ≤ 1
  · calc ‖cexp (y * I) - 1 - y * I‖
        ≤ y ^ 2 := norm_cexp_mul_I_sub_one_sub_le hy
      _ ≤ 3 * y ^ 2 := le_mul_of_one_le_left (sq_nonneg y) (by norm_num)
  · push_neg at hy
    have ha : 1 ≤ |y| := le_of_lt hy
    calc ‖cexp (y * I) - 1 - y * I‖
        ≤ ‖cexp ((y : ℂ) * I) - 1‖ + ‖(y : ℂ) * I‖ := by
          rw [show cexp (y * I) - 1 - y * I = (cexp ((y : ℂ) * I) - 1) - (y : ℂ) * I from by ring]
          exact norm_sub_le _ _
      _ ≤ 2 + |y| := by
          have h1 : ‖cexp ((y : ℂ) * I) - 1‖ ≤ 2 := by
            calc ‖cexp ((y : ℂ) * I) - 1‖
                ≤ ‖cexp ((y : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_one]
              _ = 2 := by norm_num
          linarith [norm_ofReal_mul_I y]
      _ ≤ 3 * y ^ 2 := by nlinarith [sq_abs y]

/-- For all `y : ℝ`, `‖exp(iy) - 1 - iy + y²/2‖ ≤ 4 * y²`.
This is the global bound used as a dominator in the Taylor expansion proof. -/
lemma norm_cexp_mul_I_taylor2_le (y : ℝ) :
    ‖cexp (y * I) - 1 - y * I + (y ^ 2 / 2 : ℝ)‖ ≤ 4 * y ^ 2 := by
  by_cases hy : |y| ≤ 1
  · -- Small case: use first-order bound and triangle
    calc ‖cexp (y * I) - 1 - y * I + (y ^ 2 / 2 : ℝ)‖
        ≤ ‖cexp (y * I) - 1 - y * I‖ + ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ := by
          rw [show cexp (y * I) - 1 - y * I + (y ^ 2 / 2 : ℝ) =
            (cexp (y * I) - 1 - y * I) + ((y ^ 2 / 2 : ℝ) : ℂ) from by push_cast; ring]
          exact norm_add_le _ _
      _ ≤ y ^ 2 + y ^ 2 / 2 := by
          gcongr
          · exact norm_cexp_mul_I_sub_one_sub_le hy
          · rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ 4 * y ^ 2 := by nlinarith [sq_nonneg y]
  · -- Large case: triangle inequality
    push_neg at hy
    have ha : 1 ≤ |y| := le_of_lt hy
    calc ‖cexp (y * I) - 1 - y * I + (y ^ 2 / 2 : ℝ)‖
        ≤ ‖cexp ((y : ℂ) * I)‖ + ‖(1 : ℂ)‖ + ‖(y : ℂ) * I‖ + ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ := by
          calc ‖cexp (y * I) - 1 - y * I + (y ^ 2 / 2 : ℝ)‖
              ≤ ‖cexp (y * I) - 1 - y * I‖ + ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ := by
                rw [show cexp (y * I) - 1 - y * I + (y ^ 2 / 2 : ℝ) =
                  (cexp (y * I) - 1 - y * I) + ((y ^ 2 / 2 : ℝ) : ℂ) from by push_cast; ring]
                exact norm_add_le _ _
            _ ≤ (‖cexp ((y : ℂ) * I) - 1‖ + ‖(y : ℂ) * I‖) + ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ := by
                gcongr
                rw [show cexp (y * I) - 1 - y * I =
                  (cexp ((y : ℂ) * I) - 1) - (y : ℂ) * I from by ring]
                exact norm_sub_le _ _
            _ ≤ (‖cexp ((y : ℂ) * I)‖ + ‖(1 : ℂ)‖ + ‖(y : ℂ) * I‖) +
                  ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ := by
                gcongr
                linarith [norm_sub_le (cexp ((y : ℂ) * I)) 1]
            _ = _ := by ring
      _ = 2 + |y| + y ^ 2 / 2 := by
          simp only [norm_exp_ofReal_mul_I, norm_one, norm_ofReal_mul_I]
          rw [show ‖((y ^ 2 / 2 : ℝ) : ℂ)‖ = y ^ 2 / 2 from by
            rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
          ring
      _ ≤ 4 * y ^ 2 := by nlinarith [sq_abs y]

/-- For `|y| ≤ 1`, `‖exp(iy) - 1 - iy + y²/2‖ ≤ |y|³`.
This cubic bound is used for the pointwise convergence in the DCT argument
of the charFun Taylor expansion. Follows from `Complex.exp_bound` with `n = 3`. -/
lemma norm_cexp_mul_I_taylor2_le_cube {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp (y * I) - 1 - y * I + (y ^ 2 / 2 : ℝ)‖ ≤ |y| ^ 3 := by
  have hz : ‖(y : ℂ) * I‖ ≤ 1 := by rw [norm_ofReal_mul_I]; exact hy
  -- Apply exp_bound with n = 3: ‖exp z - ∑ₘ<3 zᵐ/m!‖ ≤ ‖z‖³ * (4/(3!·3))
  have hexp := Complex.exp_bound hz (n := 3) (by norm_num : 0 < 3)
  -- ∑ m ∈ range 3, (y*I)^m/m! = 1 + y*I + (y*I)²/2 = 1 + y*I - y²/2
  have hsq : ((y : ℂ) * I) ^ 2 = -((y : ℂ) ^ 2) := by rw [mul_pow, I_sq]; ring
  have hR : cexp ((y : ℂ) * I) - 1 - (y : ℂ) * I + ((y ^ 2 / 2 : ℝ) : ℂ) =
      cexp ((y : ℂ) * I) -
        ∑ m ∈ Finset.range 3, ((y : ℂ) * I) ^ m / ↑(Nat.factorial m) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.mul_one,
      pow_succ, Nat.cast_one, hsq]
    push_cast; ring
  rw [hR]
  calc ‖cexp ((y : ℂ) * I) -
          ∑ m ∈ Finset.range 3, ((y : ℂ) * I) ^ m / ↑(Nat.factorial m)‖
      ≤ ‖(y : ℂ) * I‖ ^ 3 *
          ((↑(Nat.succ 3) : ℝ) * (↑(Nat.factorial 3) * (3 : ℝ))⁻¹) := hexp
    _ = |y| ^ 3 * (4 * (6 * 3)⁻¹) := by
        rw [norm_ofReal_mul_I]; norm_num [Nat.factorial]
    _ ≤ |y| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg y) 3]
