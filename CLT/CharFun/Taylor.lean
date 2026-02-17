/-
Copyright (c) 2026 Kenoma Labs LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenoma Labs
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.Variance
import CLT.CharFun.ExpBound

/-!
# Second-order Taylor expansion of characteristic functions

For a probability measure `μ` on `ℝ` with finite second moment, we prove:
  `charFun μ t = 1 + i·t·m₁ - t²·m₂/2 + o(t²)`
where `m₁ = ∫ x dμ` and `m₂ = ∫ x² dμ`.

## Main results

* `charFun_taylor_remainder_isLittleO` : general second-order expansion
* `charFun_taylor_centered_unit_variance` : simplified for centered, unit-variance measures
-/

open MeasureTheory Complex Filter Asymptotics Topology
open scoped ComplexConjugate

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The second-order Taylor expansion of the characteristic function.
For a probability measure with finite second moment:
  `charFun μ t - (1 + i·t·m₁ - t²·m₂/2) = o(t²)` as `t → 0`
where `m₁ = ∫ x dμ` and `m₂ = ∫ x² dμ`. -/
theorem charFun_taylor_remainder_isLittleO
    (hL2 : MemLp id 2 μ) :
    (fun t : ℝ ↦ charFun μ t - (1 + I * t * ∫ x, (x : ℂ) ∂μ
      - t ^ 2 / 2 * ∫ x, (x : ℂ) ^ 2 ∂μ)) =o[𝓝 0] (fun t ↦ (t : ℂ) ^ 2) := by
  -- Integrability prerequisites from MemLp id 2 μ
  have hL1 : Integrable id μ := hL2.integrable one_le_two
  -- Decomposition: charFun μ t - poly = ∫ R(t, ·) dμ
  -- where R(t,x) = exp(itx) - 1 - itx + (tx)²/2
  have hdiff : ∀ t : ℝ, charFun μ t - (1 + I * ↑t * ∫ x, (↑x : ℂ) ∂μ
      - ↑t ^ 2 / 2 * ∫ x, (↑x : ℂ) ^ 2 ∂μ) =
      ∫ x : ℝ, (cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I +
        (↑(t * x) ^ 2 / 2 : ℂ)) ∂μ := by
    intro t
    -- Integrability of individual terms
    have hi_exp : Integrable (fun x : ℝ ↦ cexp (↑t * ↑x * I)) μ := by
      apply Integrable.mono' (integrable_const (1 : ℝ))
      · exact (((continuous_const.mul continuous_ofReal).mul
            continuous_const).cexp).aestronglyMeasurable
      · exact ae_of_all _ fun x ↦ by
          rw [show (↑t : ℂ) * (↑x : ℂ) * I = ↑(t * x) * I from by push_cast; ring]
          rw [norm_exp_ofReal_mul_I]
    have hi_lin : Integrable (fun x : ℝ ↦ (↑t * ↑x * I : ℂ)) μ := by
      have h1 : Integrable (fun x : ℝ ↦ (x : ℂ)) μ := hL1.ofReal
      exact (h1.const_mul (↑t * I)).congr (ae_of_all _ fun x ↦ by push_cast; ring)
    have hi_sq : Integrable (fun x : ℝ ↦ (↑(t * x) ^ 2 / 2 : ℂ)) μ := by
      have h1 : Integrable (fun x : ℝ ↦ (x : ℝ) ^ 2) μ := hL2.integrable_sq
      have h2 : Integrable (fun x : ℝ ↦ ((x ^ 2 : ℝ) : ℂ)) μ := h1.ofReal
      exact (h2.const_mul (↑t ^ 2 / 2)).congr (ae_of_all _ fun x ↦ by push_cast; ring)
    -- Rewrite charFun as integral
    rw [charFun_apply_real]
    -- Express polynomial terms as integrals
    -- 1 = ∫ 1 dμ (probability measure)
    have h_const : ∫ _ : ℝ, (1 : ℂ) ∂μ = 1 := by
      simp [integral_const, probReal_univ]
    -- I*t*∫ x = ∫ t*x*I (pull constant out)
    have h_lin : ∫ x : ℝ, (↑t * ↑x * I : ℂ) ∂μ = I * ↑t * ∫ x : ℝ, (↑x : ℂ) ∂μ := by
      simp_rw [show ∀ x : ℝ, (↑t * ↑x * I : ℂ) = (↑t * I : ℂ) * (↑x : ℂ) from
        fun x ↦ by ring]
      rw [integral_const_mul]; ring
    -- t²/2*∫ x² = ∫ (tx)²/2 (pull constant out)
    have h_sq : ∫ x : ℝ, (↑(t * x) ^ 2 / 2 : ℂ) ∂μ =
        ↑t ^ 2 / 2 * ∫ x : ℝ, (↑x : ℂ) ^ 2 ∂μ := by
      simp_rw [show ∀ x : ℝ, (↑(t * x) ^ 2 / 2 : ℂ) =
        (↑t ^ 2 / 2 : ℂ) * ((↑x : ℂ) ^ 2) from fun x ↦ by push_cast; ring]
      rw [integral_const_mul]
    -- Split the integral: ∫ (f - 1 - g + h) = ∫ f - ∫ 1 - ∫ g + ∫ h
    -- Approach: rewrite the combined integrand as explicit function arithmetic,
    -- then use integral_add/sub to decompose, then substitute h_const/h_lin/h_sq.
    -- First, rewrite the integrand pointwise to expose Pi.add / Pi.sub structure
    have hi_comb : Integrable (fun x : ℝ ↦ cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I +
        (↑(t * x) ^ 2 / 2 : ℂ)) μ :=
      ((hi_exp.sub (integrable_const (1 : ℂ))).sub hi_lin).add hi_sq
    -- Compute the integral by splitting
    have h_split_add := integral_add ((hi_exp.sub (integrable_const (1 : ℂ))).sub hi_lin) hi_sq
    have h_split_sub1 := integral_sub (hi_exp.sub (integrable_const (1 : ℂ))) hi_lin
    have h_split_sub2 := integral_sub hi_exp (integrable_const (1 : ℂ))
    -- Beta-reduce Pi.sub_apply / Pi.add_apply in the split lemmas
    simp only [Pi.sub_apply] at h_split_add h_split_sub1
    -- Now use the beta-reduced split lemmas to decompose the integral
    have h_eq_add : ∫ x : ℝ, (cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I +
        (↑(t * x) ^ 2 / 2 : ℂ)) ∂μ =
      ∫ x : ℝ, cexp (↑t * ↑x * I) ∂μ - ∫ _ : ℝ, (1 : ℂ) ∂μ -
        ∫ x : ℝ, (↑t * ↑x * I : ℂ) ∂μ + ∫ x : ℝ, (↑(t * x) ^ 2 / 2 : ℂ) ∂μ := by
      rw [← h_split_sub2, ← h_split_sub1, ← h_split_add]
    rw [h_eq_add, h_const, h_lin, h_sq]; ring
  -- Use isLittleO_of_tendsto
  apply Asymptotics.isLittleO_of_tendsto
  · -- When (t : ℂ)² = 0, LHS = 0
    intro t ht
    simp only [sq_eq_zero_iff, ofReal_eq_zero] at ht; subst ht
    simp
  · -- Tendsto (LHS/t²) → 0 via DCT
    -- Rewrite using decomposition + pull division inside integral
    have hcongr : ∀ t : ℝ, (charFun μ t - (1 + I * ↑t * ∫ x, (↑x : ℂ) ∂μ
        - ↑t ^ 2 / 2 * ∫ x, (↑x : ℂ) ^ 2 ∂μ)) / (↑t : ℂ) ^ 2 =
        ∫ x : ℝ, (cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I +
          (↑(t * x) ^ 2 / 2 : ℂ)) / (↑t : ℂ) ^ 2 ∂μ := by
      intro t; rw [hdiff, integral_div]
    simp_rw [hcongr]
    -- Apply DCT with limit function 0 and dominator 4x²
    rw [show (0 : ℂ) = ∫ _ : ℝ, (0 : ℂ) ∂μ from by simp]
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ 4 * x ^ 2)
    · -- AEStronglyMeasurable for each t
      apply Eventually.of_forall; intro t
      exact ((((continuous_const.mul continuous_ofReal).mul
        continuous_const).cexp.sub continuous_const |>.sub
        ((continuous_const.mul continuous_ofReal).mul
        continuous_const) |>.add
        (((continuous_ofReal.comp
        (continuous_const.mul continuous_id)).pow 2).div_const
        _)).div_const _).aestronglyMeasurable
    · -- Bound: ‖R(t,x)/t²‖ ≤ 4x² a.e. for all t
      apply Eventually.of_forall; intro t
      apply ae_of_all; intro x
      by_cases ht : t = 0
      · subst ht
        simp only [ofReal_zero, zero_mul, Complex.exp_zero, sub_self, zero_add]
        norm_num [sq_nonneg]
      · rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs]
        have hbound : ‖cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I + (↑(t * x) ^ 2 / 2 : ℂ)‖
            ≤ 4 * (t * x) ^ 2 := by
          have h := norm_cexp_mul_I_taylor2_le (t * x)
          simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_ofNat] at h
          convert h using 2
          push_cast; ring
        calc ‖cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I + (↑(t * x) ^ 2 / 2 : ℂ)‖ / |t| ^ 2
            ≤ 4 * (t * x) ^ 2 / |t| ^ 2 :=
              div_le_div_of_nonneg_right hbound (sq_nonneg |t|)
          _ = 4 * x ^ 2 := by
              rw [mul_pow, sq_abs]
              have : |t| ≠ 0 := abs_ne_zero.mpr ht
              field_simp
    · -- 4x² integrable
      exact hL2.integrable_sq.const_mul 4
    · -- Pointwise: R(t,x)/t² → 0 a.e. as t → 0
      apply ae_of_all; intro x
      by_cases hx : x = 0
      · simp [hx]
      · rw [Metric.tendsto_nhds]
        intro ε hε
        have hxpos : (0 : ℝ) < |x| := abs_pos.mpr hx
        have hxcube : (0 : ℝ) < |x| ^ 3 := by positivity
        have hδ : (0 : ℝ) < min (|x|⁻¹) (ε / |x| ^ 3) :=
          lt_min (inv_pos.mpr hxpos) (div_pos hε hxcube)
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
        simp only [dist_zero_right]
        by_cases ht0 : t = 0
        · subst ht0; simp; exact hε
        · have htx : |t * x| ≤ 1 := by
            rw [abs_mul]
            calc |t| * |x| ≤ |x|⁻¹ * |x| :=
                  mul_le_mul_of_nonneg_right
                    (le_of_lt (lt_of_lt_of_le ht (min_le_left _ _))) (abs_nonneg x)
              _ = 1 := inv_mul_cancel₀ (ne_of_gt hxpos)
          rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs]
          have hcube : ‖cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I + (↑(t * x) ^ 2 / 2 : ℂ)‖
              ≤ |t * x| ^ 3 := by
            have h := norm_cexp_mul_I_taylor2_le_cube htx
            simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_ofNat] at h
            convert h using 2
            push_cast; ring
          calc ‖cexp (↑t * ↑x * I) - 1 - ↑t * ↑x * I + (↑(t * x) ^ 2 / 2 : ℂ)‖ / |t| ^ 2
              ≤ |t * x| ^ 3 / |t| ^ 2 :=
                div_le_div_of_nonneg_right hcube (sq_nonneg |t|)
            _ = |t| * |x| ^ 3 := by
                rw [abs_mul, mul_pow]
                have : |t| ≠ 0 := abs_ne_zero.mpr ht0
                field_simp
            _ < ε := by
                calc |t| * |x| ^ 3
                    < (ε / |x| ^ 3) * |x| ^ 3 :=
                      mul_lt_mul_of_pos_right
                        (lt_of_lt_of_le ht (min_le_right _ _)) hxcube
                  _ = ε := div_mul_cancel₀ ε (ne_of_gt hxcube)

/-- The Taylor expansion for a centered measure with variance σ².
If `∫ x dμ = 0` and `∫ x² dμ = σ²`, then:
  `charFun μ t - (1 - σ²·t²/2) = o(t²)` as `t → 0` -/
theorem charFun_taylor_centered
    (hL2 : MemLp id 2 μ)
    (hcenter : ∫ x, (x : ℝ) ∂μ = 0)
    (σ2 : ℝ) (hvar : ∫ x, (x : ℝ) ^ 2 ∂μ = σ2) :
    (fun t : ℝ ↦ charFun μ t - (1 - σ2 * t ^ 2 / 2)) =o[𝓝 0] (fun t ↦ (t : ℂ) ^ 2) := by
  have hm1 : (∫ x, (x : ℂ) ∂μ) = 0 := by
    have h1 : ∫ x : ℝ, (x : ℂ) ∂μ = (↑(∫ x : ℝ, x ∂μ) : ℂ) := integral_ofReal
    rw [h1, hcenter, Complex.ofReal_zero]
  have hm2 : (∫ x, (x : ℂ) ^ 2 ∂μ) = (σ2 : ℂ) := by
    have h2 : (fun x : ℝ => (x : ℂ) ^ 2) = (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) :=
      funext fun x ↦ by push_cast; ring
    rw [h2]
    have h3 : ∫ x : ℝ, ((x ^ 2 : ℝ) : ℂ) ∂μ = (↑(∫ x : ℝ, x ^ 2 ∂μ) : ℂ) := integral_ofReal
    rw [h3, hvar]
  have h := charFun_taylor_remainder_isLittleO hL2
  exact h.congr_left (fun t ↦ by simp only [hm1, hm2]; ring)

/-- Simplified Taylor expansion for a centered measure with unit variance.
If `∫ x dμ = 0` and `∫ x² dμ = 1`, then:
  `charFun μ t - (1 - t²/2) = o(t²)` as `t → 0` -/
theorem charFun_taylor_centered_unit_variance
    (hL2 : MemLp id 2 μ)
    (hcenter : ∫ x, (x : ℝ) ∂μ = 0)
    (hvar : ∫ x, (x : ℝ) ^ 2 ∂μ = 1) :
    (fun t : ℝ ↦ charFun μ t - (1 - t ^ 2 / 2)) =o[𝓝 0] (fun t ↦ (t : ℂ) ^ 2) := by
  exact (charFun_taylor_centered hL2 hcenter 1 hvar).congr_left
    (fun t ↦ by push_cast; ring)
