/-
Copyright (c) 2026 Kenoma Labs LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brandon Bell
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.IntegralCharFun

/-!
# Lévy's continuity theorem

We prove the forward direction of Lévy's continuity theorem:
if the characteristic functions of a sequence of probability measures converge pointwise
to the characteristic function of a probability measure, then the sequence converges weakly.

We also prove the easy converse: weak convergence implies charFun convergence.

## Main results

* `levy_continuity` : forward direction (charFun convergence → weak convergence)
* `tendsto_charFun_of_tendsto_probabilityMeasure` : converse (weak → charFun convergence)
-/

open MeasureTheory Filter Topology BoundedContinuousFunction Complex
open scoped ENNReal NNReal

private lemma charFun_continuous_real (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (charFun μ) := by
  show Continuous (fun t ↦ charFun μ t)
  simp_rw [charFun_eq_fourierIntegral]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_probChar
    continuous_inner (integrable_const _)).comp continuous_neg

/-- Tightness of a sequence of probability measures whose charFuns converge pointwise. -/
private lemma isTightMeasureSet_of_charFun_tendsto
    {μₙ : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (μₙ n : Measure ℝ) t) atTop
      (𝓝 (charFun (μ : Measure ℝ) t))) :
    IsTightMeasureSet {((μₙ n : ProbabilityMeasure ℝ) : Measure ℝ) | n : ℕ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal ε' ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hne, (ENNReal.ofReal_toReal hne).le⟩
  -- DCT: for fixed interval, ∫ (1 - charFun (μₙ n)) → ∫ (1 - charFun μ)
  have hDCT : ∀ (a b : ℝ), Tendsto
      (fun n ↦ ∫ t in a..b, ((1 : ℂ) - charFun (↑(μₙ n) : Measure ℝ) t)) atTop
      (𝓝 (∫ t in a..b, ((1 : ℂ) - charFun (↑μ : Measure ℝ) t))) := by
    intro a b
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (2 : ℝ))
    · exact Eventually.of_forall fun n ↦
        (continuous_const.sub (charFun_continuous_real _)).aestronglyMeasurable.restrict
    · exact Eventually.of_forall fun n ↦ ae_of_all _ fun t _ ↦ norm_one_sub_charFun_le_two
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun t _ ↦ (h t).const_sub 1
  -- charFun μ is continuous at 0 with value 1
  have hφ_cont : Continuous (charFun (↑μ : Measure ℝ)) := charFun_continuous_real _
  have hφ_zero : charFun (↑μ : Measure ℝ) 0 = 1 := by
    rw [charFun_zero]; simp [probReal_univ]
  -- By continuity of charFun μ at 0: for ε'/4 > 0, ∃ η > 0, ‖t‖ < η → ‖1 - charFun μ t‖ < ε'/4
  have hcont_norm : ContinuousAt (fun t ↦ ‖(1 : ℂ) - charFun (↑μ : Measure ℝ) t‖) 0 :=
    (continuousAt_const.sub hφ_cont.continuousAt).norm
  have hval_zero : ‖(1 : ℂ) - charFun (↑μ : Measure ℝ) 0‖ = 0 := by rw [hφ_zero]; simp
  obtain ⟨η, hη_pos, hη_bound⟩ := Metric.continuousAt_iff.mp hcont_norm (ε' / 4) (by positivity)
  -- hη_bound: dist t 0 < η → dist ‖1 - charFun μ t‖ 0 < ε'/4
  -- i.e., ‖t‖ < η → |‖1 - charFun μ t‖ - 0| < ε'/4
  -- i.e., ‖t‖ < η → ‖1 - charFun μ t‖ < ε'/4
  replace hη_bound : ∀ t : ℝ, ‖t‖ < η → ‖(1 : ℂ) - charFun (↑μ : Measure ℝ) t‖ < ε' / 4 := by
    intro t ht
    have := hη_bound (by rwa [dist_zero_right])
    rw [hval_zero, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this
  -- Set r₁ > 0 large enough that 2/r₁ < η
  set r₁ := max (4 / η) 1 with hr₁_def
  have hr₁_pos : (0 : ℝ) < r₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2r₁_lt_η : 2 * r₁⁻¹ < η := by
    rw [mul_inv_lt_iff₀ hr₁_pos]
    calc η * r₁ ≥ η * (4 / η) := by gcongr; exact le_max_left _ _
      _ = 4 := by field_simp
      _ > 2 := by norm_num
  -- Integral norm bound for μ: ‖∫ in (-2/r₁, 2/r₁), (1-φ_μ)‖ ≤ ε' * r₁⁻¹
  have hbound_norm_μ : ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
      ((1 : ℂ) - charFun (↑μ : Measure ℝ) t)‖ ≤ ε' * r₁⁻¹ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(2 * r₁⁻¹))
      (b := 2 * r₁⁻¹) (C := ε' / 4) (fun t ht ↦ by
        rw [Set.uIoc_of_le (by have := inv_pos.mpr hr₁_pos; linarith)] at ht
        have ht_norm : ‖t‖ < η := by
          rw [Real.norm_eq_abs, abs_lt]
          constructor <;> linarith [ht.1, ht.2, h2r₁_lt_η]
        exact le_of_lt (hη_bound t ht_norm))
    calc ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
          ((1 : ℂ) - charFun (↑μ : Measure ℝ) t)‖
        ≤ ε' / 4 * |2 * r₁⁻¹ - -(2 * r₁⁻¹)| := this
      _ = ε' / 4 * (4 * r₁⁻¹) := by
          congr 1; rw [show 2 * r₁⁻¹ - -(2 * r₁⁻¹) = 4 * r₁⁻¹ from by ring]
          exact abs_of_pos (by positivity)
      _ = ε' * r₁⁻¹ := by ring
  -- DCT norm convergence: ‖integral_n‖ → ‖integral_μ‖
  have hDCT_norm := (hDCT (-(2 * r₁⁻¹)) (2 * r₁⁻¹)).norm
  -- Get N: for n ≥ N, |‖integral_n‖ - ‖integral_μ‖| < ε' * r₁⁻¹
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hDCT_norm) (ε' * r₁⁻¹) (by positivity)
  -- For n ≥ N: ‖integral_n‖ ≤ ‖integral_μ‖ + ε' * r₁⁻¹ ≤ 2 * ε' * r₁⁻¹
  -- So charFun bound: 2⁻¹ * r₁ * ‖integral_n‖ ≤ 2⁻¹ * r₁ * 2ε'/r₁ = ε'
  -- For n < N: individual tightness
  have hK_fin : ∀ n : Fin N, ∃ K : Set ℝ, IsCompact K ∧ (μₙ n : Measure ℝ) Kᶜ ≤ ε := by
    intro ⟨n, hn⟩
    obtain ⟨K, hK, hKb⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := (μₙ n : Measure ℝ)))) ε hε
    exact ⟨K, hK, hKb _ rfl⟩
  choose K_fin hK_compact hK_bound using hK_fin
  set K := (⋃ i : Fin N, K_fin i) ∪ Metric.closedBall 0 r₁
  refine ⟨K, (isCompact_iUnion fun i ↦ hK_compact i).union (isCompact_closedBall 0 r₁), ?_⟩
  intro μ' hμ'
  obtain ⟨n, rfl⟩ := hμ'
  by_cases hn : n < N
  · -- n < N: Kᶜ ⊆ (K_fin n)ᶜ
    exact le_trans (measure_mono (Set.compl_subset_compl.mpr
      (Set.subset_union_of_subset_left (Set.subset_iUnion _ ⟨n, hn⟩) _))) (hK_bound ⟨n, hn⟩)
  · -- n ≥ N: Kᶜ ⊆ {x | r₁ < ‖x‖}
    push_neg at hn
    have hKc : Kᶜ ⊆ {x : ℝ | r₁ < ‖x‖} := by
      intro x hx
      have : x ∉ Metric.closedBall (0 : ℝ) r₁ :=
        fun h ↦ hx (Set.mem_union_right _ h)
      rwa [Metric.mem_closedBall, dist_zero_right, not_le] at this
    -- (μₙ n) Kᶜ ≤ (μₙ n) {x | r₁ < ‖x‖} ≤ ENNReal.ofReal (measureReal bound) ≤ ε
    have hnorm_abs : (μₙ n : Measure ℝ) {x | r₁ < ‖x‖} =
        (μₙ n : Measure ℝ) {x | r₁ < |x|} := by
      simp only [Real.norm_eq_abs]
    have hmeasReal := measureReal_abs_gt_le_integral_charFun hr₁_pos
      (μ := (μₙ n : Measure ℝ))
    -- Align neg_mul: -2 * r₁⁻¹ = -(2 * r₁⁻¹)
    simp only [neg_mul] at hmeasReal
    calc (μₙ n : Measure ℝ) Kᶜ
        ≤ (μₙ n : Measure ℝ) {x | r₁ < ‖x‖} := measure_mono hKc
      _ = (μₙ n : Measure ℝ) {x | r₁ < |x|} := hnorm_abs
      _ = ENNReal.ofReal ((μₙ n : Measure ℝ).real {x | r₁ < |x|}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (2⁻¹ * r₁ * ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
            ((1 : ℂ) - charFun (↑(μₙ n) : Measure ℝ) t)‖) :=
          ENNReal.ofReal_le_ofReal hmeasReal
      _ ≤ ENNReal.ofReal ε' := by
          apply ENNReal.ofReal_le_ofReal
          have hNn := hN n hn
          rw [Real.dist_eq] at hNn
          have h_norm_bound : ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
              ((1 : ℂ) - charFun (↑(μₙ n) : Measure ℝ) t)‖ ≤ 2 * ε' * r₁⁻¹ :=
            calc ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
                  ((1 : ℂ) - charFun (↑(μₙ n) : Measure ℝ) t)‖
                = ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
                    ((1 : ℂ) - charFun (↑μ : Measure ℝ) t)‖ +
                  (‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
                    ((1 : ℂ) - charFun (↑(μₙ n) : Measure ℝ) t)‖ -
                   ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
                    ((1 : ℂ) - charFun (↑μ : Measure ℝ) t)‖) := by ring
              _ ≤ ε' * r₁⁻¹ + ε' * r₁⁻¹ :=
                  add_le_add hbound_norm_μ (le_of_lt (lt_of_abs_lt hNn))
              _ = 2 * ε' * r₁⁻¹ := by ring
          calc 2⁻¹ * r₁ * ‖∫ t in (-(2 * r₁⁻¹))..(2 * r₁⁻¹),
                ((1 : ℂ) - charFun (↑(μₙ n) : Measure ℝ) t)‖
              ≤ 2⁻¹ * r₁ * (2 * ε' * r₁⁻¹) := by gcongr
            _ = ε' := by field_simp
      _ ≤ ε := hε'_le

/-- **Forward Lévy continuity theorem**: If characteristic functions converge pointwise to
the characteristic function of a probability measure, then the measures converge weakly. -/
theorem levy_continuity
    {μₙ : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (μₙ n : Measure ℝ) t) atTop
      (𝓝 (charFun (μ : Measure ℝ) t))) :
    Tendsto μₙ atTop (𝓝 μ) := by
  have htight := isTightMeasureSet_of_charFun_tendsto h
  have hcompact : IsCompact (closure (Set.range μₙ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1; ext ν; simp [Set.mem_range]
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall fun n ↦ subset_closure (Set.mem_range_self n)
  · intro ν _ hν_cluster
    have hcharFun_eq : charFun (ν : Measure ℝ) = charFun (μ : Measure ℝ) := by
      ext t
      simp_rw [charFun_eq_integral_innerProbChar]
      have hg_cont : Continuous
          (fun ρ : ProbabilityMeasure ℝ ↦ ∫ ω, (innerProbChar t) ω ∂(ρ : Measure ℝ)) := by
        rw [continuous_iff_continuousAt]; intro ρ₀
        exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
          tendsto_id (innerProbChar t)
      have hconv_ν : MapClusterPt
          (∫ ω, (innerProbChar t) ω ∂(ν : Measure ℝ)) atTop
          (fun n ↦ ∫ ω, (innerProbChar t) ω ∂(μₙ n : Measure ℝ)) :=
        hν_cluster.continuousAt_comp hg_cont.continuousAt
      have hconv_μ : Tendsto
          (fun n ↦ ∫ ω, (innerProbChar t) ω ∂(μₙ n : Measure ℝ)) atTop
          (𝓝 (∫ ω, (innerProbChar t) ω ∂(μ : Measure ℝ))) := by
        simp_rw [← charFun_eq_integral_innerProbChar]; exact h t
      -- Use ultrafilter characterization: MapClusterPt gives a sub-ultrafilter converging to ν-val,
      -- and Tendsto gives convergence to μ-val. tendsto_nhds_unique in T2 gives equality.
      rw [mapClusterPt_iff_ultrafilter] at hconv_ν
      obtain ⟨U, hU_le, hU_ν⟩ := hconv_ν
      exact tendsto_nhds_unique hU_ν (hconv_μ.mono_left (map_mono hU_le))
    exact ProbabilityMeasure.toMeasure_injective (Measure.ext_of_charFun hcharFun_eq)

/-- **Converse Lévy continuity theorem**: Weak convergence of probability measures implies
pointwise convergence of characteristic functions. -/
theorem tendsto_charFun_of_tendsto_probabilityMeasure
    {μₙ : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto μₙ atTop (𝓝 μ)) :
    ∀ t : ℝ, Tendsto (fun n ↦ charFun (μₙ n : Measure ℝ) t) atTop
      (𝓝 (charFun (μ : Measure ℝ) t)) := by
  intro t
  simp_rw [charFun_eq_integral_innerProbChar]
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h
    (innerProbChar t)
