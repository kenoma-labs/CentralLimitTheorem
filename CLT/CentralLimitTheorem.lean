/-
Copyright (c) 2026 Kenoma Labs LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brandon Bell
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import CLT.CharFun.Taylor
import CLT.LevyContinuity

/-!
# Central Limit Theorem (Lindeberg-Lévy)

We prove the Lindeberg-Lévy Central Limit Theorem: for i.i.d. random variables with
finite variance, the standardized partial sums converge in distribution to a standard
Gaussian.

## Main results

* `charFun_iid_sum_eq_pow` : charFun of iid sum factorizes as a power
* `central_limit_theorem_charFun` : CLT in terms of characteristic function convergence
* `central_limit_theorem` : CLT as weak convergence of measures

## Proof strategy

The proof follows the classical characteristic function approach:

1. **Factorization**: For iid X₁,...,Xₙ, the characteristic function of Sₙ = ∑ Xᵢ
   factors as φ(t)ⁿ where φ is the common characteristic function. This uses
   `IndepFun.charFun_map_add_eq_mul` and `IdentDistrib`.

2. **Standardization**: The charFun of Zₙ = (Sₙ - nμ)/(σ√n) equals ψ(t/(σ√n))ⁿ
   where ψ is the charFun of the centered distribution X₀ - E[X₀].

3. **Power limit**: Show n·(ψ(t/(σ√n)) - 1) → -t²/2 using the Taylor expansion
   of ψ near 0 (from `CLT.CharFun.Taylor`).

4. **Convergence**: Apply `Complex.tendsto_one_add_pow_exp_of_tendsto` to get
   ψ(t/(σ√n))ⁿ → exp(-t²/2).

5. **Identification**: By `charFun_gaussianReal`, exp(-t²/2) = charFun(gaussianReal 0 1)(t).
-/

open MeasureTheory ProbabilityTheory Filter Complex Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For i.i.d. random variables, the characteristic function of the sum Sₙ = X₁ + ⋯ + Xₙ
equals the n-th power of the common characteristic function.

Proof: by induction on n.
- Base case n = 0: charFun of the zero sum is 1 = φ(t)⁰.
- Inductive step: Sₙ₊₁ = Sₙ + X_{n+1}. By independence of Sₙ and X_{n+1},
  charFun(Sₙ₊₁)(t) = charFun(Sₙ)(t) · charFun(X_{n+1})(t). By IdentDistrib,
  charFun(X_{n+1}) = charFun(X₀). By IH, charFun(Sₙ) = charFun(X₀)ⁿ.
  So charFun(Sₙ₊₁) = charFun(X₀)^{n+1}. -/
theorem charFun_iid_sum_eq_pow
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmeas : ∀ i, AEStronglyMeasurable (X i) P)
    (n : ℕ) (t : ℝ) :
    charFun (P.map (fun ω ↦ ∑ i ∈ Finset.range n, X i ω)) t =
      (charFun (P.map (X 0)) t) ^ n := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero, pow_zero]
    have hmap : P.map (fun _ : Ω ↦ (0 : ℝ)) = Measure.dirac 0 := by
      rw [Measure.map_const, measure_univ, one_smul]
    rw [hmap, charFun_dirac]
    simp
  | succ n ih =>
    rw [pow_succ]
    have hae : ∀ i, AEMeasurable (X i) P := fun i ↦ (hmeas i).aemeasurable
    -- Rewrite: fun ω ↦ ∑ range(n+1) X i ω = (∑ range n, X i) + X n  (Pi-form sum)
    have hfun : (fun ω ↦ ∑ i ∈ Finset.range (n + 1), X i ω) =
        (∑ i ∈ Finset.range n, X i) + X n := by
      ext ω; simp [Finset.sum_range_succ, Finset.sum_apply]
    rw [hfun]
    -- Independence of the partial sum and X n (Pi form matches directly)
    have hindep_n : IndepFun (∑ j ∈ Finset.range n, X j) (X n) P :=
      hindep.indepFun_sum_range_succ₀ hae n
    -- CharFun factorization for independent sums
    have hfact := hindep_n.charFun_map_add_eq_mul
      (Finset.aemeasurable_sum (Finset.range n) (fun i _ ↦ hae i)) (hae n)
    rw [congr_fun hfact t, Pi.mul_apply]
    -- Convert Pi sum back to lambda form for IH, then apply IH
    rw [Finset.sum_fn (Finset.range n) X, ih]
    -- Use IdentDistrib to equate charFun(P.map(X n)) = charFun(P.map(X 0))
    congr 1
    exact congr_arg₂ charFun (hident n).map_eq rfl

/-- **Central Limit Theorem** (characteristic function version).
For i.i.d. real-valued random variables with finite positive variance,
the characteristic function of the standardized sum converges to
the characteristic function of the standard Gaussian.

Proof outline:
1. Let ψ(s) = charFun(P.map(X₀ - E[X₀]))(s) (centered charFun).
2. charFun(P.map Zₙ)(t) = ψ(t/(σ√n))ⁿ (by factorization + scaling + centering).
3. ψ(s) = 1 - σ²s²/2 + o(s²) (Taylor expansion, `charFun_taylor_centered`).
4. n·(ψ(t/(σ√n)) - 1) → -t²/2 (from Taylor + algebra).
5. ψ(t/(σ√n))ⁿ → exp(-t²/2) (by `Complex.tendsto_one_add_pow_exp_of_tendsto`).
6. exp(-t²/2) = charFun(gaussianReal 0 1)(t) (by `charFun_gaussianReal`). -/
theorem central_limit_theorem_charFun
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmeas : ∀ i, AEStronglyMeasurable (X i) P)
    (hL2 : MemLp (X 0) 2 P)
    (hvar : 0 < variance (X 0) P) :
    ∀ t : ℝ, Tendsto
      (fun n ↦ charFun (P.map (fun ω ↦
        (∑ i ∈ Finset.range n, X i ω - ↑n * ∫ x, X 0 x ∂P) /
        Real.sqrt (↑n * variance (X 0) P))) t)
      atTop (𝓝 (charFun (gaussianReal 0 1) t)) := by
  intro t
  set σ2 := variance (X 0) P with hσ2_def
  set μ_X := ∫ x, X 0 x ∂P with hμ_X_def
  -- Step 1: Define the centered charFun ψ
  -- ψ(s) = charFun of the law of (X 0 - μ_X), evaluated at s
  set ψ : ℝ → ℂ := charFun (P.map (fun ω ↦ X 0 ω - μ_X)) with hψ_def
  -- Step 2: Factorization — charFun(Zₙ)(t) = ψ(t/√(nσ²))ⁿ
  -- This follows from charFun_iid_sum_eq_pow + scaling + centering
  have hfact : ∀ n, charFun (P.map (fun ω ↦
      (∑ i ∈ Finset.range n, X i ω - ↑n * μ_X) /
      Real.sqrt (↑n * σ2))) t =
      (ψ (t / Real.sqrt (↑n * σ2))) ^ n := by
    intro n
    -- Set up centered variables Y_i = X_i - μ_X
    set Y : ℕ → Ω → ℝ := fun i ω ↦ X i ω - μ_X
    -- Y_i are iid and measurable
    have hY_indep : iIndepFun Y P :=
      hindep.comp (fun _ ↦ (· - μ_X)) (fun _ ↦ measurable_sub_const μ_X)
    have hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) P P :=
      fun i ↦ (hident i).comp (measurable_sub_const μ_X)
    have hY_meas : ∀ i, AEStronglyMeasurable (Y i) P :=
      fun i ↦ (hmeas i).sub aestronglyMeasurable_const
    -- Measure equality: P.map Z_n = (P.map (∑ Y_i)).map (c * ·)
    have hae : AEMeasurable (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) P := by
      have := Finset.aemeasurable_sum (Finset.range n) (fun i _ ↦ (hY_meas i).aemeasurable)
      rwa [Finset.sum_fn] at this
    have hmap : P.map (fun ω ↦ (∑ i ∈ Finset.range n, X i ω - ↑n * μ_X) /
        Real.sqrt (↑n * σ2)) =
        (P.map (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω)).map
          ((1 / Real.sqrt (↑n * σ2)) * ·) := by
      rw [AEMeasurable.map_map_of_aemeasurable
        (measurable_const_mul _).aemeasurable hae]
      congr 1; funext ω; simp only [Function.comp_apply, Y]
      rw [show ∑ i ∈ Finset.range n, (X i ω - μ_X) =
          ∑ i ∈ Finset.range n, X i ω - ↑n * μ_X from by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
      ring
    rw [hmap, charFun_map_mul, charFun_iid_sum_eq_pow hY_indep hY_ident hY_meas]
    change (ψ (1 / Real.sqrt (↑n * σ2) * t)) ^ n = (ψ (t / Real.sqrt (↑n * σ2))) ^ n
    congr 2; rw [one_div, mul_comm, ← div_eq_mul_inv]
  -- Step 3: Show n · (ψ(t/√(nσ²)) - 1) → -t²/2 using the Taylor expansion
  have hlimit : Tendsto (fun n : ℕ ↦ (↑n : ℂ) * (ψ (t / Real.sqrt (↑n * σ2)) - 1))
      atTop (𝓝 (-(↑t ^ 2 / 2))) := by
    -- Prerequisites for Taylor expansion of ψ
    have hcaem : AEMeasurable (fun ω ↦ X 0 ω - μ_X) P :=
      (hmeas 0).aemeasurable.sub aemeasurable_const
    haveI : IsProbabilityMeasure (P.map (fun ω ↦ X 0 ω - μ_X)) :=
      Measure.isProbabilityMeasure_map hcaem
    have hL2c : MemLp id 2 (P.map (fun ω ↦ X 0 ω - μ_X)) :=
      (memLp_map_measure_iff aestronglyMeasurable_id hcaem).mpr (hL2.sub (memLp_const μ_X))
    have hce : ∫ x, (x : ℝ) ∂(P.map (fun ω ↦ X 0 ω - μ_X)) = 0 := by
      have h := integral_map hcaem aestronglyMeasurable_id
      simp only [id_eq] at h
      rw [h, integral_sub (hL2.integrable one_le_two) (integrable_const μ_X), integral_const]
      simp only [probReal_univ, one_smul]
      exact sub_self _
    have hve : ∫ x, (x : ℝ) ^ 2 ∂(P.map (fun ω ↦ X 0 ω - μ_X)) = σ2 := by
      rw [integral_map hcaem ((continuous_pow 2).aestronglyMeasurable)]
      exact (variance_eq_integral (hmeas 0).aemeasurable).symm
    -- Taylor: ψ(s) - (1 - σ2·s²/2) = o(s²) near 0
    have htaylor := charFun_taylor_centered hL2c hce σ2 hve
    -- sₙ → 0
    have hs : Tendsto (fun n : ℕ ↦ t / Real.sqrt (↑n * σ2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ Real.sqrt (↑n * σ2)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hvar)
      have h2 := tendsto_inv_atTop_zero.comp h1
      rw [show (0 : ℝ) = t * 0 from (mul_zero t).symm]
      exact h2.const_mul t |>.congr fun n ↦ (div_eq_mul_inv t _).symm
    -- n * remainder(sₙ) → 0
    -- Build: n * rem(sₙ) → 0 via mul_isLittleO + trans_isBigO + isLittleO_one_iff
    have hbigO : (fun n : ℕ ↦ (↑n : ℂ) * ((↑(t / Real.sqrt (↑n * σ2)) : ℂ) ^ 2))
        =O[atTop] fun _ ↦ (1 : ℂ) := by
      apply Asymptotics.IsBigO.of_bound ‖(↑t : ℂ) ^ 2 / (↑σ2 : ℂ)‖
      apply Eventually.of_forall; intro n
      simp only [norm_one, mul_one]
      by_cases hn : n = 0
      · subst hn; simp; positivity
      · have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hne : (↑n : ℝ) * σ2 > 0 := mul_pos hn_pos hvar
        -- Compute at ℝ: n * (t/√(nσ2))² = t²/σ2
        have hreal : (↑n : ℝ) * (t / Real.sqrt (↑n * σ2)) ^ 2 = t ^ 2 / σ2 := by
          rw [div_pow, Real.sq_sqrt hne.le]; field_simp
        -- Transfer to ℂ and close
        have hc : (↑n : ℂ) * ((↑(t / Real.sqrt (↑n * σ2)) : ℂ) ^ 2) =
            (↑t : ℂ) ^ 2 / (↑σ2 : ℂ) := by
          have := congr_arg Complex.ofReal hreal; push_cast at this ⊢; exact this
        rw [hc]
    have hrem := (Asymptotics.isLittleO_one_iff (F := ℂ)).mp
      (((Asymptotics.isBigO_refl (fun n : ℕ ↦ (↑n : ℂ)) atTop).mul_isLittleO
        (htaylor.comp_tendsto hs)).trans_isBigO hbigO)
    -- Combine: rem(n) + const → 0 + const = const
    have hsum := hrem.add (tendsto_const_nhds (x := (-((↑t : ℂ) ^ 2 / 2))))
    rw [zero_add] at hsum
    -- Convert: (rem + const)(n) = n*(ψ(sₙ)-1) eventually
    refine (tendsto_congr' ?_).mpr hsum
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    -- Need: n * (ψ(sₙ) - 1) = n * rem(sₙ) + (-(t²/2))
    -- where rem(sₙ) = ψ(sₙ) - (1 - σ2*sₙ²/2)
    -- So: n * (ψ(sₙ) - 1) - n * rem(sₙ) = -(t²/2)
    -- i.e., n * (-σ2*sₙ²/2) = -(t²/2)
    -- i.e., n * σ2 * sₙ² / 2 = t²/2, which holds since n*σ2*sₙ² = t² for n ≥ 1
    have hne : (↑n : ℝ) * σ2 > 0 :=
      mul_pos (Nat.cast_pos.mpr (by omega)) hvar
    simp only [Function.comp, ← hψ_def]
    -- Rewrite s² = t²/(n*σ2) in ℂ
    have hs2 : (↑(t / Real.sqrt ((↑n : ℝ) * σ2)) : ℂ) ^ 2 =
        (↑t : ℂ) ^ 2 / ((↑n : ℂ) * (↑σ2 : ℂ)) := by
      have hreal : (t / Real.sqrt ((↑n : ℝ) * σ2)) ^ 2 = t ^ 2 / ((↑n : ℝ) * σ2) := by
        rw [div_pow, Real.sq_sqrt hne.le]
      have := congr_arg Complex.ofReal hreal; push_cast at this ⊢; exact this
    rw [hs2]
    have hn_ne : (↑n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hσ_ne : (↑σ2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hvar.ne'
    field_simp
    ring
  -- Step 4: Apply power limit theorem
  -- tendsto_one_add_pow_exp_of_tendsto: if n·g(n) → L then (1+g(n))ⁿ → exp(L)
  have hpower : Tendsto (fun n : ℕ ↦ ψ (t / Real.sqrt (↑n * σ2)) ^ n)
      atTop (𝓝 (cexp (-(↑t ^ 2 / 2)))) := by
    have h := Complex.tendsto_one_add_pow_exp_of_tendsto hlimit
    exact h.congr (fun n ↦ by congr 1; ring)
  -- Step 5: Identify target — charFun(gaussianReal 0 1)(t) = cexp(-t²/2)
  have hgauss : charFun (gaussianReal 0 1) t = cexp (-((t : ℂ) ^ 2 / 2)) := by
    rw [charFun_gaussianReal]
    simp only [ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, ofReal_one, one_mul, zero_sub]
  -- Conclude: charFun(Zₙ)(t) = ψ(...)^n for all n, so convergence transfers
  rw [hgauss]
  exact (tendsto_congr (fun n ↦ hfact n)).mpr hpower

/-- **Central Limit Theorem** (Lindeberg-Lévy, weak convergence version).
For i.i.d. real-valued random variables with finite positive variance,
the law of the standardized sum converges weakly to the standard Gaussian. -/
theorem central_limit_theorem
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmeas : ∀ i, AEStronglyMeasurable (X i) P)
    (hL2 : MemLp (X 0) 2 P)
    (hvar : 0 < variance (X 0) P) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ ⟨P.map (fun ω ↦
        (∑ i ∈ Finset.range n, X i ω - ↑n * ∫ x, X 0 x ∂P) /
        Real.sqrt (↑n * variance (X 0) P)), by
          apply Measure.isProbabilityMeasure_map
          have h1 : AEMeasurable (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) P := by
            have := Finset.aemeasurable_sum (Finset.range n)
              (fun i _ ↦ (hmeas i).aemeasurable)
            rwa [Finset.sum_fn] at this
          exact (h1.sub aemeasurable_const).div_const _⟩)
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  exact levy_continuity (central_limit_theorem_charFun hindep hident hmeas hL2 hvar)
