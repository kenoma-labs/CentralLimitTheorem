# Construction Spec: Central Limit Theorem (iid, finite variance)

## Domain

Probability theory on a probability space (Ω, F, P). Real-valued random variables with finite second moments. Characteristic functions of probability measures on ℝ. Weak convergence (convergence in distribution) of probability measures.

## Goal

Prove the Lindeberg–Lévy Central Limit Theorem: if X₁, X₂, ... are iid real-valued random variables with mean μ and variance σ² ∈ (0, ∞), then the standardized partial sums

  Zₙ = (X₁ + ... + Xₙ - n·μ) / (σ·√n)

converge in distribution to the standard normal distribution N(0,1).

In mathlib terms: `TendstoInDistribution Zₙ atTop Z μ` where `Z` has distribution `gaussianReal 0 1`, or equivalently, the pushforward measures `Measure.map Zₙ μ` converge weakly to `gaussianReal 0 1` in the `ProbabilityMeasure ℝ` topology.

This requires two prerequisite results that are not in mathlib:
- (A) Second-order Taylor expansion of characteristic functions
- (B) Lévy's continuity theorem (charFun convergence ↔ weak convergence)

## Required Properties

### P-A: Characteristic Function Taylor Expansion

1. If X is a real random variable with E[|X|²] < ∞, then the characteristic function φ_X(t) = E[e^{itX}] satisfies:
   φ_X(t) = 1 + it·E[X] - t²·E[X²]/2 + o(t²)  as t → 0

   More precisely: for all ε > 0, there exists δ > 0 such that for |t| < δ,
   |φ_X(t) - (1 + it·E[X] - t²·E[X²]/2)| ≤ ε·t²

2. If additionally E[X] = 0 and Var(X) = 1, then:
   φ_X(t) = 1 - t²/2 + o(t²)  as t → 0

### P-B: Lévy Continuity Theorem

3. (Forward direction — sufficient for CLT) Let (μₙ) be a sequence of probability measures on ℝ and μ a probability measure on ℝ. If charFun μₙ t → charFun μ t for all t ∈ ℝ, and charFun μ is continuous at 0 (which is automatic since μ is a probability measure), then μₙ → μ weakly (convergence in distribution).

4. (Converse — desirable but lower priority) If μₙ → μ weakly, then charFun μₙ t → charFun μ t for all t ∈ ℝ.

Note: Property 4 (the converse) is straightforward since charFun is defined as an integral of a bounded continuous function. Property 3 is the hard direction requiring a tightness argument.

### P-C: Central Limit Theorem

5. Let (Ω, F, μ) be a probability space. Let X : ℕ → Ω → ℝ be a family of random variables that are:
   - mutually independent (`iIndepFun` with respect to the Borel σ-algebra on ℝ)
   - identically distributed (`IdentDistrib (X i) (X 0) μ μ` for all i)
   - square-integrable (E[|X₀|²] < ∞, i.e., `Memℒp (X 0) 2 μ`)
   - with positive variance (Var(X₀) > 0)

   Define Sₙ = X₀ + X₁ + ... + X_{n-1} and Zₙ = (Sₙ - n·E[X₀]) / (√(n·Var(X₀))).

   Then Zₙ converges in distribution to a standard normal random variable. That is:
   `Measure.map Zₙ μ` converges weakly to `gaussianReal 0 1`.

6. (CharFun form — intermediate) Under the same hypotheses, for all t ∈ ℝ:
   charFun (Measure.map Zₙ μ) t → exp(-t²/2)  as n → ∞

## Cases & Edge Cases

- **Zero variance**: Var(X₀) = 0 implies X₀ is a.e. constant, so the CLT statement is vacuous. The spec requires Var(X₀) > 0 as a hypothesis. The formalization must not accidentally admit the σ = 0 case.

- **n = 0**: The sum S₀ is empty (= 0). Z₀ involves division by √0 = 0. The formalization should handle this by starting the convergence at n ≥ 1 or using a filter that avoids n = 0.

- **Measurability**: All random variables X i must be measurable. The sum Sₙ must be shown measurable. The standardized Zₙ must be shown measurable. These are routine but must be explicit.

- **Integrability of sums**: E[Sₙ²] < ∞ must be established from iid + finite second moment. This follows from independence + identical distribution.

- **CharFun of sums of independent RVs**: charFun(μ₁ * μ₂) = charFun(μ₁) · charFun(μ₂) for independent RVs. This is a key computational lemma. Mathlib may or may not have this — needs survey. If not, it must be proved.

- **CharFun under affine transformation**: charFun of (aX + b) in terms of charFun of X. Specifically, charFun(Measure.map (fun x => a*x + b) μ) t = e^{ibt} · charFun μ (at). Needed for standardization step.

- **Convergence of (1 + zₙ/n)ⁿ → eᶻ**: The core analytic step. For complex zₙ → z, (1 + zₙ/n)ⁿ → eᶻ. This is standard complex analysis — check if mathlib has it.

## Constraints

- Must NOT use `axiom`, `unsafe`, `native_decide`, or `admit`.
- Must NOT assume decidable equality on ℝ for proof-relevant steps (use classical logic via `Classical.em` or `by_contra` only).
- Must NOT introduce additional type-theoretic assumptions beyond what mathlib provides (no custom universes, no `Inhabited` assumptions that restrict generality).
- The CLT statement should be stated for general `iIndepFun` families, not for product probability spaces. This matches the mathlib convention.
- The Lévy continuity theorem should be stated for probability measures on ℝ (not general metric spaces). Generalization to ℝⁿ or Banach spaces is out of scope.

## Mathlib Dependencies

### Already in mathlib (verified Feb 2026):
- `MeasureTheory.charFun` — characteristic function of a measure (`Mathlib.MeasureTheory.Measure.CharacteristicFunction`)
- `MeasureTheory.charFun_apply` — charFun μ t = ∫ x, exp(⟨x,t⟩ * I) ∂μ
- `MeasureTheory.Measure.ext_of_charFun` — charFun uniquely determines finite measures
- `ProbabilityTheory.IsGaussian` — Gaussian measure class (`Mathlib.Probability.Distributions.Gaussian.Basic`)
- `ProbabilityTheory.charFun_gaussianReal` — charFun of gaussianReal μ v is t ↦ exp(t·μ·I - v·t²/2) (`Mathlib.Probability.Distributions.Gaussian.Real`)
- `MeasureTheory.TendstoInDistribution` — convergence in distribution (`Mathlib.MeasureTheory.Function.ConvergenceInDistribution`)
- `MeasureTheory.TendstoInDistribution.continuous_comp` — continuous mapping theorem
- `MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const` — Slutsky's theorem
- `ProbabilityTheory.iIndepFun` — mutual independence of random variable families (`Mathlib.Probability.Independence.Basic`)
- `ProbabilityTheory.IdentDistrib` — identical distribution (`Mathlib.Probability.IdentDistrib`)
- `MeasureTheory.variance` — variance of a random variable
- `MeasureTheory.Memℒp` — Lp membership (finite p-th moment)
- `ProbabilityTheory.moment`, `ProbabilityTheory.centralMoment` — moments
- `ProbabilityTheory.mgf`, `ProbabilityTheory.complexMGF` — moment generating functions (`Mathlib.Probability.Moments.ComplexMGF`)
- `MeasureTheory.ProbabilityMeasure` — type of probability measures with weak convergence topology (`Mathlib.MeasureTheory.Measure.ProbabilityMeasure`)
- Portmanteau theorem characterizations (`Mathlib.MeasureTheory.Measure.Portmanteau`)
- Lévy-Prokhorov metric (`Mathlib.MeasureTheory.Measure.LevyProkhorovMetric`)
- `Mathlib.Analysis.Calculus.Taylor` — Taylor's theorem for real functions
- `VectorFourier.fourierIntegral` — Fourier transform (`Mathlib.Analysis.Fourier.FourierTransform`)
- Fourier transform differentiability (`Mathlib.Analysis.Fourier.FourierTransformDeriv`)
- Gaussian Fourier transform (`Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`)
- Convolution (`Mathlib.MeasureTheory.Measure.Convolution`)

### Needs verification during SURVEY:
- `charFun` of convolution (product of charFuns for independent RVs)
- `charFun` under affine maps
- `Complex.exp` limit: (1 + z/n)^n → exp(z)
- Tightness / relative compactness of probability measures on ℝ (Prokhorov's theorem is in Isabelle but may not be in mathlib; however, tightness on ℝ can be shown directly via Markov/Chebyshev)
- Dominated convergence for complex exponentials (needed for charFun convergence)

## Success Criteria

- [ ] All required properties P-A through P-C are formalized as Lean4 theorems
- [ ] `lake build` succeeds with zero `sorry` warnings
- [ ] Zero `axiom` declarations
- [ ] Zero `native_decide` usage
- [ ] The main CLT theorem has a clean, standalone statement that a mathematician would recognize
- [ ] The Lévy continuity theorem (forward direction) is stated and proved as a standalone result, reusable beyond CLT
- [ ] The charFun Taylor expansion is stated and proved as a standalone result
- [ ] All intermediate lemmas (charFun of sums, charFun under affine maps, (1+z/n)^n limit) are proved
- [ ] Edge cases (zero variance excluded, n=0 handled) are addressed in the formalization

## Prior Art

- **Isabelle/HOL (2017)**: Avigad, Hölzl, Serafin formalized CLT following Billingsley (Theorem 27.1). The CLT proof itself was ~120 lines; the infrastructure was the heavy part. They used characteristic functions, Lévy's continuity theorem, and the Helly selection theorem.
- **Mathlib Zulip**: Discussion of Lévy continuity requiring "a tightness argument (at least Helly's selection theorem) and some Fourier analysis of measures (Lévy's inversion theorem)." Portmanteau theorem work by Kytölä preceded current mathlib version. No known WIP on CLT or Lévy continuity in mathlib as of early 2025.

## Proof Strategy Notes (for CONSTRUCT phase)

The standard characteristic function approach (Billingsley §27):

1. WLOG reduce to E[X] = 0, Var(X) = 1 by centering and scaling.
2. Show charFun of Zₙ = φ(t/√n)ⁿ where φ is the common charFun.
3. Use Taylor expansion: φ(t/√n) = 1 - t²/(2n) + o(t²/n).
4. Therefore φ(t/√n)ⁿ = (1 - t²/(2n) + o(1/n))ⁿ → e^{-t²/2}.
5. e^{-t²/2} = charFun(gaussianReal 0 1).
6. By Lévy continuity, Zₙ →_d N(0,1).

For Lévy continuity on ℝ (the hard prerequisite):
- Show the sequence (Measure.map Zₙ μ) is tight using Chebyshev's inequality + finite variance.
- Every subsequence has a further subsequence converging weakly (tightness on ℝ = Prokhorov via Helly for CDFs).
- The limit is uniquely determined by the charFun limit (via `Measure.ext_of_charFun`).
- Therefore the full sequence converges.

Alternative: avoid full Prokhorov by using the direct tightness characterization on ℝ via CDFs + diagonal extraction (Helly's selection theorem for monotone functions, which is a relatively straightforward compactness argument on ℝ).
