# Construction Spec: Lévy Continuity Theorem (on ℝ)

## Domain
Weak convergence of probability measures on ℝ. Characteristic functions. Tightness.

## Goal
Prove Lévy's continuity theorem for probability measures on ℝ: pointwise convergence of characteristic functions is equivalent to weak convergence of the underlying measures. The forward direction (charFun convergence implies weak convergence) is the critical result needed for the CLT.

## Required Properties

### Core theorem (forward direction — CLT-critical)

1. **Lévy continuity, forward**: Let (μₙ) be a sequence of probability measures on ℝ and μ a probability measure on ℝ. If for all t ∈ ℝ:
   charFun μₙ t → charFun μ t   as n → ∞,
   then μₙ → μ in the weak convergence topology (convergence in distribution).

   Mathlib phrasing: If for all t, `Filter.Tendsto (fun n => charFun (μₙ n) t) atTop (nhds (charFun μ t))`, then `μₙ n` tends to `μ` in `ProbabilityMeasure ℝ`.

### Converse (lower priority, but completes the equivalence)

2. **Lévy continuity, converse**: If μₙ → μ weakly, then charFun μₙ t → charFun μ t for all t ∈ ℝ.

### Supporting results (needed for the forward direction)

3. **Tightness from charFun convergence**: If charFun μₙ t → φ(t) pointwise, and φ is continuous at 0, then the family {μₙ} is tight.

   Specifically: for all ε > 0, there exists K > 0 such that μₙ([-K, K]) ≥ 1 - ε for all n.

   The standard proof uses the identity:
   (1/2T) ∫_{-T}^{T} charFun μ t dt = μ({0}) for Dirac, and more generally bounds μ([-K,K]^c) using charFun.

4. **Helly's selection theorem on ℝ**: Every sequence of probability measures on ℝ that is tight has a weakly convergent subsequence.

   On ℝ, this reduces to: every uniformly bounded sequence of right-continuous non-decreasing functions has a pointwise convergent subsequence (on a dense set), and the limit determines a measure.

   Note: This might already be partially available through mathlib's Lévy-Prokhorov metric + compactness results. Check during SURVEY whether `IsCompact` or `TotallyBounded` results for `ProbabilityMeasure ℝ` under tight families are available.

5. **CharFun determines the measure** (already in mathlib): `Measure.ext_of_charFun` — if charFun μ = charFun ν for finite measures μ, ν, then μ = ν.

## Cases & Edge Cases

- **Degenerate limit**: μ is a Dirac mass. CharFun is exp(i·c·t). Must work.
- **Oscillating charFuns**: If charFun μₙ t → φ(t) but φ is NOT continuous at 0, the sequence is not tight and no probability measure limit exists. The theorem's hypothesis excludes this by assuming the limit IS a charFun of a probability measure (so continuity at 0 is automatic since charFun μ 0 = 1 for probability measures, and charFun of probability measures is continuous everywhere).
- **Non-probability finite measures**: The theorem is stated for probability measures. Do not generalize to arbitrary finite measures (the normalization matters for tightness).
- **ℝ vs ℝⁿ**: We restrict to ℝ. The proof on ℝ is significantly simpler than the general Banach space case because CDF-based arguments work.

## Constraints

- The forward direction (Property 1) is essential. The converse (Property 2) is highly desirable but can be deferred.
- The proof of Property 1 should follow the standard route: tightness → subsequential convergence → unique limit via charFun uniqueness → full convergence.
- Avoid Prokhorov's theorem in full generality (which requires Riesz-Markov-Kakutani). On ℝ, Helly's selection theorem suffices and is much simpler.
- The tightness estimate (Property 3) is the key technical lemma. The standard proof uses:
  ∫_{-T}^{T} (1 - charFun μ t) dt relates to μ of tails via Fourier inversion-type identities.

## Mathlib Dependencies

- `MeasureTheory.charFun`, `Measure.ext_of_charFun`
- `MeasureTheory.ProbabilityMeasure` with weak convergence topology
- Portmanteau theorem (`Mathlib.MeasureTheory.Measure.Portmanteau`)
- `MeasureTheory.Measure.IsProbabilityMeasure`
- `Filter.Tendsto`, `Filter.atTop`
- `TopologicalSpace.IsCompact` — for compactness arguments on bounded intervals
- `MeasureTheory.integral` over bounded intervals (`set_integral`)
- Fubini's theorem (for swapping integral order in tightness proof)
- `Mathlib.MeasureTheory.Measure.LevyProkhorovMetric` — may provide useful infrastructure

### Needs SURVEY verification:
- Whether mathlib has `IsTight` or equivalent for families of measures
- Whether Helly's selection theorem (for CDFs) exists in any form
- Whether `Measure.CDF` exists and has relevant compactness properties
- Whether `LevyProkhorov` metric provides Prokhorov's theorem or just the metric

## Success Criteria

- [ ] Property 1 (forward Lévy continuity) formalized and proved
- [ ] Property 2 (converse) formalized and proved, OR explicitly scoped out with a TODO
- [ ] Property 3 (tightness from charFun convergence) proved as a standalone lemma
- [ ] `lake build` succeeds with zero `sorry`
- [ ] Zero `axiom` declarations
- [ ] The theorem is stated using `ProbabilityMeasure ℝ` and its weak convergence topology, compatible with mathlib conventions
- [ ] The tightness machinery is reusable (not inlined into the Lévy continuity proof)

## Proof Strategy Notes (for CONSTRUCT phase)

The standard proof of Property 1 (Billingsley §26, or Durrett §3.3):

**Step A: Tightness.** For a probability measure μ on ℝ and T > 0:
  μ({x : |x| > 2/T}) ≤ (1/T) ∫₀ᵀ (1 - Re(charFun μ t)) dt

If charFun μₙ → charFun μ pointwise, and charFun μ is continuous at 0 (which holds for probability measures), then the right side can be made small uniformly in n for large enough T.

**Step B: Subsequential limits.** By Helly's theorem (tightness on ℝ), every subsequence of (μₙ) has a further subsequence converging weakly to some probability measure ν.

**Step C: Limit identification.** Since charFun is continuous under weak convergence (this is Property 2, the easy direction — charFun is a bounded continuous function integral), the weakly convergent subsequence satisfies charFun ν = lim charFun μₙ = charFun μ. By uniqueness (`Measure.ext_of_charFun`), ν = μ.

**Step D: Full convergence.** Every subsequence has a further subsequence converging to μ. This implies the full sequence converges to μ.

The converse (Property 2) follows because t ↦ exp(i·x·t) is a bounded continuous function of x for each fixed t, so ∫ exp(i·x·t) dμₙ → ∫ exp(i·x·t) dμ by the definition of weak convergence (Portmanteau).
