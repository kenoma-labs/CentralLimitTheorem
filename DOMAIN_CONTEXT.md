# Domain Context

Domain knowledge, Mathlib mappings, and notation conventions for this project.

## Domain Description

Probability theory on ℝ: characteristic functions of probability measures, weak convergence, tightness, and the Central Limit Theorem. The formalization covers the Lindeberg-Levy CLT via the classical charFun approach.

## Mathlib Type Mappings

| Domain Concept | Mathlib Type | Module |
|---------------|-------------|--------|
| Probability measure on ℝ | `ProbabilityMeasure ℝ` | `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` |
| Characteristic function | `charFun μ : ℝ → ℂ` | `Mathlib.MeasureTheory.Measure.CharacteristicFunction` |
| Weak convergence | `Tendsto μₙ atTop (𝓝 μ)` on `ProbabilityMeasure ℝ` | `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` |
| Tightness | `IsTightMeasureSet S` | `Mathlib.MeasureTheory.Measure.Tight` |
| Standard Gaussian | `gaussianReal 0 1` | `Mathlib.Probability.Distributions.Gaussian.Real` |
| i.i.d. random variables | `iIndepFun X P` + `IdentDistrib` | `Mathlib.Probability.Independence.Basic` |
| Finite second moment | `MemLp (X 0) 2 P` | `Mathlib.MeasureTheory.Function.LpSeminorm.Defs` |
| Variance | `variance (X 0) P` | `Mathlib.Probability.Moments.Variance` |

## Notation Table

| Symbol | Lean4 | Meaning |
|--------|-------|---------|
| charFun μ t | `charFun μ t` | Characteristic function of μ at t |
| μₙ → μ weakly | `Tendsto μₙ atTop (𝓝 μ)` | Weak convergence of probability measures |
| Zₙ | `(∑ Xᵢ - nμ) / √(nσ²)` | Standardized partial sum |
| o(t²) | `=o[𝓝 0] (fun t ↦ (t : ℂ) ^ 2)` | Little-o as t → 0 |

## Key Mathlib Lemmas

| Lemma | Module | Used For |
|-------|--------|----------|
| `measureReal_abs_gt_le_integral_charFun` | `Measure.IntegralCharFun` | Bound μ.real {x \| r < \|x\|} ≤ 2⁻¹ * r * ‖∫ t in (-2*r⁻¹)..(2*r⁻¹), 1 - charFun μ t‖ |
| `isTightMeasureSet_singleton` | `Measure.Tight` | Any single probability measure on ℝ is tight |
| `isTightMeasureSet_iff_tendsto_measure_norm_gt` | `Measure.TightNormed` | IsTightMeasureSet S ↔ Tendsto (fun r ↦ ⨆ μ ∈ S, μ {x \| r < ‖x‖}) atTop (𝓝 0) |
| `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` | `Measure.Tight` | IsTightMeasureSet S ↔ ∀ ε > 0, ∃ K compact, ∀ μ ∈ S, μ Kᶜ ≤ ε |
| `norm_one_sub_charFun_le_two` | `Measure.CharacteristicFunction` | ‖1 - charFun μ t‖ ≤ 2 for probability measures |
| `charFun_zero` | `Measure.CharacteristicFunction` | charFun μ 0 = μ.real Set.univ |
| `intervalIntegrable_charFun` | `Measure.IntegralCharFun` | charFun is interval integrable |
| `ENNReal.tendsto_atTop_zero` | `Topology.Instances.ENNReal` | Tendsto f atTop (𝓝 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε |
| `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` | `Integral.DominatedConvergence` | DCT for interval integrals |
| `ofReal_measureReal` | `Measure.Real` | ENNReal.ofReal (μ.real s) = μ s (when μ s ≠ ∞) |
| `iSup_le_iff` | `CompleteLattice.Basic` | iSup f ≤ a ↔ ∀ i, f i ≤ a |
| `squeeze_zero` | `MetricSpace.Pseudo.Lemmas` | f ≥ 0 ∧ f ≤ g ∧ g → 0 implies f → 0 |

## Project-Specific Conventions
<!-- Naming conventions, proof style preferences, etc. -->

- Follow Mathlib naming conventions (`snake_case` for definitions, descriptive theorem names)
- Use `namespace` to organize related definitions
- Prefer `structure` over `class` for concrete mathematical objects
- Use Mathlib typeclasses for abstract algebraic structures

## Known Limitations

- The CLT is stated for ℝ-valued random variables only (not ℝⁿ or general Banach spaces)
- The Levy continuity theorem is for ℕ-indexed sequences (not general nets/filters)
- No Berry-Esseen bound (would require third moment and quantitative estimates)
- No Lindeberg condition generalization (only the i.i.d. case)

## Key Proof Patterns

- **ℝ→ℂ transfer pattern**: When `Real.sq_sqrt` or similar ℝ-only lemmas are needed inside a ℂ expression, compute at ℝ level first: `have hreal := ... by rw [div_pow, Real.sq_sqrt hne.le]`, then `have := congr_arg Complex.ofReal hreal; push_cast at this ⊢; exact this`. Avoids `← ofReal_pow` + `sq_sqrt` chain which fails in ℂ context.
- **`integral_div` not `integral_div_const`**: The correct name in Mathlib v4.27.0 is `integral_div`.
- **`probReal_univ` not `measureReal_univ`**: For `μ.real univ = 1` on probability measures.
- **`Eventually.of_forall` not `Filter.eventually_of_forall`**: The latter was removed.
- **`tendsto_natCast_atTop_atTop (R := ℝ)`**: Parameter name is `R`, not `α`.
- **`linarith` does NOT work over ℂ**: Use `exact this` after normalizing with `push_cast`.
- **`field_simp` may close goals completely**: Don't add redundant `ring` after it.

## DOES NOT APPLY
<!-- Record failed approaches here during PROVE phase.
     Each entry should explain WHY the lemma/approach doesn't work.
     This prevents future revision cycles from re-attempting known-bad approaches. -->

- `measureReal_univ`: Unknown identifier in Mathlib v4.27.0. Use `probReal_univ` instead.
- `Filter.eventually_of_forall`: Removed from Mathlib. Use `Eventually.of_forall`.
- `Asymptotics.isBigO_one_iff_isBoundedUnder_le`: Does not exist. Use `Asymptotics.IsBigO.of_bound` constructor instead.
- `integral_div_const`: Unknown. Correct name is `integral_div`.
- `← ofReal_pow` + `Real.sq_sqrt` in ℂ context: Type mismatch because `sq_sqrt` operates on ℝ but expression is already cast to ℂ. Use the `congr_arg Complex.ofReal` transfer pattern above.
- `by_cases hn : (n : ℝ) = 0` then `subst hn`: Cannot subst a coerced variable. Use `by_cases hn : n = 0` (on ℕ) instead, then `subst hn; simp`.
- `linarith` over ℂ: `linarith` only works for linearly ordered types. ℂ is not linearly ordered.
- `nlinarith` with `r₁⁻¹`: `nlinarith` does NOT automatically derive `r₁⁻¹ > 0` from `r₁ > 0`. You must provide the intermediate fact explicitly: `have : 0 < r₁⁻¹ := inv_pos.mpr hr₁_pos` then `nlinarith` or `linarith` can use it.
- `MeasureTheory.Measure.mono`: UNKNOWN in current Mathlib. Search for the actual name — may be `measure_mono` or accessed via `OuterMeasure.mono`.
- `lt_of_not_le`: UNKNOWN. Use `not_le.mp` or `lt_of_not_ge` instead.
