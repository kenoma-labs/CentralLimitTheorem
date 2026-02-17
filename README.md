# Central Limit Theorem (Lindeberg-Levy) — Lean 4 Formalization

A complete formalization of the **Lindeberg-Levy Central Limit Theorem** in Lean 4 / Mathlib.
Zero sorry, zero axiom, ~830 lines across 4 files.

## Main Result

For i.i.d. real-valued random variables with finite positive variance, the law of the
standardized sum converges weakly to the standard Gaussian:

```lean
theorem central_limit_theorem
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmeas : ∀ i, AEStronglyMeasurable (X i) P)
    (hL2 : MemLp (X 0) 2 P)
    (hvar : 0 < variance (X 0) P) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n ↦ ⟨P.map Zₙ, ...⟩)
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩)
```

where `Zₙ = (∑ Xᵢ - n * E[X₀]) / √(n * Var(X₀))`.

## Structure

The proof follows the classical characteristic function approach:

| File | Lines | Contents |
|------|-------|----------|
| `CLT/CharFun/ExpBound.lean` | 125 | Pointwise bounds on `exp(iy) - polynomial` for all real y |
| `CLT/CharFun/Taylor.lean` | 219 | Second-order Taylor expansion of charFun via DCT |
| `CLT/LevyContinuity.lean` | 215 | Levy continuity theorem (both directions) |
| `CLT/CentralLimitTheorem.lean` | 273 | CharFun factorization, power limit, and the CLT |

### Proof outline

1. **Exponential bounds** (`ExpBound`): `‖exp(iy) - 1 - iy + y²/2‖ ≤ 4y²` (global) and `≤ |y|³` (local). These serve as dominators for DCT arguments.

2. **CharFun Taylor expansion** (`Taylor`): For a probability measure with finite second moment, `charFun μ t = 1 + i·t·m₁ - t²·m₂/2 + o(t²)`. Proved via DCT with the exponential bounds as dominator.

3. **Levy continuity** (`LevyContinuity`): Pointwise charFun convergence implies weak convergence. The forward direction uses tightness (via `measureReal_abs_gt_le_integral_charFun`), compactness of tight families (Prokhorov), and charFun uniqueness. The converse follows from the Portmanteau theorem.

4. **Central Limit Theorem** (`CentralLimitTheorem`): CharFun of iid sums factorizes as a power (by induction). The Taylor expansion gives `n · (ψ(t/√(nσ²)) - 1) → -t²/2`. The power limit theorem yields `ψ(t/√(nσ²))ⁿ → exp(-t²/2) = charFun(gaussianReal 0 1)(t)`. Levy continuity upgrades this to weak convergence.

## All theorems

| Theorem | File |
|---------|------|
| `norm_cexp_mul_I_sub_one_sub_le` | `CLT/CharFun/ExpBound.lean` |
| `norm_cexp_mul_I_sub_one_sub_le_sq` | `CLT/CharFun/ExpBound.lean` |
| `norm_cexp_mul_I_taylor2_le` | `CLT/CharFun/ExpBound.lean` |
| `norm_cexp_mul_I_taylor2_le_cube` | `CLT/CharFun/ExpBound.lean` |
| `charFun_taylor_remainder_isLittleO` | `CLT/CharFun/Taylor.lean` |
| `charFun_taylor_centered` | `CLT/CharFun/Taylor.lean` |
| `charFun_taylor_centered_unit_variance` | `CLT/CharFun/Taylor.lean` |
| `levy_continuity` | `CLT/LevyContinuity.lean` |
| `tendsto_charFun_of_tendsto_probabilityMeasure` | `CLT/LevyContinuity.lean` |
| `charFun_iid_sum_eq_pow` | `CLT/CentralLimitTheorem.lean` |
| `central_limit_theorem_charFun` | `CLT/CentralLimitTheorem.lean` |
| `central_limit_theorem` | `CLT/CentralLimitTheorem.lean` |

## Building

Requires Lean 4.27.0 and Mathlib v4.27.0.

```bash
# Install dependencies (first time only)
lake update

# Build
lake build
```

## Verification

```bash
# Zero sorry
grep -rn '\bsorry\b' CLT/ --include='*.lean'

# Zero axiom/unsafe/admit
grep -rn '\baxiom\b\|\bunsafe\b\|\badmit\b\|\bnative_decide\b' CLT/ --include='*.lean'
```

## Key Mathlib dependencies

- `Mathlib.MeasureTheory.Measure.CharacteristicFunction` (charFun, ext_of_charFun)
- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` (weak convergence topology)
- `Mathlib.MeasureTheory.Measure.Prokhorov` (tight families are compact)
- `Mathlib.MeasureTheory.Measure.IntegralCharFun` (Fourier tail bound)
- `Mathlib.Probability.Independence.CharacteristicFunction` (charFun factorization)
- `Mathlib.Probability.Distributions.Gaussian.Real` (charFun_gaussianReal)

## License

Apache 2.0
