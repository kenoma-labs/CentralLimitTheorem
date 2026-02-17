## Proof of concept: Central Limit Theorem

The first end-to-end output of the pipeline is a complete formalization of the **Lindeberg-Levy Central Limit Theorem** in Lean 4.27.0 / Mathlib v4.27.0.

No `sorry`, `admit`, or `native_decide`. ~830 lines across 4 files. The human provided the proof architecture (characteristic function route, lemma decomposition, which Mathlib API to target). The agent handled all tactic-level proof search, `lake build` iteration, error resolution, and Mathlib API navigation. No human intervention occurred between `./math.sh full` invocations.

Degenne's independent CLT formalization for Mathlib covers the same theorem via a different proof route. The two efforts converging on the same result from different directions — one human-driven for Mathlib contribution, one agent-driven as a capability demonstration — is useful signal that the agent's output is mathematically sound rather than an artifact of overfitting to a single proof strategy.

### Main result

```lean
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
        Real.sqrt (↑n * variance (X 0) P)), ⋯⟩)
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩)
```

For i.i.d. real-valued random variables with finite positive variance, the law of the standardized sum converges weakly to the standard Gaussian.

### Proof structure

| File | Lines | Purpose |
|------|-------|---------|
| `CLT/CharFun/ExpBound.lean` | 125 | Pointwise bounds on `exp(iy) - polynomial` for all real y |
| `CLT/CharFun/Taylor.lean` | 219 | Second-order Taylor expansion of charFun via DCT |
| `CLT/LevyContinuity.lean` | 215 | Levy continuity theorem (both directions) |
| `CLT/CentralLimitTheorem.lean` | 273 | CharFun factorization, power limit, and the CLT |

**Proof chain:** Exponential bounds provide dominators for DCT. Taylor expansion gives `charFun μ t = 1 + i·t·m₁ - t²·m₂/2 + o(t²)`. Levy continuity converts pointwise charFun convergence to weak convergence (forward: tightness via `measureReal_abs_gt_le_integral_charFun`, Prokhorov compactness, `Measure.ext_of_charFun` uniqueness; converse: Portmanteau). The CLT factorizes the charFun of i.i.d. sums as a power, applies Taylor to get `n·(ψ(t/√(nσ²)) - 1) → -t²/2`, takes the n-th power limit via `Complex.tendsto_one_add_pow_exp_of_tendsto`, and lifts through Levy continuity.

### Construction log

The full record of what was proved, what failed, what was retried, and what dead-end approaches were recorded is in [`CONSTRUCTION_LOG.md`](CONSTRUCTION_LOG.md). The negative knowledge accumulated during proving is in [`DOMAIN_CONTEXT.md`](DOMAIN_CONTEXT.md) under `## DOES NOT APPLY`.

## Building the POC

```bash
lake update    # first time only
lake build
```

Requires Lean 4.27.0 (see `lean-toolchain`). Mathlib v4.27.0 is pinned in `lakefile.toml`.

## Theorem inventory

| Declaration | File |
|-------------|------|
| `norm_cexp_mul_I_sub_one_sub_le` | `ExpBound.lean` |
| `norm_cexp_mul_I_sub_one_sub_le_sq` | `ExpBound.lean` |
| `norm_cexp_mul_I_taylor2_le` | `ExpBound.lean` |
| `norm_cexp_mul_I_taylor2_le_cube` | `ExpBound.lean` |
| `charFun_taylor_remainder_isLittleO` | `Taylor.lean` |
| `charFun_taylor_centered` | `Taylor.lean` |
| `charFun_taylor_centered_unit_variance` | `Taylor.lean` |
| `levy_continuity` | `LevyContinuity.lean` |
| `tendsto_charFun_of_tendsto_probabilityMeasure` | `LevyContinuity.lean` |
| `charFun_iid_sum_eq_pow` | `CentralLimitTheorem.lean` |
| `central_limit_theorem_charFun` | `CentralLimitTheorem.lean` |
| `central_limit_theorem` | `CentralLimitTheorem.lean` |

## License

Apache 2.0
