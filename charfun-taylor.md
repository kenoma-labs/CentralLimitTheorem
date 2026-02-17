# Construction Spec: Characteristic Function Taylor Expansion

## Domain
Characteristic functions of probability measures on ℝ with finite second moments. Taylor approximation of charFun near zero.

## Goal
Prove that the characteristic function of a measure with finite second moment admits a second-order Taylor expansion at t = 0 in terms of the first two moments. This is the computational engine of the CLT proof.

## Required Properties

1. **Second-order expansion with moment terms**: Let μ be a probability measure on ℝ with finite second moment (∫ x², dμ < ∞). Then for all t ∈ ℝ:

   charFun μ t = 1 + i·t·(∫ x dμ) - t²/2 · (∫ x² dμ) + r(t)

   where |r(t)| ≤ ε(t) · t² for some ε(t) → 0 as t → 0.

   More precisely: the function t ↦ (charFun μ t - 1 - i·t·m₁ + t²·m₂/2) / t² tends to 0 as t → 0, where m₁ = ∫ x dμ and m₂ = ∫ x² dμ.

2. **Centered, unit-variance specialization**: If μ is a probability measure with E[X] = 0 and E[X²] = 1, then:
   charFun μ t = 1 - t²/2 + o(t²)

3. **Quantitative remainder bound** (desirable but lower priority): Under finite third moment,
   |r(t)| ≤ C · |t|³ · E[|X|³]
   for some universal constant C. (This gives a Berry–Esseen-type bound but is not needed for the basic CLT.)

## Cases & Edge Cases

- **t = 0**: charFun μ 0 = 1 for probability measures. The expansion is trivially exact.
- **Degenerate measure** (Dirac at c): charFun is exp(i·c·t), expansion is exact with m₁ = c, m₂ = c².
- **Division by t²**: The little-o statement involves t² in the denominator. Must handle t = 0 separately (the limit is 0/0 → 0 by L'Hôpital or direct argument).

## Constraints

- The proof should go through dominated convergence: write charFun as ∫ e^{itx} dμ, expand e^{itx} = 1 + itx - t²x²/2 + R where |R| ≤ min(|t|³|x|³/6, t²x²), then integrate and take limits.
- Do NOT assume third moment exists for properties 1-2.
- The key analytic fact is: |e^{iy} - 1 - iy + y²/2| ≤ min(|y|³/6, y²) for real y. This pointwise bound, combined with dominated convergence (dominated by x² which is integrable), gives the result.

## Mathlib Dependencies

- `MeasureTheory.charFun`, `charFun_apply`
- `Complex.exp`, `Complex.abs_exp`, power series for exp
- `MeasureTheory.integral` (Bochner integral)
- `MeasureTheory.Memℒp` (for finite second moment condition)
- Dominated convergence theorem (`MeasureTheory.tendsto_integral_of_dominated_convergence`)
- `Complex.exp` Taylor / power series: `Complex.exp_bound` or related
- Basic inequalities for |e^{iy} - 1 - iy|, |e^{iy} - 1 - iy + y²/2|

## Success Criteria

- [ ] Properties 1 and 2 formalized as Lean4 theorems
- [ ] `lake build` succeeds with zero `sorry`
- [ ] Zero `axiom` declarations
- [ ] The expansion is stated in a way that's directly usable by the CLT proof: given charFun of Measure.map X μ, express it in terms of E[X] and E[X²]
