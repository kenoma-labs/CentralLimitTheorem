# Construction Spec: Characteristic Function Products and Affine Maps

## Domain
Characteristic functions of probability measures on ℝ. Interaction of charFun with measure convolution and affine transformations.

## Goal
Establish the algebraic properties of characteristic functions needed downstream by the Taylor expansion and Lévy continuity constructions: charFun is multiplicative over convolution of independent measures, and transforms predictably under affine maps.

## Required Properties

1. **CharFun of convolution**: For finite measures μ and ν on ℝ,
   charFun (μ * ν) t = charFun μ t · charFun ν t
   where * is measure convolution (`MeasureTheory.Measure.conv`).

2. **CharFun of independent sum**: If X, Y : Ω → ℝ are independent random variables (IndepFun), then
   charFun (Measure.map (X + Y) μ) t = charFun (Measure.map X μ) t · charFun (Measure.map Y μ) t

3. **CharFun of iid sum**: For iIndepFun X and IdentDistrib, the charFun of the sum X₀ + ... + X_{n-1} is the n-th power of the common charFun:
   charFun (Measure.map (∑ i in Finset.range n, X i) μ) t = (charFun (Measure.map (X 0) μ) t) ^ n

4. **CharFun under scaling**: charFun (Measure.map (fun x => a * x) μ) t = charFun μ (a * t)

5. **CharFun under translation**: charFun (Measure.map (fun x => x + b) μ) t = exp(i·b·t) · charFun μ t

6. **CharFun under affine map** (combines 4 and 5):
   charFun (Measure.map (fun x => a * x + b) μ) t = exp(i·b·t) · charFun μ (a * t)

7. **CharFun is bounded**: |charFun μ t| ≤ μ(Set.univ) for any finite measure μ. For probability measures, |charFun μ t| ≤ 1.

8. **CharFun at zero**: charFun μ 0 = μ(Set.univ). For probability measures, charFun μ 0 = 1.

9. **CharFun is uniformly continuous**: For a finite measure μ, charFun μ is uniformly continuous on ℝ.

## Cases & Edge Cases

- a = 0 in affine map: charFun of constant b is exp(i·b·t), which is a Dirac mass.
- n = 0 in iid sum: empty sum is the zero function, charFun should be the constant 1 (Dirac at 0).
- Measurability: X + Y, a*X + b, and finite sums must be shown measurable.

## Constraints

- Properties 1-3 require some form of independence assumption. Do not assume product spaces — use mathlib's `IndepFun`/`iIndepFun`.
- Properties 4-6 hold for all finite measures, not just probability measures.
- Proofs should use `charFun_apply` (the integral definition) and standard integration lemmas.

## Mathlib Dependencies

- `MeasureTheory.charFun`, `charFun_apply`, `charFun_zero`
- `MeasureTheory.Measure.conv` (convolution of measures)
- `ProbabilityTheory.IndepFun`, `ProbabilityTheory.iIndepFun`
- `MeasureTheory.Measure.map` (pushforward measure)
- `MeasureTheory.integral_add`, integration linearity
- `Complex.exp`, `Complex.abs_exp`

## Success Criteria

- [ ] All 9 properties formalized as Lean4 theorems
- [ ] `lake build` succeeds with zero `sorry`
- [ ] Zero `axiom` declarations
- [ ] Properties are stated for general finite measures where possible, specialized to probability measures where needed
