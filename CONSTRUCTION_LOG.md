# Construction Log

Cumulative record of all construction audit results.

---

## Log Entries

### ExpBound — 2026-02-14
- **Spec**: (part of `specs/charfun-taylor.md`)
- **Lean files**: `CLT/CharFun/ExpBound.lean`
- **lake build**: PASS
- **sorry count**: 0
- **axiom count**: 0
- **native_decide count**: 0

#### Coverage
| Spec Property | Lean4 Theorem | Status |
|--------------|---------------|--------|
| ‖exp(iy)-1-iy‖ ≤ y² for \|y\|≤1 | `norm_cexp_mul_I_sub_one_sub_le` | PROVED |
| ‖exp(iy)-1-iy‖ ≤ 3y² for all y | `norm_cexp_mul_I_sub_one_sub_le_sq` | PROVED |
| ‖exp(iy)-1-iy+y²/2‖ ≤ 4y² for all y | `norm_cexp_mul_I_taylor2_le` | PROVED |
| ‖exp(iy)-1-iy+y²/2‖ ≤ \|y\|³ for \|y\|≤1 | `norm_cexp_mul_I_taylor2_le_cube` | PROVED |

#### Verdict: PASS
#### Notes
Pointwise bounds on exp(iy) - polynomial for ALL real y. Case-split on |y| ≤ 1 vs |y| > 1. Small case uses `norm_exp_sub_one_sub_id_le`, large case uses triangle inequality. Cubic bound uses `Complex.exp_bound` with n=3.

---

### CentralLimitTheorem — 2026-02-15
- **Spec**: `specs/central-limit-theorem.md`
- **Lean files**: `CLT/CentralLimitTheorem.lean`
- **lake build**: PASS
- **sorry count**: 0
- **axiom count**: 0
- **native_decide count**: 0

#### Coverage
| Spec Property | Lean4 Theorem | Status |
|--------------|---------------|--------|
| charFun of iid sum = power | `charFun_iid_sum_eq_pow` | PROVED |
| CLT charFun convergence | `central_limit_theorem_charFun` | PROVED |
| CLT (weak convergence) | `central_limit_theorem` | PROVED |

#### Verdict: PASS
#### Notes
Key techniques: (1) `congr_arg Complex.ofReal` pattern for ℝ→ℂ transfer (avoids `sq_sqrt` issues in ℂ context), (2) `Complex.tendsto_one_add_pow_exp_of_tendsto` for the n-th power limit, (3) `charFun_gaussianReal` for target identification. The `hlimit` block required careful handling of 5 inner sorrys: centered mean (hce), variance (hve), scaling sequence (hs), big-O bound (hbigO), and algebraic identity.

---

### Taylor — 2026-02-16
- **Spec**: `charfun-taylor.md`
- **Lean files**: `CLT/CharFun/Taylor.lean`
- **lake build**: PASS (style warnings only)
- **sorry count**: 0
- **axiom count**: 0
- **native_decide count**: 0

#### Coverage
| Spec Property | Lean4 Theorem | Status |
|--------------|---------------|--------|
| General 2nd-order expansion | `charFun_taylor_remainder_isLittleO` | PROVED |
| Centered measure specialization | `charFun_taylor_centered` | PROVED |
| Unit variance specialization | `charFun_taylor_centered_unit_variance` | PROVED |

#### Verdict: PASS
#### Notes
All 5 sorrys in `charFun_taylor_remainder_isLittleO` eliminated:
- **hdiff**: `charFun_apply_real` + integral linearity via `integral_sub`/`integral_add` with Pi-form bridging via `integral_congr_ae` + `ring`
- **Bound**: `norm_cexp_mul_I_taylor2_le` with coercion matching: `simp only [ofReal_*] at h; convert h using 2; push_cast; ring`
- **Pointwise**: `norm_cexp_mul_I_taylor2_le_cube` for cubic bound
- **Integrability**: `hL2.integrable_sq.const_mul 4`
- **AEStronglyMeasurable**: Continuity chain
- Key lesson: `rw` cannot rewrite under integral binders with function equalities. Use `← integral_sub/add` on split forms, then `integral_congr_ae` to bridge Pi vs lambda forms.

---

### LevyContinuity — 2026-02-16 (COMPLETED 2026-02-16)
- **Spec**: `specs/levy-continuity.md`
- **Lean files**: `CLT/LevyContinuity.lean`
- **lake build**: PASS
- **sorry count**: 0
- **axiom count**: 0
- **native_decide count**: 0

#### Coverage
| Spec Property | Lean4 Theorem | Status |
|--------------|---------------|--------|
| Tightness from charFun convergence | `isTightMeasureSet_of_charFun_tendsto` | PROVED |
| Forward Lévy continuity | `levy_continuity` | PROVED |
| Converse Lévy continuity | `tendsto_charFun_of_tendsto_probabilityMeasure` | PROVED |

#### Fixes applied (2026-02-16):
1. **Error 1 (Line 95-99)**: Replaced `rw [mul_comm]; exact this` with explicit `calc` chain computing `|2r₁⁻¹ - -(2r₁⁻¹)| = 4r₁⁻¹` then `ring` to close `ε'/4 * 4r₁⁻¹ = ε' * r₁⁻¹`
2. **Error 2 (Line 132)**: Changed `congr 1; ext x; simp [Real.norm_eq_abs]` to `simp only [Real.norm_eq_abs]`
3. **Error 3 (Lines 134-136)**: Extracted `measureReal_abs_gt_le_integral_charFun` into a `have` with `simp only [neg_mul]` to align `-2 * r₁⁻¹` with `-(2 * r₁⁻¹)`
4. **Error 4 (Lines 153-154)**: Replaced `gcongr` + swapped focus with `add_le_add hbound_norm_μ (le_of_lt (lt_of_abs_lt hNn))`

#### Verdict: PASS

---

### CentralLimitTheorem — UPGRADED — 2026-02-16
- **Spec**: `specs/central-limit-theorem.md`
- **Lean files**: `CLT/CentralLimitTheorem.lean`
- **lake build**: PASS
- **sorry count**: 0
- **axiom count**: 0
- **native_decide count**: 0

#### Coverage
| Spec Property | Lean4 Theorem | Status |
|--------------|---------------|--------|
| charFun of iid sum = power | `charFun_iid_sum_eq_pow` | PROVED |
| CLT charFun convergence | `central_limit_theorem_charFun` | PROVED |
| CLT (weak convergence of ProbabilityMeasure ℝ) | `central_limit_theorem` | PROVED |

#### Upgrade applied (2026-02-16):
- `central_limit_theorem` statement changed from charFun convergence (duplicate of `central_limit_theorem_charFun`) to weak convergence of `ProbabilityMeasure ℝ` via `levy_continuity`
- New statement: `Tendsto (β := ProbabilityMeasure ℝ) (fun n ↦ ⟨P.map Zₙ, ...⟩) atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩)`
- Proof: `exact levy_continuity (central_limit_theorem_charFun hindep hident hmeas hL2 hvar)`
- Used `β := ProbabilityMeasure ℝ` explicit type parameter for `TopologicalSpace` instance synthesis
- `IsProbabilityMeasure` for `P.map Zₙ` proved inline via `Measure.isProbabilityMeasure_map`

#### Verdict: PASS

---
