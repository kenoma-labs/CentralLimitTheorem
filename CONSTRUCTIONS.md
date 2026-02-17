# Constructions Queue

Program mode reads this file to auto-advance through mathematical constructions.

## Priority Queue

| Priority | Construction | Spec File | Status | Depends On | Notes |
|----------|-------------|-----------|--------|------------|-------|
| P1 | charfun_products | `specs/charfun-products.md` | Audited | — | charFun of convolutions / independent sums, charFun under affine maps. Used Mathlib builtins directly. |
| P2 | charfun_taylor | `specs/charfun-taylor.md` | Audited | P1 | Second-order Taylor expansion: charFun μ t = 1 + itm₁ - t²m₂/2 + o(t²). ExpBound + Taylor complete, 0 sorry. |
| P3 | levy_continuity | `specs/levy-continuity.md` | Audited | P1 | Forward + converse Levy continuity theorem. Tightness lemma complete, 0 sorry. |
| P4 | central_limit_theorem | `specs/central-limit-theorem.md` | Audited | P2, P3 | Lindeberg-Levy CLT for iid finite variance. Weak convergence via levy_continuity. 0 sorry. |

### Status Values
- **Not started** — spec not yet written
- **Specified** — spec complete, ready for construction
- **Constructed** — informal math done, ready for formalization
- **Formalized** — .lean files written (all sorry)
- **Proved** — all sorrys eliminated
- **Audited** — passed audit, logged
- **Revision** — needs revision (see REVISION.md)
- **Blocked** — blocked on dependency

---

## Completed

| Construction | Spec File | Date Completed | Theorems |
|-------------|-----------|----------------|----------|
| ExpBound | (part of charfun-taylor) | 2026-02-14 | `norm_cexp_mul_I_sub_one_sub_le`, `norm_cexp_mul_I_sub_one_sub_le_sq`, `norm_cexp_mul_I_taylor2_le`, `norm_cexp_mul_I_taylor2_le_cube` |
| Taylor | `charfun-taylor.md` | 2026-02-16 | `charFun_taylor_remainder_isLittleO`, `charFun_taylor_centered`, `charFun_taylor_centered_unit_variance` |
| LevyContinuity | `specs/levy-continuity.md` | 2026-02-17 | `levy_continuity`, `tendsto_charFun_of_tendsto_probabilityMeasure` |
| CentralLimitTheorem | `specs/central-limit-theorem.md` | 2026-02-17 | `charFun_iid_sum_eq_pow`, `central_limit_theorem_charFun`, `central_limit_theorem` |

---

## Dependencies

P1 (charfun_products) is foundational: it establishes how charFun interacts with measure convolution (products of independent RVs) and affine transformations. Both P2 and P3 use this.

P2 (charfun_taylor) depends on P1 because the Taylor expansion uses the relationship between charFun and moments, and the proof may use charFun differentiability results.

P3 (levy_continuity) depends on P1 because the proof requires knowing that charFun of a probability measure is continuous and bounded (basic properties from P1's development). The core of P3 is a tightness + subsequence argument specific to ℝ.

P4 (central_limit_theorem) depends on both P2 and P3: it uses the Taylor expansion (P2) to show charFun convergence, then Levy continuity (P3) to upgrade that to convergence in distribution.

### Diamond dependency: P4 depends on P2 and P3, both depend on P1.
Lean handles duplicate imports idempotently, so no deduplication issues.
