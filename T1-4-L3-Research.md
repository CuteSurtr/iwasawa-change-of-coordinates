# T1-4 L3 research notes (2026-05-22)

Phase 1 research for closing `mfderiv_iwasawaMap_at_factored`.

## Textbook factorization (Knapp / Helgason / Folland)

Standard real-Lie-group references write the differential of the
Iwasawa multiplication map `μ : K × A × N → G, (k, a, n) ↦ k·a·n`
using LEFT-translation: `dμ_{(k,a,n)} = dL_{kan} ∘ (at-identity ∘
Ad-twist)`. The Cayley factor `-2` from our identity-case
parametrization persists in the K-component at general points,
absorbed into the chart-coord differential.

## Mathlib infrastructure (Agent 1 results)

**Mathlib has ZERO closed-form `mfderiv mul` lemmas** for general
base points. The library provides:

- `mfderiv_prod_eq_add_apply` (in `MFDeriv/SpecificFunctions.lean`):
  `mfderiv (fun p ↦ f (p.1, p.2)) p v = mfderiv (fun z ↦ f (z, p.2)) p.1 v.1 +
  mfderiv (fun z ↦ f (p.1, z)) p.2 v.2`. The canonical pattern for
  product-domain differentials.
- `inverse_mfderiv_mul_left` (in `GroupLieAlgebra.lean:103`):
  invertibility of partial-left-translation mfderiv, not a closed form.
- `mulInvariantVectorField v g := mfderiv (g * ·) 1 v` — left-translation
  is the canonical convention.

Mathlib uses LEFT-translation throughout `GroupLieAlgebra.lean`. No
right-translation analogue is developed. Our project's K chart
(`cayley X.1 * Q₀.1` per IwasawaSmoothK.lean:125-126) uses
RIGHT-multiplication, which creates a tension with the Mathlib idiom.

**No PR closes the closed-form-of-product-rule gap.** The bottom-line
recommendation: use `mfderiv_prod_eq_add_apply` + `mfderiv_comp` with
`contMDiff_mul_left`/`contMDiff_mul_right`.

## Lean elaboration (Agent 2 results)

Root cause of `ChartedSpace` TC stalls: `ChartedSpace`'s `H` parameter
was changed from `outParam` to explicit to avoid product diamonds (per
Gouëzel on Zulip). When `H` is a metavariable, TC synthesis stalls.

**Battle-tested unstick idioms** (in priority order):

1. `mfderiv_comp_of_eq` and `HasMFDerivAt.comp` — variants that take
   `(hy : f x = y)` argument, decoupling basepoint from `f x`. The
   most reliable fix for stuck synthesis.
2. Named model-corners arguments: `mfderiv (I := IK) (I' := IA) ...`.
3. Full CLM type ascription on every intermediate `have`.
4. `HasMFDerivAt.prodMk` (this is our validated T1-3 pattern).
5. Avoid `MDifferentiableAt.comp` — it throws away derivative
   witnesses, leaving TC with nothing to anchor.

## Correct formula for our chart conventions

Given our K chart (`cayley X.1 * Q₀.1`, right-mul), our A chart
(`diag(exp v)`, global single chart), and our UU chart (`v ↦ v + 1`,
affine global chart):

**Chart-coord differentials at general base points** (each is a
sub-lemma we'd need to prove):
- K at `k₀`: `δX ↦ -2 (δX.1) * k₀.1` (`-2` Cayley factor times right-mul by `k₀.1`).
- A at `a₀`: `δv ↦ a₀.1 * Matrix.diagonal v` (`a₀.1` left-multiplication times diagonal CLM).
- UU at `u₀`: `δZ ↦ δZ.1` (uniformly `NN.subtypeL`, chart is affine global).

**Matrix Leibniz at `(k₀.1, a₀.1, u₀.1)`** gives:
```
mfderiv iwasawaMap (k₀, a₀, u₀) (X, v, Z) =
  (-2 X.1 * k₀.1) * a₀.1 * u₀.1
    + k₀.1 * (a₀.1 * diag v) * u₀.1
    + k₀.1 * a₀.1 * Z.1
= -2 X.1 * (k₀.1 a₀.1 u₀.1) + k₀.1 a₀.1 diag(v) u₀.1 + k₀.1 a₀.1 Z.1
```

This is form (c). The previous-session stated factorization
`leftMul_{kau} ∘ iwasawaLieMapCLM ∘ lieTwistCLM a` would distribute
to `-2 (kau) X.1 + (kau) diag v + (kau) a Z.1 a⁻¹` — INCONSISTENT
with the actual formula (X.1 on right of kau, not left).

## Decision for Phase 2

**Use form (c): direct matrix Leibniz.** Change the L3 theorem
statement to use the correct formula. Sub-lemmas (chart-coord
differentials at general points) follow the same template as the
at-identity versions (`mfderiv_subtypeVal_*_one`) but parameterized
over the base point — each is ~50 lines of reuse. The Mathlib idiom
`HasMFDerivAt.comp` with explicit `f x = y` argument handles the TC
elaboration issues.

Time budget: 35 min for Phase 2. If sub-lemmas blow up, the L3 theorem
itself may transitively carry sub-sorries on the general-point
chart-coord differentials, but the OVERALL statement and assembly
structure will be correct.
