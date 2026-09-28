# Current Blockers and Status

> **Status, 2026-09-28.** Partly out of date. The integration formula is proved in
> `IwasawaIntegration.lean` by Haar uniqueness, so the Route B items listed as
> remaining below (B1c' steps 3 to 5, B1d, B2b, Level 3) are no longer needed for
> it. The Cayley density blocker still stands, but only for the explicit
> description of Haar measure on `K`. The build now runs from this repository's
> own `lakefile.toml`, not from a parent Lake project. See the README for the
> current state.

This file is a current status note for the Iwasawa change-of-coordinates
project. Older status logs have been superseded by the proved
diffeomorphism and derivative layers.

## Verified Core Status

- Active branch `haar-polynull`. The namespace for the project declarations
  is `IwasawaCoC` (the Haar layers live under `IwasawaCoC.Complete`).
- `lake build` succeeds from the parent Lake project root.
- The whole `iwasawa_change_of_coords/` subtree has ZERO active Lean `sorry`,
  `admit`, or `axiom` declarations and builds clean.
- `IwasawaCoC.contMDiff_iwasawaSymm` depends only on
  `[propext, Classical.choice, Quot.sound]`.
- `IwasawaCoC.iwasawaDiffeomorph` depends only on
  `[propext, Classical.choice, Quot.sound]`.
- `IwasawaCoC.mfderiv_iwasawaMap_at_factored` depends only on
  `[propext, Classical.choice, Quot.sound]`.
- The diffeomorphism and manifold derivative layers are closed (unchanged).

## Derivative Layer

The general derivative theorem is closed:

```lean
IwasawaCoC.mfderiv_iwasawaMap_at_factored
```

Its right-hand side is the direct chart-level matrix Leibniz map

```lean
iwasawaMatrixLeibnizCLM k a u
```

This is the actual derivative of `iwasawaMap` in the current charts.
The Cayley chart convention contributes the `-2` factor on the `K`
component.

The older

```lean
lieTwistCLM a
```

is retained as an auxiliary source twist. It is useful for isolating the
`A`-action on `NN` and for recognizing the positive-root density factor,
but it is not the full derivative of `iwasawaMap` in the current chart
convention.

## Jacobian Layer

`IwasawaJacobianExplicit.lean` proves the explicit determinant formula

```lean
adNN_det_eq_pair_product
```

which computes

```text
det(adNN a) = ∏_{i<j} a_i / a_j.
```

This is the positive-root product expected in the Iwasawa measure
formula. This auxiliary determinant is now connected to the determinant of
the actual derivative: `absDetInIwasawaBases_fderiv_iwasawaCharted_general`
(IwasawaComplete.lean) gives `|det fderiv|` of `iwasawaCharted` as
`absDetInIwasawaBases`, and
`absDetInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN`
(IwasawaJacobianExplicit.lean) folds in `adNN_det_eq_pair_product` with the
chart constants explicit (the `2^{n(n-1)/2} . |det a|^n . |det adNN a|`
form). The Jacobian and derivative layers are closed and axiom clean.

## Haar Bridge (axiom removed)

`IwasawaBridge.lean` previously declared one explicit axiom,
`iwasawa_haar_pushforward_bridge`, as future facing scaffolding. That axiom
has been REMOVED: it now survives only as prose in comments
(IwasawaBridge.lean and IwasawaComplete.lean), and the whole subtree is
axiom clean. The real Haar/change-of-variables development now lives in the
`IwasawaHaar.lean` / `IwasawaHaarK.lean` / `PolynomialNullSet.lean` files
under `IwasawaCoC.Complete` and proceeds via the Route B change-of-variables
program (see `RouteAssessment.md`), not via a single bridge axiom.

## Active Blocker

The single active blocker is density of the Cayley image in `SO(n)`,
needed for the nonemptiness that discharges B1c' step 2 over all of `SO(n)`.

The B1c' step 2 MEASURE CORE is DONE and axiom clean in
`IwasawaHaarK.lean` (`cayleyLeftDom_compl_null`): if `cayleyLeftDom k0`
is nonempty then its complement (the set the chart misses) has `volSk` measure zero. This
wires the standalone `MvPolynomial.volume_setOf_eval_eq_zero`
(`PolynomialNullSet.lean`) through an explicit coordinate transport
(`skCoordEquiv`, `map_skCoordEquiv_volSk`, `cayleyDomPoly` /
`eval_cayleyDomPoly`, `volSk_eq_volume_image`).

The nonemptiness hypothesis is REQUIRED. CORRECTNESS NOTE: the earlier
"for every `k0`" target is FALSE, because `det (cayley X) = 1` always, so
`cayleyLeftDom k0` is EMPTY when `det k0 = -1`. The honest statement is
conditional on nonemptiness, which holds on `SO(n)` (det +1). The generic
case is discharged (`cayleyLeftDom_nonempty_of_one_add_unit`,
`cayleyLeftDom_compl_null_of_one_add_unit`, take `X = 0` when `1 + k0` is
invertible). The hard remaining case (`k0` in `SO(n)` with `-1` in its
spectrum, e.g. `-I`) needs density of the Cayley image in `SO(n)`. See
`KDensityPlan.md`: Mathlib currently lacks connectedness of the orthogonal
group and exp/Cayley surjectivity onto `SO(n)`.

## Remaining Work

- B2a (Level 2 measure half) has LANDED, axiom clean in `IwasawaHaar.lean`
  (`nuG_lintegral_eq_setLIntegral_coord`,
  `haarG_lintegral_eq_smul_setLIntegral_coord`): the `haarG` integral equals
  a positive scalar times a coordinate Lebesgue integral weighted by
  `detWeightCoord` over `Set.range gToCoord`. It was independent of the
  density gap for the K factor.
- Still pending: the full PHASE-2 discharge for all `SO(n)` (Cayley density,
  `KDensityPlan.md`); B1c' steps 3 (Jacobian of `Psi`), 4 (density
  transformation), 5 (left invariance of `nuK`); the `det = -1` second chart;
  B1d (`nuK = c . haarK`); B2b (area formula on `iwasawaCharted`); Level 3
  (B3a/B3b/B3c). The final `iwasawaIntegrationFormula` is NOT done.
