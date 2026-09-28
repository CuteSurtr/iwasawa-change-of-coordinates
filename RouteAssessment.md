# Iwasawa integration formula: route assessment (branch `haar-polynull`, namespace `IwasawaCoC.Complete`)

> **Status, 2026-09-28.** The integration formula is now proved in
> `IwasawaIntegration.lean` by a third route: Haar uniqueness on the group
> `K × B`, `B = AU` (Knapp, Prop. 8.43). It needs neither Route A's disintegration
> nor Route B's Cayley density on `K`, so the remaining B1c' and B1d steps below are
> no longer needed for the formula.

Goal of the assembly (NOT started here): the Iwasawa integration formula on
`G n = GL_n(R)`, relating `haarG` to the factor Haar measures through
`iwasawaMap (k,a,u) = k * a * u`, with the modular weight from the `A` action on
`U`. Schematically, `integral over G of f d haarG` equals (up to a positive
constant) `integral over K x A x U of f(k a u) . delta(a) d(haarK x haarA x haarN)`.

## What is already done (verified on `main` / this branch)
- `iwasawaEquiv` / `iwasawaHomeo` / `iwasawaDiffeo`: `K n x A n x UU n` is
  homeomorphic and diffeomorphic to `G n` via `(k,a,u) |-> k a u` (IwasawaCoC.lean,
  IwasawaComplete.lean).
- `iwasawaCharted`: a chart from an open subset of the Lie algebra
  `Sk n x (Fin n -> R) x NN n` (dimension `n^2`) onto `G n`, with explicit
  Frechet derivative; its absolute Jacobian determinant is `absDetInIwasawaBases`
  ( = `2^{n(n-1)/2} . |det a|^n . |det adNN a|`, the `..._unconditional` form).
- `map_conjAut_haarN` (the crux): conjugation by `a` scales `haarN` by
  `delta(a) = det (adNN a)`.
- `modularCharacterFun_eq_one`: `GL_n(R)` is unimodular (done in this project).
- `nuG = haarScalarFactor nuG haarG . haarG`: the explicit coordinate Haar
  `haarGCoord = volume.withDensity detWeightCoord` (pulled back to `G n` as `nuG`)
  equals the canonical `haarG` up to a positive scalar (PHASE 1, this branch).
- `haarAExplicit` (A, via the log chart) and `nuU` (U, via the entry chart):
  explicit left Haar measures on the abelian/unipotent factors, each a pushforward
  of Lebesgue through a global chart, proven left invariant.

## Mathlib API that is available
- Change of variables / area formula: `lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
  `integral_image_eq_integral_abs_det_fderiv_smul`, and the chart form
  `integral_target_eq_integral_abs_det_fderiv_smul` (Function/Jacobian.lean). This is
  Route B's engine and it is fully general for C^1 maps injective on a measurable set.
- Haar uniqueness: `isHaarMeasure_eq_smul` (second countable), `haarMeasure_unique`,
  `haarMeasure_self` (compact Haar is a probability measure). This is the chart free
  way to identify any left invariant regular measure with the canonical Haar.
- Regularity: the PHASE 1 instances (`SecondCountableTopology`, `PseudoMetrizableSpace`,
  `SigmaCompactSpace`, `Regular`, `InnerRegular`) are now in place for `G n` and
  transfer to the factors by the same pattern.
- NOT available: a Weil integration formula for a non-discrete closed subgroup.
  `Haar/Quotient.lean` is entirely `[Countable Gamma]` (lattices, fundamental domains).
  `Haar/Disintegration.lean` is only about linear maps on vector spaces (Lie algebra
  level), not subgroup disintegration. General `condKernel` disintegration exists but
  only as an abstract kernel, with no "invariant implies product" specialization.

## Route B (change of variables) -- RECOMMENDED
Leverages the project's largest investment (the explicit Jacobian and the chart
`iwasawaCharted`) plus the now completed coordinate Haar identification, and runs on
Mathlib's fully supported change of variables engine.
- Hard step: the `K = O(n)` factor. `O(n)` is compact with no global chart and two
  components, so it needs a multi chart Cayley atlas (skew symmetric `Sk` to special
  orthogonal, one chart per component, each onto an open dense subset). The chart
  Lebesgue measure on `K` must be tied to `haarK`. This is concrete and of the SAME
  KIND as the already done `A` (log) and `U` (entry) chart work, only messier
  (the Cayley map does not linearize multiplication, and the chart is partial).

## Route A (Haar uniqueness) -- viable but higher risk, NOT recommended
Leverages unimodularity (done) and the crux (done), and avoids charting `K` (the `K`
factor is `haarK` by uniqueness on the compact group). But the core step, decomposing
the pulled back `haarG` on `K x A x U` into a weighted product, is a disintegration /
Weil integration formula for the non-discrete closed subgroup `AN`, which Mathlib does
not provide. The "pushforward of a product is left invariant" shortcut fails because
left multiplication by `A` or `U` does not respect the `KAU` decomposition (only left
`K` and right `A`, `U` do, the latter via the crux), so it still funnels through a
disintegration. Building that is a general measure theory development of uncertain size.

## Recommendation and reasoning
Recommend **Route B**. Reasoning, in order of weight:
1. Engine support: Route B's change of variables is fully in Mathlib; Route A's
   disintegration core is not packaged and must be built from scratch (higher risk).
2. Leverage: Route B reuses `iwasawaCharted`, `absDetInIwasawaBases`, `iwasawaDiffeo`,
   `haarGCoord = nuG = c . haarG`, `haarAExplicit`, `nuU` directly; Route A largely
   bypasses the Jacobian, the project's biggest asset.
3. Nature of the bottleneck: Route B's `K` Cayley chart plus left invariance, then
   `haarK` by uniqueness, is concrete and analogous to the finished `A` and `U` work;
   Route A's bottleneck is abstract and general.
4. Decomposability: Route B can first produce a fully explicit coordinate integration
   formula with the chart measure on `K`, and only then (optionally) identify that chart
   measure with the canonical `haarK` by uniqueness. The hard `K` step is thus isolable
   and does not block a complete intermediate result.

Biggest residual risk: the `K` chart Haar identification. Fallback if Mathlib's
manifold / Riemannian volume support is insufficient: prove the Cayley chart Lebesgue
measure on `K` is left invariant by direct matrix computation and invoke `haarMeasure_unique`
(no Riemannian volume needed), exactly mirroring `toFinNRHomeomorph_mul` for `A` and
`leftMul_nnChart_symm` for `U`.

## Route B: dependency ordered lemma DAG (to implement next; not started)
Level 0 (factor Haar identifications by uniqueness; reuse PHASE 1 regularity pattern): DONE
on branch `haar-routeb` (commit `efcb18b`), green and axiom clean.
- B0a [DONE] `haarAExplicit_eq_haarScalarFactor_smul_haarA : haarAExplicit = haarScalarFactor haarAExplicit haarA . haarA`.
  Needed two new instances on `haarAExplicit` (finite on compacts and `Regular`, transported
  through the log chart homeomorphism, mirroring `nuU`); `A` already had second countable and
  pseudo metrizable, so inner regularity then resolved automatically.
- B0b [DONE] `nuU_eq_haarScalarFactor_smul_haarN : nuU = haarScalarFactor nuU haarN . haarN`.
  No new instances; `nuU` already carried its regularity (`instRegular_nuU`).

Level 1 (the K chart): IN PROGRESS. Existing machinery inventoried and reused (do not rebuild):
`Sk n` (skew matrices), `cayley` / `cayleyInv`, `cayleyToK : Sk n -> K n`,
`cayleyHomeomorph : Sk n =t K_open n`, `cayleyOpenChartAt Q0 : OpenPartialHomeomorph (K n) (Sk n)`,
`cayleyFDerivCLM M : d cayley = -2 . (1+M)^{-1} . _ . (1+M)^{-1}`, `det_cayley_skew : (cayley X).det = 1`,
`instCompactSpaceK : CompactSpace (K n)`.

CORRECTION to the earlier plan (important). The premise "flat chart Lebesgue `map cayleyToK volume`
is left invariant, mirroring A and U" is FALSE for `n >= 2`. A (abelian, log linearizes left
translation to addition) and U (unipotent, affine with unit linear part) are flat groups, so flat
Lebesgue is invariant there. `O(n)` is curved: left translation in Cayley coordinates is a Mobius
type map with non constant Jacobian (the `cayleyFDerivCLM` sandwich by `(1+M)^{-1}` is not volume
preserving). Verified for `SO(2)`: with `X = [[0,a],[-a,0]]`, `cayley X` is rotation by `2 arctan a`,
so Haar `dtheta` pulls back to `(2/(1+a^2)) da`, NOT flat `da`. The invariant density in Cayley
coordinates is `proportional to det(1+X)^{-(n-1)}` (consistent with the `cayleyFDerivCLM` sandwich
and the `SO(2)` value `2/(1+a^2)`). Also `det_cayley_skew = 1` means one Cayley chart covers only the
`SO(n)` (det +1) component, so `O(n) = SO(n) sqcup (det -1)` needs a second chart.

Corrected Level 1 sub steps (file `IwasawaHaarK.lean`, branch `haar-cayleyk`, axiom clean):
- B1a [available, reuse] the Cayley chart `cayleyHomeomorph` / `cayleyOpenChartAt` and
  `cayleyFDerivCLM` already exist; no rebuild needed.
- B1b' [DONE] density `rhoK X = ENNReal.ofReal (|det (1+X.1)|^{-(n-1)})` defined (`rhoK`), with the
  exponent PINNED (not hard-coded) by an honest determinant computation:
  `cayleyDerivOnSk X = -2 . sandwichOnSkCLM ((1+X)^{-1})` is the intrinsic chart derivative on `Sk n`
  (the ambient `cayleyFDerivCLM X` left translated by `(cayley X)^T` back to the identity tangent
  space), and `det_cayleyDerivOnSk` gives
  `det (cayleyDerivOnSk X) = (-2)^{card nnIndex} . (det (1+X))^{-(n-1)}` reusing the existing
  `det_sandwichOnSkCLM`. `abs_det_cayleyDerivOnSk` and `ofReal_abs_det_cayleyDerivOnSk` tie `rhoK` to
  the absolute Jacobian (up to the positive constant `2^{card nnIndex}`, absorbed by uniqueness).
  SO(2) check: `card_nnIndex_two : card (nnIndex 2) = 1` and `abs_det_cayleyDerivOnSk_two` recover the
  classical `2 / (1+a^2)`. Density continuity / measurability: `continuous_rhoK`, `measurable_rhoK`.
- B1c' [PARTIAL] infrastructure: `volSk := skBasis.addHaar` (Lebesgue on `Sk n`),
  `nuK := map cayleyToK (volSk.withDensity rhoK)` (candidate measure on the `SO(n)` component),
  `continuous_cayleyToK` / `measurable_cayleyToK` / `nuK_apply`. Goal: left invariance
  `map (fun k => k0 * k) nuK = nuK` for `k0` in `SO(n)`, via change of variables for the Mobius left
  translation `Psi k0 X = cayleyInv (k0 * cayley X)`. Progress against the five sub steps:
  - step 1 [DONE] `cayleyLeftDom k0` (the domain, `{X | 1 + k0 * cayley X invertible}`),
    `cayleyLeftTrans` (= `Psi k0`), `cayleyLeftTrans_isSkew`, `cayley_cayleyLeftTrans`
    (`cayley (Psi k0 X) = k0 * cayley X`, the geometric heart), `cayleyToK_cayleyLeftTransSk`
    (`cayleyToK (Psi k0 X) = k0 * cayleyToK X`, the chart intertwines `Psi k0` with left mult by `k0`),
    `isOpen_cayleyLeftDom`, `continuousOn_cayleyLeftTrans`. (C^1 smoothness of `Psi` not yet done.)
  - step 2 [MEASURE CORE DONE; nonemptiness/density open] reduction `one_add_k_cayley_mul`:
    `(1 + k0 * cayley X) * (1 + X) = (1 + X) + k0 * (1 - X)`, hence `det_one_add_k_cayley` and
    `mem_cayleyLeftDom_iff`: `X in cayleyLeftDom k0 iff det ((1 + X) + k0 * (1 - X)) != 0`, the
    non-vanishing locus of a polynomial in the entries of `X`. The split is into (a) that polynomial is
    not identically zero (a domain point, i.e. `cayleyLeftDom k0` nonempty) and (b) the zero set of a
    nonzero multivariate polynomial is Lebesgue null.
    Part (b) is DONE: the general lemma `MvPolynomial.volume_setOf_eval_eq_zero` (for nonzero
    `p : MvPolynomial (Fin d) R`, `volume {x | eval x p = 0} = 0`) is proven and axiom clean in the new
    self contained file `PolynomialNullSet.lean` (induction via `finSuccEquiv`: leading coefficient null
    base set by IH, `Polynomial.finite_setOf_isRoot` finite slices, Fubini `measure_prod_null`). This
    closes the Mathlib gap.
    The PHASE 2 APPLICATION to `cayleyLeftDom` is now DONE and axiom clean in `IwasawaHaarK.lean`:
    `cayleyLeftDom_compl_null` proves that if `cayleyLeftDom k0` is nonempty then its complement
    (the set the chart misses) has `volSk` measure zero. The wiring runs `MvPolynomial.volume_setOf_eval_eq_zero`
    through an explicit coordinate transport: `skCoordEquiv` (the reindexed coordinate equiv
    `Sk n` to `Fin (card nnIndex) -> R`), `map_skCoordEquiv_volSk` (pushes `volSk` to Lebesgue
    `volume`), the determinant polynomial `cayleyDomPoly` with `eval_cayleyDomPoly`
    (`eval c cayleyDomPoly = det ((1 + X) + k0 (1 - X))` at `X = skCoordEquiv.symm c`),
    `volSk_eq_volume_image`, plus `skEntryPoly` / `eval_skEntryPoly` / `skCoordEquiv_symm_apply`
    / `skMatPoly`. So parts (i) det as an `MvPolynomial` in coordinates and (ii) null transport from
    `volSk` to Lebesgue are both closed.
    REMAINDER, part (a) the nonemptiness: this hypothesis is REQUIRED and is the real remaining
    sub step. CORRECTNESS NOTE: the earlier "for every `k0 : K n`" target is FALSE. Since
    `det (cayley X) = 1` always (`det_cayley_skew`), `cayleyLeftDom k0` is EMPTY when `det k0 = -1`,
    so the honest statement is conditional on nonemptiness, which holds on `SO(n)` (det +1). The
    generic case is discharged: `cayleyLeftDom_nonempty_of_one_add_unit` (take `X = 0` when `1 + k0`
    is invertible) and `cayleyLeftDom_compl_null_of_one_add_unit`. The hard remaining case
    (`k0` in `SO(n)` with `-1` in its spectrum, e.g. `-I`) needs density of the Cayley image in
    `SO(n)`; see `KDensityPlan.md` (Mathlib lacks connectedness of the orthogonal group and
    exp/Cayley surjectivity onto `SO(n)`).
  - step 3 [not started] Jacobian `|det D Psi X|` via `det_cayleyDerivOnSk`. `Psi = cayleyInv o (left
    mult k0) o cayley`, and since `cayleyInv` and `cayley` are the SAME formula, `D cayleyInv` reuses
    `cayleyFDerivCLM`; needs the tangent-space / left-translation bookkeeping to give
    `|det D Psi X| = |det cayleyDerivOnSk X| / |det cayleyDerivOnSk (Psi X)|`.
  - step 4 [not started] density transformation `rhoK (Psi X) * |det D Psi X| = rhoK X`, pure algebra
    from step 3 and `ofReal_abs_det_cayleyDerivOnSk` once step 3 lands.
  - step 5 [not started] assemble left invariance via Mathlib change of variables, the density
    transformation (step 4), and the null complement (step 2 remainder). Gated by steps 2(b), 3, 4.
- det = -1 component: one Cayley chart covers `SO(n)` only (`det_cayley_skew = 1`); the `det -1` coset
  needs a reflected copy. Deferred.
- B1d [not started] `nuK = c_K . haarK` by Haar uniqueness (`K` compact, `InnerRegular haarK` free).
  Requires `nuK` first established as a Haar measure (needs B1c' invariance, finiteness, open positivity).

Status: B1b' complete. B1c' step 1 (the Mobius map, defining identity, domain openness, continuity)
DONE; step 2 reduction (domain = polynomial non-vanishing locus) DONE. Step 2(b), the measure-zero of a
nonzero multivariate polynomial zero set, is DONE as the standalone axiom clean lemma
`MvPolynomial.volume_setOf_eval_eq_zero` in `PolynomialNullSet.lean` (the Mathlib gap is closed). The
step 2 MEASURE CORE is now DONE and axiom clean in `IwasawaHaarK.lean`: `cayleyLeftDom_compl_null`
wires that lemma to `cayleyLeftDom` through the `skCoordEquiv` coordinate transport (det as
`MvPolynomial` via `cayleyDomPoly` / `eval_cayleyDomPoly`, null transport from `volSk` to Lebesgue via
`map_skCoordEquiv_volSk` and `volSk_eq_volume_image`), conditional on `cayleyLeftDom k0` being
nonempty. The nonemptiness is REQUIRED (a correctness fix: `cayleyLeftDom k0` is empty for `det k0 = -1`
since `det (cayley X) = 1`), holds on `SO(n)`, and is discharged in the generic case
(`cayleyLeftDom_nonempty_of_one_add_unit`). The hard remaining case (`k0` in `SO(n)` with `-1` in its
spectrum) needs density of the Cayley image in `SO(n)`; see `KDensityPlan.md`. What remains for the full
PHASE 2 discharge over all `SO(n)`: that Cayley density (`KDensityPlan.md`); then the step 3 Jacobian
bookkeeping, steps 4 and 5. No flat Lebesgue shortcut; no Riemannian volume form; no statement weakened;
no sorry or axiom.

Level 2 (the change of variables on the full chart):
- B2a [DONE, axiom clean in `IwasawaHaar.lean`] `nuG_lintegral_eq_setLIntegral_coord` and
  `haarG_lintegral_eq_smul_setLIntegral_coord`: the `haarG` integral equals a positive scalar times a
  coordinate Lebesgue integral weighted by `detWeightCoord` over `Set.range gToCoord`, with the scalar
  `= haarScalarFactor nuG haarG`. Built from `nuG = c . haarG`,
  `haarGCoord = volume.withDensity detWeightCoord`, and `comap` apply. This is the Level 2 measure half
  and, as predicted, it is independent of the density gap for the K factor.
- B2b [not started] apply `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (or the
  `integral_target_eq_integral_abs_det_fderiv_smul` chart form) to `iwasawaCharted`,
  using `absDetInIwasawaBases` as `|det fderiv|`, giving the integral over `G` as an
  integral over the chart domain in `Sk x (Fin n -> R) x NN` against Lebesgue with weight
  `absDetInIwasawaBases`. Needs the source/target coordinate identification: the bridge
  `detInIwasawaBases = LinearMap.det` of the coordinate composite, injectivity of `iwasawaCharted` on
  its domain, `HasFDerivWithinAt` of the composite, then
  `integral_image_eq_integral_abs_det_fderiv_smul` using
  `absDetInIwasawaBases_fderiv_iwasawaCharted_general`.

Level 3 (assembly):
- B3a factor the chart domain Lebesgue measure as a product over the `Sk`, diagonal, and
  `NN` blocks (`Measure.prod`, `volume_pi`), aligning `iwasawaCharted` with
  `iwasawaMap` composed with the three factor charts.
- B3b substitute B0a, B0b, B1d to replace the three block chart Lebesgue measures by
  `haarK`, `haarA`, `haarN`, and fold `absDetInIwasawaBases` into the `delta(a)` weight
  (`2^{n(n-1)/2} |det a|^n |det adNN a|`).
- B3c `iwasawaIntegrationFormula : integral over G of f d haarG = (scalar) . integral over
  K x A x U of f(k a u) . delta-weight d(haarK x haarA x haarN)`. Final result.

Critical path: B1b' -> B1c' -> B1d (the density weighted K chart and its left invariance under
the Mobius left translation) is the long pole; within B1c', the step 2 measure core is done and the
active blocker is now density of the Cayley image in `SO(n)` for nonemptiness (`KDensityPlan.md`). Level 0
(B0a, B0b) is done and Level 2 B2a (the measure half) has landed; B2b proceeds independently and in
parallel with B1. The final `iwasawaIntegrationFormula` (Level 3, B3a/B3b/B3c) is NOT done.
