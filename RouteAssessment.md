# Iwasawa integration formula: route assessment (branch `haar-assembly`)

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
Level 0 (factor Haar identifications by uniqueness; reuse PHASE 1 regularity pattern):
- B0a `haarAExplicit_eq_smul_haarA : haarAExplicit = haarScalarFactor haarAExplicit haarA . haarA`
  (A is locally compact abelian, second countable; same uniqueness step as `nuG = c . haarG`).
- B0b `nuU_eq_smul_haarN : nuU = haarScalarFactor nuU haarN . haarN` (same, for U).

Level 1 (the K chart):
- B1a `cayleyK` per component: an `OpenPartialHomeomorph` (or local diffeo) from an open
  subset of `Sk n` onto an open dense subset of each component of `K n`; off chart set
  is closed of measure zero.
- B1b `cayleyK` is `C^1` with invertible derivative (for the change of variables and the
  chart pushforward); record `|det D cayleyK|` if the Riemannian route is taken.
- B1c `nuK := map cayleyK.symm volume` is left `K` invariant (direct computation of left
  multiplication in Cayley coordinates), hence a Haar measure on `K`.
- B1d `nuK_eq_smul_haarK : nuK = c_K . haarK` by `haarMeasure_unique` (K compact, chart free);
  off chart complement is `haarK` null and `nuK` null.

Level 2 (the change of variables on the full chart):
- B2a `haarG_integral_eq_coord : integral over G of f d haarG = (scalar) . integral over the
  coordinate space of (f restricted) . detWeightCoord d volume`, from
  `nuG = c . haarG`, `haarGCoord = volume.withDensity detWeightCoord`, and `comap` apply.
- B2b apply `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (or the
  `integral_target_eq_integral_abs_det_fderiv_smul` chart form) to `iwasawaCharted`,
  using `absDetInIwasawaBases` as `|det fderiv|`, giving the integral over `G` as an
  integral over the chart domain in `Sk x (Fin n -> R) x NN` against Lebesgue with weight
  `absDetInIwasawaBases`.

Level 3 (assembly):
- B3a factor the chart domain Lebesgue measure as a product over the `Sk`, diagonal, and
  `NN` blocks (`Measure.prod`, `volume_pi`), aligning `iwasawaCharted` with
  `iwasawaMap` composed with the three factor charts.
- B3b substitute B0a, B0b, B1d to replace the three block chart Lebesgue measures by
  `haarK`, `haarA`, `haarN`, and fold `absDetInIwasawaBases` into the `delta(a)` weight
  (`2^{n(n-1)/2} |det a|^n |det adNN a|`).
- B3c `iwasawaIntegrationFormula : integral over G of f d haarG = (scalar) . integral over
  K x A x U of f(k a u) . delta-weight d(haarK x haarA x haarN)`. Final result.

Critical path: B1a -> B1b -> B1c -> B1d (the K chart) is the long pole; B0a, B0b and
B2a, B2b can proceed independently and in parallel with B1.
