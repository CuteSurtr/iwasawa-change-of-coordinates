# Haar Uniqueness Plan for the Iwasawa integration formula

Plan note. Records the strategy, the verified feasibility findings, the exact
target, the weight power, the crux route, and the dependency order. Proves
nothing here. Mathlib facts were read from the pinned copy under
`.lake/packages/mathlib` on 2026-05-28; project facts from the current source.

## Progress (2026-05-28e): T3 and T4 closed in `IwasawaHaar.lean` — crux complete

All axiom clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
- **T3 DONE (the left invariance gate).** `instIsMulLeftInvariant_nuU` plus the
  Haar instances `instIsFiniteOnCompacts_nuU`, `instIsOpenPos_nuU`,
  `instRegular_nuU`, `instIsHaarMeasure_nuU`. Left translation `u ↦ u₀ u` in
  `nnChart` coordinates is the affine map `w ↦ transLin Y w + nnChart u₀` with
  `Y = u₀ - 1`, where `transLin Y` is the conjugate by `nnCoordEquiv` of
  `1 + leftMulNN Y`; `leftMulNN Y` is nilpotent (`leftMulNN_isNilpotent`, from
  T1), so `det (transLin Y) = 1` (`det_transLin` via `LinearMap.det_conj` and
  `det_one_add_of_isNilpotent`). The measure chain uses `map_transLin_volume`
  (`map (transLin Y) volume = volume`) and `map_add_right_eq_self`. Support:
  `nnCoordEquiv`, `leftMulNN`, `fromCoords_eq`, `leftMul_nnChart_symm`,
  `map_transAffine_volume`.
- **T4 DONE (closes the crux).** `mulEquivHaarChar_conjAut_eq_toNNReal_inv` and
  `mulEquivHaarChar_conjAut`: combining T2 (`map_conjAut_nuU`) with `nuU` being
  a regular Haar measure (T3), via `mulEquivHaarChar_eq` and
  `mul_haarScalarFactor_smul` + `haarScalarFactor_self`,
  `mulEquivHaarChar (conjAut a) = (det (adNN a))⁻¹ = δ(a)⁻¹` (stated in both
  `ℝ≥0` and `ℝ` form). The crux measure identity is genuine, not a positivity
  existential.

## PHASE 2 gate (verified 2026-05-28e): GL_n unimodularity / GL_n Haar NOT in Mathlib

A thorough search of the pinned Mathlib confirms the gate for the full
integration formula:
- **No group-theoretic unimodularity.** Only `Matrix.TotallyUnimodular`
  (0/±1 minors) exists; unrelated. No modular-function / `haarChar`-trivial
  predicate, no "Haar on compact/abelian is right invariant" packaged beyond
  `IsMulLeftInvariant.isMulRightInvariant` (abelian only).
- **No Haar on `GL_n`.** `Matrix.GeneralLinearGroup` has the group/`det`
  structure but no topology/measure/Haar. The classical fact "Haar on `GL_n(ℝ)`
  is `|det g|^{-n} d(Lebesgue)`" is not in Mathlib.
- **No `distribHaarChar`/`mulEquivHaarChar` ↔ `det` lemma.** Confirms T4 is
  genuinely novel (we proved it via the explicit `U` Haar).
- **Available:** `map_linearMap_addHaar_eq_smul_addHaar` (and the `volume_pi`
  variants) for `map L volume = |det L|⁻¹ • volume`; `IsMulRightInvariant`
  typeclass; `withDensity`.

Consequence: assembling the genuine integration formula on `G n = GL_n(ℝ)`
requires either (a) an explicit bi-invariant Haar `|det g|^{-n} • volume` on the
open set `GL_n ⊂ Matrix`, proved `IsHaarMeasure` and reconciled with the
abstract `haarG` by uniqueness, then the Iwasawa-map Jacobian; or (b) proving
`G n` unimodular. Both are large multi-lemma constructions, not quick wins.
The crux (T1–T4) is the self-contained, axiom-clean core; the remaining
assembly is gated on this GL_n groundwork.

## Progress (2026-05-28d): T1 and T2 closed in `IwasawaHaar.lean`

All axiom clean.
- **T1 DONE.** `nn_isNilpotent`: a member of `NN n` (strictly upper
  triangular) is nilpotent. Via `charpoly_of_upperTriangular` (charpoly is
  `X ^ n` since the diagonal is zero) and Cayley-Hamilton.
- **T2 DONE (the determinant half of the crux).** `map_conjAut_nuU`:
  `map (conjAut a) nuU = ENNReal.ofReal (det (adNN a)) • nuU`, where
  `nuU := map nnChart.symm volume` is the explicit `U` measure. Built from the
  diagonal map `conjDiag a` (det `= det (adNN a⁻¹) = (det adNN a)⁻¹` via
  `det_adNN_inv` from `adNN` multiplicativity `adNN_adNN_inv` /
  `adNN_comp_adNN_inv`, and `adNN_det_eq_pair_product`), and
  `map_linearMap_addHaar_eq_smul_addHaar`. Supporting: `conjRatio`,
  `conjDiag`, `det_conjDiag`, `det_adNN_pos`.

Remaining:
- **T3 (the left invariance gate).** `nuU` is left invariant, hence a Haar
  measure. Left translation `u ↦ u₀ u` in `nnChart` coordinates is the affine
  map `w ↦ nnChart u₀ + (1 + N) w`, where `N w = ` strict upper entries of
  `Y · S(w)` with `Y = u₀ - 1` and `S` the linear iso to strict upper
  matrices, so `N = S⁻¹ ∘ (left mul by Y) ∘ S` is nilpotent (T1 gives
  `Y` nilpotent), giving `det (1 + N) = 1` by `det_one_add_of_isNilpotent`,
  and the affine map preserves `volume`. This is a large tightly coupled
  piece (the iso `S`, the operator `N`, its nilpotency transfer, the affine
  decomposition, and the measure chain); not yet built.
- **T4 (closes the crux).** From T3 (`nuU` is regular Haar) and T2, via
  `mulEquivHaarChar φ • map φ μ = μ`, conclude
  `mulEquivHaarChar (conjAut a) = (det adNN a)⁻¹ = δ(a)⁻¹`. Needs T3.

## Target theorem

With `iwasawaDiffeomorph : K n × A n × UU n ≃ G n` and the real Haar measures
`haarK`, `haarA`, `haarN`, `haarG` (all `Measure.haar`, `IsHaarMeasure`), and
the product Haar `haarKAU = haarK.prod (haarA.prod haarN)`:

```
Measure.map iwasawaDiffeomorph.symm haarG
  = c • (haarKAU.withDensity (fun p => w p.2.1))
```

for a constant `c > 0` and a weight `w : A n → ℝ≥0∞` that is a power of the
positive root product `δ(a) = det (adNN a) = ∏_{i<j} a_i / a_j`
(`adNN_det_eq_pair_product`). Equivalently the integral form
`∫ f dμ_G = c ∫∫∫ f(iwasawaMap (k,a,u)) · w(a) dμ_K dμ_A dμ_N`.

## Feasibility findings (verified)

1. **Mathlib has the character framework but no determinant lemma.**
   `MeasureTheory.mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0` exists with
   `mulEquivHaarChar φ • map φ μ = μ` (`mulEquivHaarChar_smul_map`, for `μ`
   regular Haar), plus `_eq`, `_trans`, `_symm`, `_refl`,
   `_eq_one_of_compactSpace`. `distribHaarChar (A) : G →* ℝ≥0` exists for a
   `DistribMulAction G A` on an additive group with `addHaar`. But a global
   search shows NO lemma relating either character to `LinearMap.det` /
   `ContinuousLinearEquiv` / a determinant. So crux route (a) has no ready
   made `char = |det|` lemma; the value must be computed via an explicit Haar.

2. **The linear algebra of the crux is already done.**
   `adNN a : NN n →L[ℝ] NN n`, `adNN a X = a.1 * X.1 * a.1⁻¹`
   (`adNN_apply_val`), entrywise `(adNN a X) i j = (a_i / a_j) * X i j`
   (`adNN_entry`), diagonal in `nnBasis` (`adNN_toMatrix_diagonal`), and
   `LinearMap.det (adNN a) = ∏_{i<j} a_i / a_j = δ(a)`
   (`adNN_det_eq_pair_product`).

3. **The conjugation and its chart form.** The strategy's right A move uses
   `c_{a₀} : u ↦ a₀⁻¹ u a₀`. In the chart `UU.toNNHomeomorph : UU n ≃ₜ NN n`
   (`u ↦ u - 1`), since `a₀⁻¹ (1 + X) a₀ = 1 + a₀⁻¹ X a₀`, the chart form of
   `c_{a₀}` is the linear map `X ↦ a₀⁻¹ X a₀ = adNN (a₀⁻¹)` on `NN n`, with
   `LinearMap.det (adNN (a₀⁻¹)) = δ(a₀)⁻¹` (since `δ(a₀⁻¹) = δ(a₀)⁻¹`).

4. **Weight power (pinned).** Using `map_linearMap_addHaar_eq_smul_addHaar`
   (`map L μ = |det L|⁻¹ • μ`) and the chart, an explicit U Haar `ν` satisfies
   `map c_{a₀} ν = |δ(a₀)⁻¹|⁻¹ • ν = δ(a₀) • ν`. So `mulEquivHaarChar c_{a₀}
   = δ(a₀)⁻¹`, equivalently the right A conjugation scales U Haar by `δ(a₀)`.
   The weight `w` that makes the pullback right A invariant is therefore a
   fixed power of `δ`; the exact exponent (and `c`) are fixed in PHASE 3.

5. **GL_n unimodularity.** `G n` is locally compact; bi invariance of `haarG`
   follows from `IsHaarMeasure` plus unimodularity. To confirm in Mathlib:
   `IsHaarMeasure` is left invariant by definition; right invariance needs
   `IsMulRightInvariant haar`, available for unimodular groups. Check
   `Mathlib/MeasureTheory/.../Unimodular` for the GL_n route, or derive right
   invariance of the relevant transport directly.

## The crux and its real obstruction

The crux is the measure equation `map c_{a₀} (U Haar) = δ(a₀) • (U Haar)`.
By finding 2 to 4, the only missing ingredient is an explicit regular Haar
measure on `U` that can be computed in coordinates, because the abstract
`haarN = Measure.haar` is opaque and `mulEquivHaarChar c_{a₀}` can only be
evaluated against a Haar measure whose pushforward we can compute.

The explicit U Haar `ν` is the pushforward of Lebesgue under a chart
`U ≃ (coordinate space)`. To be a Haar measure it must be left invariant.
Left translation by `u₀ = 1 + Y` in chart coordinates is the affine map
`X ↦ (1 + Y)(1 + X) - 1 = X + Y + Y X`, whose linear part is `1 + M_Y` with
`M_Y(X) = Y X` (restricted to strict upper). `M_Y` is nilpotent (it strictly
raises the lower index gap), so `det (1 + M_Y) = 1` and left translation
preserves Lebesgue: this is "Haar on a unipotent group is Lebesgue in
exponential coordinates."

**Obstruction (the real gate).** Building `ν` needs `addHaar`/Lebesgue on the
Lie algebra coordinate space and the `|det|` scaling lemmas, which require a
`NormedAddCommGroup` + `NormedSpace ℝ` on that space whose topology matches
the chart's topology. `NN n` is a `Submodule` and the project activates the
`Matrix` norm only locally, so giving `NN n` a global normed instance risks a
topology diamond with the existing subtype topology used by
`UU.toNNHomeomorph`. The clean sidestep is a direct homeomorphism
`UU n ≃ₜ (nnIndex n → ℝ)` to the clean normed Pi space (volume is the
standard `addHaar`), in which the conjugation is the diagonal scaling
`(i,j) ↦ (a_j / a_i)` and the left translation Jacobian is `det (1 + M_Y) = 1`.

## Progress (2026-05-28c): chain partially built in `IwasawaHaar.lean`

All axiom clean.
- **C1 DONE.** `conjAut a : UU n ≃ₜ* UU n`, conjugation `u ↦ a⁻¹ u a`, with
  `conjAut_mem`, `conjAut_mem'`, `conjAut_apply_val`. Membership via the public
  chart and `adNN` (no private dependencies).
- **C2 DONE.** `nnChart : UU n ≃ₜ (nnIndex n → ℝ)` (strict upper entries),
  with `fromCoords` and `fromCoords_isUpperUnipotent`. Built in the product
  topology, so the `NN n` normed structure is sidestepped entirely.
- **C5 core DONE.** `conjAut_nnChart_apply`: through the chart, `conjAut a`
  multiplies coordinate `ij` by `(a⁻¹)_{i i} / (a⁻¹)_{j j}`, i.e. it is the
  diagonal scaling matching `adNN a⁻¹`. Proved with public lemmas only.
- Already available: `det_one_add_of_isNilpotent` (the C4 determinant input).

Remaining: the diagonal map's determinant equals `det (adNN a⁻¹) = δ(a)⁻¹`
(via `Matrix.det_diagonal` and `adNN_det_eq_pair_product`); the measure
identity `map (conjAut a) νU = δ(a) • νU` for `νU := map nnChart.symm volume`
(via `map_linearMap_addHaar_eq_smul_addHaar`); C3/C4 left invariance of `νU`
(the affine Jacobian `det (1 + M_Y) = 1`, using the proved nilpotent
determinant lemma) to upgrade to `mulEquivHaarChar (conjAut a) = δ(a)⁻¹`; then
the PHASE 3/4 assembly.

## Dependency ordered plan

- C0 (have): `adNN`, `adNN_entry`, `adNN_det_eq_pair_product`,
  `UU.toNNHomeomorph`, `nnBasis`, `haarN`, `mulEquivHaarChar` framework.
- C1 `[medium]`: the conjugation as a continuous group automorphism
  `conjAut a₀ : UU n ≃ₜ* UU n`, `u ↦ a₀⁻¹ u a₀` (well defined into `UU n`,
  group hom, continuous both ways).
- C2 `[medium]`: a direct chart `nnChart : UU n ≃ₜ (nnIndex n → ℝ)` (strict
  upper entries), avoiding the `NN n` normed diamond.
- C3 `[medium]`: `nnChart ∘ conjAut a₀ ∘ nnChart.symm` is the diagonal linear
  map `D_{a₀} : (i,j) ↦ (a_j / a_i) • coordinate`, and
  `LinearMap.det D_{a₀} = δ(a₀)⁻¹` (direct product over `nnIndex`, or via
  `adNN_det_eq_pair_product` transported through `nnBasis`).
- C4 `[HARD, the gate]`: `νU := map nnChart.symm volume` is left invariant,
  hence a regular Haar measure on `UU n`. Needs the affine decomposition of
  left translation and `det (1 + M_Y) = 1` for the nilpotent `M_Y`. Mathlib:
  `map_linearMap_addHaar_eq_smul_addHaar`, plus a nilpotent `det (1 + N) = 1`
  (matrix version exists; LinearMap version may need transport via a basis).
- C5 `[medium, given C2 to C4]`: `map (conjAut a₀) νU = δ(a₀) • νU` via
  `map_map` and C3 and `map_linearMap_addHaar`.
- C6 `[medium]`: `mulEquivHaarChar (conjAut a₀) = δ(a₀)⁻¹` via
  `mulEquivHaarChar_eq νU` and C5; equivalently `map (conjAut a₀) haarN =
  δ(a₀) • haarN` after relating `haarN` and `νU` by Haar uniqueness
  (`measure_isHaarMeasure_eq_smul_of_isOpen`).
- P3 (PHASE 3): the three invariances of the pullback (left K from `haarK`
  uniqueness, right U from U unimodularity, right A from C6 pinning `w`), then
  per factor uniqueness to assemble the target.
- P4 (PHASE 4): the integral form with `c > 0` and weight `w`.

C4 is the gate. If C4 cannot be closed without a sorry or an axiom (for
example if the nilpotent `det (1 + M_Y) = 1` as a `LinearMap` on
`nnIndex n → ℝ` proves intractable, or the chart construction snags), STOP:
that determines reachability of the whole theorem this session.
