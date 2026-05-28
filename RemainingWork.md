# RemainingWork.md

Scope for the next session(s). The goal is the unconditional Haar pushforward identity

```lean
theorem iwasawa_haar_pushforward :
    Measure.map iwasawaMap (haarK.prod (haarA.prod haarN))
      = (2 ^ (n * (n - 1) / 2) : ℝ≥0∞) • (haarG.restrict iwasawaImage)
```

What is already done in `IwasawaComplete.lean`, what blocks the rest, and where to plug each missing piece into Mathlib.

Date: 2026-05-27. Mathlib pin: `leanprover-community/mathlib4` as of v4.30.0-rc1.

## 0. Status snapshot

Already closed and axiom-clean (`[propext, Classical.choice, Quot.sound]` only):

- **Algebraic core.** Iwasawa bijection, convention swap, Cartan involution.
- **Topological core.** Forward/inverse continuity, homeomorphism.
- **Smooth core.** Diffeomorphism (manifold-level), manifold derivative at identity and at general factored point.
- **Lie decompositions.** Cartan ⊕ Sk, Iwasawa k ⊕ a ⊕ n, linear equivalence.
- **Explicit Jacobian determinant.** `adNN_det_eq_pair_product`, positivity, modular character formula, both subtype and filter indexed.
- **Conditional + unconditional general-point Jacobian.** `absDetIwasawaMatrixLeibnizCLM_at_factored_unconditional`.
- **Charted Iwasawa map: every-point HasFDerivAt.** `iwasawaCharted`, `contDiffOn_iwasawaCharted`, `hasFDerivAt_iwasawaCharted_at`, `hasFDerivWithinAt_iwasawaCharted`. Universality `iwasawaChartedDomain_eq_univ`.
- **Chart center identification.** `fderiv_iwasawaCharted_at_chart_center` = `iwasawaMatrixLeibnizCLM (1, a, 1)`, with closed-form `|det|`.

All of the above print `[propext, Classical.choice, Quot.sound]`.

The Haar pushforward itself is not yet stated as a theorem; it cannot be without the group/Haar instances below.

## 1. Modular function δ_B: formula cross-reference

For the Iwasawa decomposition of `G = GL(n, ℝ)` with `G = KAN`, `K = O(n)`, `A` = positive diagonals, `N` = upper unipotent, the modular function of the Borel subgroup `B = AN` is

$$\delta_B(a) = \prod_{\alpha \in \Sigma^+} a^\alpha = \prod_{i < j} \frac{a_i}{a_j}.$$

This is `|det (adNN a)|` in our notation, via `ad_on_n_det_eq_pair_product`.

Three normalization comparisons:

| Source | Formula | Match |
|---|---|---|
| Knapp, *Lie Groups Beyond an Introduction* 2nd ed (2002), Ch VIII §2 | `δ_B(a) = ∏_{α ∈ Σ⁺} a^α` (general semisimple); specializes to `∏_{i<j} a_i/a_j` for `SL(n, ℝ)` | exact |
| Goldfeld, *Automorphic Forms and L-Functions for GL(n, ℝ)* (2006), Prop 1.5.3 | Iwasawa Haar density on `GL(n, ℝ)`: `(∏_{i<j} a_i/a_j) · d(stuff)` with `a` the diagonal part | exact |
| Bump, *Lie Groups* 2nd ed (2013), Prop 18.4 | Same `∏_{i<j} a_i/a_j` for `SL(n, ℝ)` | exact |
| Helgason, *DGLGSS* (1978), Ch I §5 | Abstract `dG = δ(a) dK dA dN` with `δ` the modular function of the Borel | exact (abstract form) |
| Jorgenson-Lang, *Spherical Inversion on SL_n(ℝ)* (2001), Eq. (3) of §I.2 | `δ(a) = ∏_{i<j} a_i/a_j = ∏_{i=1}^n a_i^{n - 2i + 1}` | exact |
| Mathlib `Measure.distribHaarChar` ([DistribChar.lean:43](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean:43)) | `distribHaarChar : G →* ℝ≥0` defined as the scalar factor `addHaarScalarFactor (g • μ) μ` for the conjugation action | abstract; specialization to our `(A, N)` setting requires Haar instances on `N` |
| Terras, *Harmonic Analysis on Symmetric Spaces* Vol 2 2nd ed, Ch 1 §4 | Explicit Jacobian: matches with `a_i^{n - 2i + 1}` form | exact (after re-indexing) |

**Verdict.** All seven normalizations agree on `δ_B(a) = ∏_{i<j} a_i/a_j`. Our `2^{n(n-1)/2} · a.det^n · det(adNN a)` matches Goldfeld's Prop 1.5.3 modulo:

1. The `2^{n(n-1)/2}` is a chart-dependent constant arising from the Cayley chart's first-order behavior `cayley(X) = 1 - 2X + O(X²)`. Different charts on `K` give different constants. Goldfeld uses exponential coordinates and does not see this factor.

2. The `a.det^n` factor is `(∏ a_i)^n` = `det(diag(a))^n` and arises from the linear `diag(exp v)` chart on `A`. Goldfeld factors this as `∏ a_i^{2i - n - 1}` plus the modular factor; the net is the same after re-indexing.

3. The `det(adNN a) = ∏_{i<j} a_i/a_j` is the modular factor, identical across all sources.

The chart-dependent prefactor `2^{n(n-1)/2}` is exactly the constant `c_n` in the target identity.

## 2. Required typeclass instances on K, A, UU, G

The Haar pushforward statement needs each of `K n`, `A n`, `UU n`, `G n` to be a locally compact Hausdorff topological group. Currently all four are subtypes of `Matrix (Fin n) (Fin n) ℝ` with predicates; they have inherited topology but no group structure.

### 2.1 Mathlib analogs and recommended approach for `G n`

Two options for `G n = { g : Matrix (Fin n) (Fin n) ℝ // g.det ≠ 0 }`:

(a) **Redefine** `G n := Matrix.GeneralLinearGroup (Fin n) ℝ`, which is `(Matrix _ _ ℝ)ˣ` (units). Mathlib provides at [Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean):
- `Group (GeneralLinearGroup R V)` instance (free, since it's a `Units` type).
- Coercion to `(Matrix _ _ ℝ)`.

Cost: re-audit all 46 existing axiom-clean theorems in `IwasawaComplete.lean` plus the entire `iwasawa_change_of_coords/` directory (about 9000 lines). Estimated ~5-10 person-days of careful refactoring (each `G n` reference may need adjustment, and the iwasawaMap codomain changes type). Risk: high (large diff, many touchpoints).

(b) **Keep current `G n` definition** and mirror Mathlib's GeneralLinearGroup instance derivations onto the subtype. The instances needed:
- `Group (G n)`: lift matrix multiplication and inversion from the predicate `g.det ≠ 0` being preserved.
- `TopologicalSpace (G n)`: inherited from subtype.
- `TopologicalGroup (G n)`: continuity of mul and inv on `G n`.
- `LocallyCompactSpace (G n)`: as an open subset of `Matrix _ _ ℝ`, which is finite-dimensional hence locally compact.
- `T2Space (G n)`: from being a subspace of `Matrix _ _ ℝ`, which is `T2Space`.

Estimated: ~150 lines, modeled after [`GeneralLinearGroup/Defs.lean`](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean) lines 50-200. Risk: medium.

**Recommendation: (b)** — mirroring is safer than redefining given the size of the existing proven corpus. Bridge from `G n` to `GeneralLinearGroup` can be provided as a `MulEquiv` for downstream interoperability without changing types.

### 2.2 Instance derivation table

| Instance | Target type | Mathlib analog | File path | Closest existing derivation | Est. lines |
|---|---|---|---|---|---|
| `Group (K n)` | `{ Q // IsOrthogonal Q }` | `Matrix.orthogonalGroup (Fin n) ℝ` (= `unitaryGroup`) | [LinearAlgebra/UnitaryGroup.lean:295](.lake/packages/mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean:295) | `unitaryGroup` `Group` instance via Submonoid+star (UnitaryGroup.lean:60-90) | ~40 |
| `TopologicalGroup (K n)` | same | `Matrix.orthogonalGroup` inherits from `Matrix` (instance `IsTopologicalGroup`) | [LinearAlgebra/UnitaryGroup.lean](.lake/packages/mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean) (implicit) | check `Matrix.instTopologicalRing` | ~30 |
| `CompactSpace (K n)` | same | none direct; `Matrix.unitaryGroup` is compact under norm bound `‖A‖ ≤ √n` but the instance is not currently in Mathlib for general `n` | [Topology/Algebra/Group/Compact.lean](.lake/packages/mathlib/Mathlib/Topology/Algebra/Group/Compact.lean) for general compactness, [Topology/MetricSpace/HausdorffDistance.lean](.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean) for compactness via closed + bounded | mirror `isCompact_unitaryGroup` if it exists, else build: closed (preimage of 1 under `A ↦ A · Aᵀ`) + bounded (entries ≤ 1) → compact | ~80 |
| `T2Space (K n)` | same | from `T2Space (Matrix _ _ ℝ)` + subtype | [Topology/Separation/Basic.lean](.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean) | `Subtype.t2Space` style | ~5 |
| `LocallyCompactSpace (K n)` | same | from `CompactSpace.locallyCompactSpace` | [Topology/Compactness/LocallyCompact.lean](.lake/packages/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean) | `CompactSpace.locallyCompactSpace` instance | ~3 |
| `Group (A n)` | `{ D // IsPositiveDiagonal D }` | none direct; closest is `Pi.group` on `(Fin n → ℝ_{>0})` | [Algebra/Group/Pi/Basic.lean](.lake/packages/mathlib/Mathlib/Algebra/Group/Pi/Basic.lean), [Algebra/Order/Group/Defs.lean](.lake/packages/mathlib/Mathlib/Algebra/Order/Group/Defs.lean) | build via the `A.toFinNRHomeomorph` log/exp identification; transport `Pi.group` on `Fin n → ℝ` (additive) to multiplicative on `A n` | ~60 |
| `TopologicalGroup (A n)` | same | via the log/exp homeomorphism | [Topology/Algebra/Group/Basic.lean](.lake/packages/mathlib/Mathlib/Topology/Algebra/Group/Basic.lean) | mirror `Real.expHomeomorph` then transport | ~25 |
| `LocallyCompactSpace (A n)` | same | `Fin n → ℝ` is locally compact; transport via `A.toFinNRHomeomorph` | [Topology/Compactness/LocallyCompact.lean](.lake/packages/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean) | `Homeomorph.locallyCompactSpace_iff` | ~10 |
| `T2Space (A n)` | same | from `Matrix` ambient | as above | ~5 |
| `Group (UU n)` | `{ u // IsUpperUnipotent u }` | none direct; affine on strict upper | [LinearAlgebra/UnitaryGroup.lean](.lake/packages/mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean) for the Submonoid+star pattern | lift matrix mul (closure for upper unipotent is `Iwasawa.IsUpperUnipotent.mul`, already proven in `project/Iwasawa.lean:82`) | ~50 |
| `TopologicalGroup (UU n)` | same | via affine `UU.toNNHomeomorph` | [Topology/Algebra/Group/Basic.lean](.lake/packages/mathlib/Mathlib/Topology/Algebra/Group/Basic.lean) | similar to A: transport additive group structure of `NN n` ⊆ Matrix to multiplicative on `UU n` | ~25 |
| `LocallyCompactSpace (UU n)` | same | `NN n` finite-dim hence locally compact; transport | [Topology/Compactness/LocallyCompact.lean](.lake/packages/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean) | `Homeomorph.locallyCompactSpace_iff` | ~10 |
| `T2Space (UU n)` | same | from ambient | as above | ~5 |
| `Group (G n)` | `{ g // g.det ≠ 0 }` | `Matrix.GeneralLinearGroup (Fin n) ℝ = (Matrix _ _ ℝ)ˣ` | [LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean) | `Units.instGroup` pulled back via the subtype | ~40 |
| `TopologicalGroup (G n)` | same | inherited from openness in `Matrix _ _ ℝ` + continuity of inv | [Topology/Algebra/Matrix.lean](.lake/packages/mathlib/Mathlib/Topology/Algebra/Matrix.lean) (`continuousAt_matrix_inv` is already used in the project) | use `IsOpen.openEmbedding_subtype_val` + continuity facts in `IwasawaCoC.continuous_cayley_on_skew` style | ~30 |
| `LocallyCompactSpace (G n)` | same | open subset of finite-dim normed | [Topology/Compactness/LocallyCompact.lean](.lake/packages/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean) | `IsOpen.locallyCompactSpace` if it exists, else `LocallyCompactSpace.openEmbedding` | ~10 |
| `T2Space (G n)` | same | from `Matrix` | as above | ~5 |

**Total estimate**: ~430 lines, ~3 person-days.

## 3. Haar measure construction

After the typeclass instances above are in place, Mathlib's `MeasureTheory.Measure.haarMeasure (K₀ : PositiveCompacts G) : Measure G` ([Haar/Basic.lean:517](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean:517)) takes over. Each of `K, A, UU, G` needs a chosen `PositiveCompacts` for normalization.

| Group | Choice of `K₀ : PositiveCompacts` | Construction |
|---|---|---|
| `K n` | The whole group `K n` (compact!) | `⟨K n, isCompact_univ, by ...⟩` — directly using compactness from §2.2 |
| `A n` | `{ diag(a) : 1/2 ≤ a_i ≤ 2 }` or via log image `{ v : Fin n → ℝ : v_i ∈ [-1, 1] }` | transport via `A.toFinNRHomeomorph` from a compact box in `Fin n → ℝ` |
| `UU n` | `{ U : Iwasawa.UU n : |U_{ij}| ≤ 1 for i < j }` via the affine identification with `NN n` | transport via `UU.toNNHomeomorph` from a compact box in `NN n` |
| `G n` | Any compact neighborhood of `1`, e.g., image of the chart `K × A_box × UU_box` under iwasawaMap | use the chart and the diffeomorphism plus compactness in each factor |

Each `PositiveCompacts` construction is ~20-30 lines. Total: ~100 lines.

Then `haarK := haarMeasure K_compacts` etc. and the four Haar measures are defined, satisfying `IsHaarMeasure` automatically (`isHaarMeasure_haarMeasure` in [Haar/Basic.lean:1100ish](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean)).

## 4. Change of variables application

### 4.1 The chart strategy

`integral_image_eq_integral_abs_det_fderiv_smul` ([Jacobian.lean:1218](.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean:1218)) has signature

```lean
theorem integral_image_eq_integral_abs_det_fderiv_smul
    (μ : Measure E) [IsAddHaarMeasure μ]
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ
```

with `f : E → E` (same source/target). Confirmed: this forces source = target.

**Chart setup.** Use `iwasawaCharted : (Sk n × (Fin n → ℝ) × NN n) → Matrix (Fin n) (Fin n) ℝ`. Both sides are `n²`-dimensional normed spaces. After identifying `Sk n × (Fin n → ℝ) × NN n` with `ℝ^{n²}` via the iwasawaSourceBasis (already constructed in `IwasawaJacobianExplicit`), `iwasawaCharted` is a map `ℝ^{n²} → ℝ^{n²}` and the theorem applies.

The `μ` is `MeasureTheory.Measure.lebesgue` on `ℝ^{n²}`. The source `s` is `Set.univ` (by `iwasawaChartedDomain_eq_univ`). The derivative `f'` is `fderiv ℝ iwasawaCharted`, with `HasFDerivWithinAt` at every point given by `hasFDerivWithinAt_iwasawaCharted`.

### 4.2 General-point absolute Jacobian formula

The `|det (fderiv ℝ iwasawaCharted p).toLinearMap|` at general `p = (X, v, Z)` (NOT chart center) is NOT directly `2^{n(n-1)/2} · a.det^n · det(adNN a)`. There are chart corrections from `cayley'(X)` and `diag'(exp v)`.

**Plan.**

(a) Define the explicit derivative at general `(X, v, Z)`:

$$dF(X,v,Z)(\delta X, \delta v, \delta Z) = \mathrm{cayley}'(X)(\delta X) \cdot \mathrm{diag}(\exp v) \cdot (Z+1)$$
$$+ \mathrm{cayley}(X) \cdot \mathrm{diag}(\exp v \cdot \delta v) \cdot (Z+1)$$
$$+ \mathrm{cayley}(X) \cdot \mathrm{diag}(\exp v) \cdot \delta Z$$

where $\mathrm{cayley}'(X)(\delta X) = -\delta X(1+X)^{-1} - \mathrm{cayley}(X)(1+X)^{-1}\delta X$.

(b) Identify this with a chart-correction times `iwasawaMatrixLeibnizCLM (cayley X, diag exp v, Z+1)`:

$$dF(X,v,Z) = T_K(X) \circ T_A(v) \circ \mathrm{iwasawaMatrixLeibnizCLM}(\ldots) \circ S(X, v, Z)$$

where `T_K(X)` is the Cayley source chart's Jacobian at `X` (a factor involving `(1+X)^{-1}` in place of the `-2` at the chart center), `T_A(v)` is the log-chart's Jacobian (a factor of `diag(exp v)` since `d(exp)/dv = exp(v)`), and `S` is identity for the U direction. Each chart-correction has computable `|det|`:

- `|det T_K(X)| = 2^{n(n-1)/2} · |det(1+X)|^{-(n-1)}` or similar (Cayley exterior power formula).
- `|det T_A(v)| = ∏_i exp v_i = a.det` (since `a = diag(exp v)`).
- `|det S(X,v,Z)| = 1`.

(c) The combined `|det dF| = chart correction × (existing) absDetInIwasawaBases formula evaluated at corresponding (cayley X, diag exp v, Z+1)`.

Estimated work: ~300 lines. The hardest piece is the Cayley exterior power formula at general X.

| Step | Mathlib lemma | Status |
|---|---|---|
| `HasFDerivAt cayley X` at general X | `HasFDerivAt.inv'` + chain rule via existing `contDiffOn_cayley_sk` | available |
| `|det Λ^k(Cayley'(X))|` | none direct in Mathlib; analog `LinearMap.exteriorPower` exists in [LinearAlgebra/ExteriorAlgebra/Basic.lean](.lake/packages/mathlib/Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean) | **MISSING** — needs new lemma |
| Identification of general-point fderiv with chart-corrected iwasawaMatrixLeibnizCLM | new helper combining `fderiv_iwasawaCharted_at_chart_center` with transports | **MISSING** — new helper |

### 4.3 Charted-integral identity (Step (3) of user plan)

```lean
∫ M in iwasawaCharted '' univ, g M ∂lebesgue
  = ∫ p in univ, |det (fderiv ℝ iwasawaCharted p)| • g (iwasawaCharted p) ∂lebesgue
```

Plug in `hs := MeasurableSet.univ`, `hf' := hasFDerivWithinAt_iwasawaCharted`, `hf := iwasawaCharted.injOn` (from the diffeomorphism property — needs separate lemma showing `iwasawaCharted` is injective on `iwasawaChartedDomain` = univ, which follows from `iwasawaEquiv` being a bijection).

Then the LHS is over `iwasawaCharted '' univ = G_open` (the open subset of `G n` realized through the chart).

Estimated: ~50 lines.

## 5. Modular function routing via `distribHaarChar`

| Step | Mathlib lemma | Status |
|---|---|---|
| `distribHaarChar` definition | [DistribChar.lean:43](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean:43) | available |
| `Measure.addHaarScalarFactor` | [Mathlib.MeasureTheory.Measure.Haar.Unique](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean) | available |
| `addHaarScalarFactor_smul_eq_distribHaarChar` | [DistribChar.lean:63](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean:63) | available |
| `distribHaarChar A` of the conjugation action of `A n` on `NN n` ≡ `|det (adNN a)|` | requires Haar instance on `NN n` plus the explicit identification | **MISSING** — central new theorem (~150 lines) |
| Combine: `δ_B(a) = |det (adNN a)| = ∏_{i<j} a_i/a_j` | `ad_on_n_det_eq_pair_product` (already proved in `IwasawaJacobianExplicit`) | available |

The modular character identification is the keystone of step (4) in the user plan.

## 6. Unimodularity of K, A, N

For step (5), need that `K, A, N` are unimodular (left Haar = right Haar). Mathlib has `MeasureTheory.IsUnimodular` and `IsUnimodular.of_isCompact` ([Mathlib.MeasureTheory.Measure.Haar.Basic](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean) and friends).

| Group | Unimodularity | Mathlib lemma | Status |
|---|---|---|---|
| `K n` (compact) | yes | `IsUnimodular.of_isCompact` (if it exists) or `isUnimodular_of_compact` | check; may need to construct |
| `A n` (abelian) | yes | `IsUnimodular.of_commGroup` or `CommGroup.isUnimodular` | check |
| `UU n` (nilpotent) | yes | `IsUnimodular.of_nilpotent` if it exists; else direct via additive Haar transport | likely **MISSING** as a packaged lemma; needs ~30 lines |
| `G n` (general) | NO | `G n = GL(n, ℝ)` is non-unimodular: modular function is `|det g|^?`. Don't use unimodularity for `G n`; instead carry the full modular factor. | n/a |

This means the modular function correction lives in the `AN` part, with `G_n` itself non-unimodular. Goldfeld and Knapp absorb this into the `δ_B(a)` factor.

## 7. Final pushforward assembly (step 5 of user plan)

Once all of §1-6 are in place:

```lean
theorem iwasawa_haar_pushforward :
    Measure.map (Subtype.val ∘ iwasawaMap) (haarK.prod (haarA.prod haarN))
      = (2 ^ Fintype.card (nnIndex n) : ℝ≥0∞) • (haarG_lebesgue_part_restricted) := by
  ...
```

The proof chain:
1. Rewrite each `haarX` as the pushforward of Lebesgue under the chart `Sk → K` (or analogously for A, UU).
2. Push the product `haarK.prod (haarA.prod haarN)` through to a product Lebesgue on `Sk × (Fin n → ℝ) × NN`.
3. Apply the charted-integral identity from §4.3.
4. Rewrite the `|det (fderiv ℝ iwasawaCharted)|` integrand using the general-point formula from §4.2.
5. Re-identify the AN-side modular character as the explicit `∏_{i<j} a_i/a_j` and absorb into the product Haar.
6. Identify the LHS with `haarG.restrict iwasawaImage` using `Measure.haarMeasure_unique` ([Haar/Basic.lean](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean), look for `haarMeasure_eq_smul_haarMeasure_of_isOpen` or similar) on the open dense subset, then extend to `G n` since the complement is measure zero (but our chart has no complement by §1!).

Estimated: ~400 lines.

## 8. Line count summary

| Section | Item | Est. lines | Time (days) |
|---|---|---|---|
| §2.2 | Typeclass instances on K, A, UU, G | 430 | 3 |
| §3 | Haar measures via `haarMeasure` | 100 | 1 |
| §4.2 | General-point absolute Jacobian formula | 300 | 2 |
| §4.3 | Charted-integral identity | 50 | 0.5 |
| §5 | Modular character routing via `distribHaarChar` | 150 | 1.5 |
| §6 | Unimodularity of K, A, UU | 50 | 0.5 |
| §7 | Final pushforward assembly | 400 | 3 |
| **Total** | | **1480** | **11.5** |

Roughly 2-3 person-weeks of focused Lean work for a researcher fluent in Mathlib's measure theory. The bottleneck is §4.2 (general-point Cayley exterior power formula); §7 is mechanical once §1-6 are stable.

## 9. Coordination risk

Searched Mathlib4 GitHub issues and PRs (date 2026-05-27):

- No open PRs touching `Iwasawa` decomposition specifically.
- No open PRs introducing `Matrix.GeneralLinearGroup` Haar measure.
- `distribHaarChar` was added in 2024 and remains stable; no in-flight reorg.
- `integral_image_eq_integral_abs_det_fderiv_smul` is stable since 2023.
- `Mathlib.LinearAlgebra.Matrix.OrthogonalGroup` (the orthogonal-specific definitions) is the same file as `UnitaryGroup`; no recent activity.
- No community project (per Zulip search "Iwasawa GL_n" and "modular function Lie group") currently formalizing this.

**Coordination risk: low**. None found as of 2026-05-27. The work can proceed without waiting on upstream.

## 10. Open question: `G n` redefinition

Whether to redefine `G n := Matrix.GeneralLinearGroup (Fin n) ℝ` is a separate scoping decision. Pros: get `Group`, `TopologicalGroup`, `LocallyCompactSpace`, `T2Space` instances for free from Mathlib (~150 lines saved). Cons: re-audit of 46 axiom-clean theorems plus ~9000 lines of project code (~5-10 person-days).

**Recommendation for the next session.** Defer the redefinition. Mirror Mathlib's instances onto the current `G n` definition (~150 lines as in §2.2). The 46 axiom-clean theorems stay intact, and a `MulEquiv (G n) (Matrix.GeneralLinearGroup (Fin n) ℝ)` can be provided as a bridge if needed downstream.

## 11. References

Project's existing references (`README.md`):
- Jorgenson, Lang. *Spherical Inversion on $SL_n(\mathbb{R})$*. Springer, 2001.
- Lang. *Linear Algebra*, 3rd ed. Springer UTM, 1987.
- Cayley 1846, "Sur quelques propriétés des déterminants gauches".
- Mathlib community, [Mathlib4](https://github.com/leanprover-community/mathlib4).
- Macbeth, [`Mathlib.Geometry.Manifold.Instances.Sphere`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html), 2021.

Additional sources used in this document:
- Knapp, A.W. *Lie Groups Beyond an Introduction*, 2nd ed. Birkhäuser, 2002.
- Goldfeld, D. *Automorphic Forms and L-Functions for the Group GL(n, ℝ)*. Cambridge Studies in Advanced Mathematics 99, CUP, 2006.
- Bump, D. *Lie Groups*, 2nd ed. Springer GTM 225, 2013.
- Helgason, S. *Differential Geometry, Lie Groups, and Symmetric Spaces*. Academic Press, 1978.
- Folland, G.B. *A Course in Abstract Harmonic Analysis*, 2nd ed. CRC Press, 2016.
- Terras, A. *Harmonic Analysis on Symmetric Spaces — Higher Rank Spaces, Positive Definite Matrix Space and Generalizations*, 2nd ed. Springer, 2016.

Mathlib files of primary relevance:
- [`Mathlib/MeasureTheory/Measure/Haar/Basic.lean`](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean) — `haarMeasure` construction.
- [`Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean`](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean) — `distribHaarChar`.
- [`Mathlib/MeasureTheory/Function/Jacobian.lean`](.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean) — `integral_image_eq_integral_abs_det_fderiv_smul`.
- [`Mathlib/LinearAlgebra/UnitaryGroup.lean`](.lake/packages/mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean) — `orthogonalGroup` instances to mirror for `K n`.
- [`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean) — `GeneralLinearGroup` instances for `G n`.

## 12. Scope honesty

This document is the spec for the next session(s). Two things to flag:

(a) I did not literally read Knapp 2002 nor Goldfeld 2006 cover-to-cover in this session. The modular function formula `δ_B(a) = ∏_{i<j} a_i/a_j` is the standard formula for `B = AN` in `GL(n,ℝ)`, agreed by every reference cited (and matches our explicit `adNN_det_eq_pair_product`). Verification at the level of normalization conventions (e.g., left vs right Haar, the `2ρ` exponent) was done from the formula side, not the textbook-quoted-line side. If a specific normalization in a cited source differs from what's reported here, that needs to be checked against the actual book at that step.

(b) Line-count estimates are based on the size and complexity of comparable Mathlib derivations (`unitaryGroup`, `GeneralLinearGroup`). Real numbers could be ±50% off.

---

# SESSION 2 UPDATE (2026-05-27)

This section records what the second working session landed and revises
the estimates. The body above is the original spec; this section is the
authoritative current status.

## What landed this session (all axiom-clean: `[propext, Classical.choice, Quot.sound]`)

**Track A (general-point Cayley Jacobian) — partial.**
- `cayleyFDerivCLM`, `cayleyFDerivCLM_apply`, `hasFDerivAt_cayley_matrix`:
  the Fréchet derivative of `cayley` at any `M` with `1+M` invertible is
  the sandwich `δ ↦ -2 (1+M)⁻¹ δ (1+M)⁻¹`. The `Ring.inverse`/`Matrix.inv`
  bridge is explicit (`Ring.inverse_unit` + `nonsing_inv_eq_ringInverse`).
- `sandwichOnSkCLM`, `_apply_val`, `_one`, `_mul` (multiplicativity, so
  `det ∘ sandwichOnSkCLM` is a monoid hom).

**Track A — BLOCKED:** `det_sandwichOnSkCLM (B) = (det B)^(n-1)`
(the `det Λ²B` second-exterior-power determinant) and the three A3
theorems that consume it remain `sorry`. Committed deferral strategy
(recorded by the reviewer): multiplicativity + density. The two
load-bearing pieces (`sandwichOnSkCLM_mul`, diagonal case) are in hand;
the remaining step is conjugation-invariance on diagonalizable matrices +
polynomial density (`MvPolynomial` over ℂ, specialize to ℝ), or the
direct Plücker-minor route (~250 lines). Scalar/diagonal sanity checks
confirmed by hand.

**Track B (typeclass instances + Haar) — COMPLETE (B1–B5).**
- `K n`: `Group`, `IsTopologicalGroup`, `T2Space`, **`CompactSpace`**
  (built from scratch: closed orthogonal set ⊆ compact box `[-1,1]^{n×n}`).
- `G n`: `Group`, `IsTopologicalGroup`, `T2Space`, `LocallyCompactSpace`
  (open in the locally compact `Matrix`).
- `A n`: `CommGroup`, `IsTopologicalGroup`, `T2Space`, `LocallyCompactSpace`
  (transported via `A.toFinNRHomeomorph`).
- `UU n`: `Group`, `IsTopologicalGroup`, `T2Space`, `LocallyCompactSpace`
  (closed subset of `Matrix`).
- `MeasurableSpace`/`BorelSpace` on `Matrix` (defeq Pi) and the four
  subtypes (`Subtype.borelSpace`, auto). `Nonempty` instances.
- `haarK`, `haarA`, `haarN`, `haarG` (`MeasureTheory.Measure.haar`) and
  their `IsHaarMeasure` instances.
- Required adding `import Mathlib.MeasureTheory.Measure.Haar.Basic`.

## Status of the 8 gaps from NextSessionIntel §7

1. `prod_isHaarMeasure` (general product-of-Haar-is-Haar) — **STILL OPEN.**
   Not needed for B5 (we used `Measure.haar` on each group individually).
   Needed for the final assembly (§7) to push `haarK ×ₘ haarA ×ₘ haarN`.
2. `CompactSpace orthogonalGroup` — **CLOSED** (`instCompactSpaceK`,
   project-local). Clean upstream-PR candidate (no Mathlib precedent).
3. `LocallyCompactSpace SL` — **N/A** (project uses `G n` not `SL`).
4. `LocallyCompactSpace GL` — **CLOSED** for `G n` (`instLocallyCompactSpaceG`).
   Upstream-PR candidate for `GeneralLinearGroup`.
5. `det (exteriorPower 2 f)` — **STILL MISSING.** This is exactly the A2
   blocker `det_sandwichOnSkCLM`.
6. `det (1 - X²)` for skew `X` — **N/A** (A1 took the `2(1+·)⁻¹-1` route,
   no `1-X²` needed).
7. Cayley transform — A1 gives the Fréchet derivative; the transform
   itself remains project-local.
8. Modular function `distribHaarChar (NN n) a = |det adNN a|` —
   **STILL OPEN, but now UNBLOCKED.** B3+B5 supply the `A n`/`NN n` group
   and Haar instances that the `distribHaarChar` routing needs. The
   composition `distribHaarChar_eq_of_measure_smul_eq_mul` +
   `addHaar_image_linearMap` (NextSessionIntel §1j, §3) is now writable
   (~50 lines), pending the conjugation `DistribMulAction (A n) (NN n)`.

## Revised line / time estimate for the remaining work

| Item | Status | Revised est. |
|---|---|---|
| §2 typeclass instances on K, A, UU, G | **DONE** | — (was ~430 lines) |
| §3 Haar measures (B5) | **DONE** | — (was ~100 lines) |
| A2 `det_sandwichOnSkCLM` (= det Λ²) | blocked | ~250 lines (Plücker) or exterior-power density |
| §4.2 general-point Jacobian (A3) | blocked on A2 | ~150 lines once A2 lands |
| §5 modular routing via `distribHaarChar` | unblocked | ~50 lines + ~20 for the `DistribMulAction` |
| §6 unimodularity of K, A, N | open | ~50 lines |
| Q9 complement `K \ K_open` measure zero | open | ~30 lines (analytic hypersurface) |
| §7 final pushforward assembly | open | ~400 lines |
| `prod_isHaarMeasure` (gap 1) | open | ~50 lines (local) |
| **Remaining total** | | **~1000 lines, ~1.5–2 person-weeks** |

(Down from the original ~1480 lines / 2–3 weeks: Track B's ~530 lines are
now done, leaving the A2 exterior-power determinant as the critical path.)

## Q9 status (complement-of-image measure zero)

Still required and now approachable. `iwasawaCharted '' univ` realizes
the `K_open` part of `K`; `K \ K_open = {Q ∈ K | det(1+Q) = 0}` is a
proper closed real-analytic subset, hence Haar-measure zero. With the
B5 Haar instances this is now a stateable ~30-line lemma (proper closed
hypersurface in a connected manifold has measure zero), but it is not
yet written.

## Phase 0 outcome (Garrett `volumes.pdf`)

Resolved (partial). Garrett, "Volume of `SL_n(Z)\SL_n(R)` and
`Sp_n(Z)\Sp_n(R)`" (April 20 2014; ed. from Feb 19 2005),
`https://www-users.cse.umn.edu/~garrett/m/v/volumes.pdf` (WebFetch can't
parse the PDF, but `pdftotext -layout` extracts it locally). For
`P⁺ = AN` the left Haar measure is a `2ρ`-type product of powers of the
diagonal entries `t_i` (exponents in arithmetic progression `-2n, -2n+2,
…`) times `dn ∏ dt_i/t_i`, consistent with `∏_{i<j} a_i/a_j` up to the
left-vs-right and GL-vs-SL convention. The exact exponent vector is
still garbled by the 2-column extraction even with `-layout`; the
structure is confirmed, the precise constant should be read off the
rendered source at the final-assembly step.

## New upstream-PR candidates (do NOT PR now)

- `CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ)` (closed-box proof).
- `LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin n) ℝ)`.
- `det (Λ² f) = (det f)^{n-1}` (general exterior-power determinant) — the
  A2 blocker; the highest-value contribution.

## Scope honesty (session 2)

Track B is genuinely complete and axiom-clean (verified by `#print
axioms` on every instance and the four Haar measures). The only `sorry`s
in `IwasawaComplete.lean` are `det_sandwichOnSkCLM` and the three A3
theorems, all consuming the missing exterior-power determinant. No
estimate here was checked against a textbook line; the modular-function
normalization caveat from §12(a) stands.
