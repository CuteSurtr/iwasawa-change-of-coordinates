# Manifold Infrastructure

## File-by-file summary

### `Mathlib/Geometry/Manifold/Algebra/Monoid.lean`
Defines `ContMDiffAdd` / `ContMDiffMul` classes for `C^n` (semi)groups on charted spaces over a model with corners, and the smooth left/right translation maps. Provides `contMDiff_mul`, pointwise smoothness lemmas, smooth left/right multiplication operators with notation `𝑳` and `𝑹`, and the product instance.

Relevant items:
- `ContMDiffMul I n G` — class: multiplication is `CMDiff n` on `G × G → G`.
- `contMDiff_mul : CMDiff n fun p : G × G ↦ p.1 * p.2` — the product is smooth.
- `contMDiff_mul_left : CMDiff n (a * ·)` and `contMDiffAt_mul_left` — **smoothness of left translation by `a`**. **DIRECT MATCH** for left-translation smoothness on any `G n` once `ContMDiffMul` is in scope.
- `contMDiff_mul_right : CMDiff n (· * a)` and `contMDiffAt_mul_right` — same for right translation.
- `mdifferentiable_mul_left`, `mdifferentiableAt_mul_left`, `mdifferentiable_mul_right`, `mdifferentiableAt_mul_right` — yielding `MDifferentiable` (so `mfderiv` exists).
- `smoothLeftMul I g : C^∞⟮I, G; I, G⟯` (notation `𝑳 I g`) and `smoothRightMul I g` (notation `𝑹 I g`) — left/right multiplication as a bundled smooth map.
- `L_apply`, `R_apply`, `L_mul`, `R_mul`, `smoothLeftMul_one`, `smoothRightMul_one` — calculation lemmas.
- `ContMDiffMul.prod` — `G × G'` is a `ContMDiffMul`.

### `Mathlib/Geometry/Manifold/Algebra/LieGroup.lean`
Defines `LieGroup I n G` (multiplication + inversion are `C^n`), proves Lie group ⇒ topological group, gives smoothness of pointwise inversion/division, the product Lie group instance, and `instNormedSpaceLieAddGroup`.

Relevant items:
- `LieGroup I n G` — class extending `ContMDiffMul` with `contMDiff_inv : CMDiff n (·⁻¹)`.
- `contMDiff_inv`, `ContMDiff.inv`, `ContMDiffAt.inv` — inversion smoothness.
- `ContMDiff.div`, `ContMDiffAt.div`, `ContMDiffOn.div`.
- `Prod.instLieGroup`.
- `instNormedSpaceLieAddGroup` — `(E, +)` over a normed space is an additive Lie group.

**No `LieGroup.Ad`, no `LieGroup.exp` declared here.**

### `Mathlib/Geometry/Manifold/Algebra/LeftInvariantDerivation.lean`
Defines `LeftInvariantDerivation I G` with `LieRing` + `LieAlgebra` structure via the commutator. Left-invariant vector fields are the favored realization elsewhere.

Relevant items:
- `LeftInvariantDerivation I G` — structure with `left_invariant''` axiom via `𝒅ₕ (smoothLeftMul_one I g)`.
- `LeftInvariantDerivation.evalAt g : LeftInvariantDerivation I G →ₗ[𝕜] PointDerivation I g`.
- `left_invariant`, `evalAt_mul`, `comp_L`.
- `LieRing`, `LieAlgebra` instances.

**No Ad and no exp here.**

### `Mathlib/Geometry/Manifold/Algebra/SmoothFunctions.lean`
Equips `C^n⟮I, N; I', G⟯` with pointwise algebraic structure: Mul, Monoid, Group, CommGroup, Semiring/Ring/CommRing, Module, Algebra. Provides `compLeftMonoidHom`, `restrictMonoidHom`, `coeFnRingHom`, `evalRingHom`.

### `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean`
Core API for `mfderiv` / `HasMFDerivAt` / `MDifferentiable`. Chain rule, `EventuallyEq` congruence, `ContMDiff → MDifferentiable`.

Relevant items:
- `MDifferentiableAt.hasMFDerivAt`, `HasMFDerivAt.mfderiv`, `mfderiv_zero_of_not_mdifferentiableAt`.
- `ContMDiffAt.mdifferentiableAt : CMDiffAt n f x → n ≠ 0 → MDiffAt f x`.
- `HasMFDerivAt.comp x`, `HasMFDerivWithinAt.comp x` — chain rule.
- `mfderiv_comp x hg hf`, `mfderiv_comp_of_eq`, `mfderiv_comp_apply`.
- `mfderiv_comp_mfderivWithin`, `mfderivWithin_comp`.
- `MDifferentiableAt.comp`, `MDifferentiable.comp`.
- `Filter.EventuallyEq.mfderiv_eq`, `mfderivWithin_congr_set`.

### `Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean`
Charts and `extChartAt` are MDifferentiable; derivatives are invertible.

Relevant items:
- `mdifferentiableAt_atlas`, `mdifferentiableOn_atlas`, `mdifferentiable_chart`.
- `OpenPartialHomeomorph.MDifferentiable.mfderiv : TangentSpace I x ≃L[𝕜] TangentSpace I' (e x)`.
- `isInvertible_mfderiv_extChartAt`, `mfderiv_extChartAt_self : mfderiv I 𝓘(𝕜, E) (extChartAt I x) x = ContinuousLinearMap.id 𝕜 _`.
- `mfderivWithin_range_extChartAt_symm`, `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`.

### `Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean`
Derivative formulas: identity, constants, products, projections, arithmetic.

Relevant items:
- `ContinuousLinearMap.hasMFDerivAt`, `mfderiv_eq`.
- `ContinuousLinearEquiv.hasMFDerivAt`, `mfderiv_eq`.
- `hasMFDerivAt_id`, `mfderiv_id`, `hasMFDerivAt_const`, `mfderiv_const`.
- `HasMFDerivAt.prodMk`, `MDifferentiableAt.prodMk`, `mfderiv_prodMk` — **product manifold differential, DIRECT MATCH**.
- `HasMFDerivAt.prodMap`, `mfderiv_prodMap`.
- `hasMFDerivAt_fst`, `hasMFDerivAt_snd`, `mfderiv_fst`, `mfderiv_snd`.
- `mfderiv_prod_left`, `mfderiv_prod_right`, `mfderiv_prod_eq_add_comp`, `mfderiv_prod_eq_add_apply`.
- `HasMFDerivAt.add`, `HasMFDerivAt.sub`, `HasMFDerivAt.neg`, `HasMFDerivAt.const_smul`, `mfderiv_add`, `mfderiv_sub`, `mfderiv_neg`, `const_smul_mfderiv`.
- `HasMFDerivAt.mul'`/`HasMFDerivAt.mul` for `NormedRing`/`NormedCommRing` codomain: `mfderiv(p*q) = p z • q' + p' <• q z`. **DIRECT MATCH for conjugation derivative.**

### `Mathlib/Geometry/Manifold/Diffeomorph.lean`
Defines `Diffeomorph I I' M M' n` with refl/symm/trans/prodCongr/prodComm/prodAssoc/sumCongr/sumComm/sumAssoc/sumEmpty, `ContinuousLinearEquiv.toDiffeomorph`, `ModelWithCorners.transContinuousLinearEquiv`.

Relevant items:
- `Diffeomorph.toContMDiffMap`, `Diffeomorph.contMDiff`, `Diffeomorph.mdifferentiable`.
- `ContinuousLinearEquiv.toDiffeomorph`.

### `Mathlib/Geometry/Manifold/Instances/UnitsOfNormedAlgebra.lean`
**Crucial for `GL_n(ℝ)`.** Exposes the open submanifold structure on `Rˣ` for `R` a complete normed ring.

Relevant items:
- `Units.instance : ChartedSpace R Rˣ` via `Units.isOpenEmbedding_val.singletonChartedSpace`.
- `Units.instance : IsManifold 𝓘(𝕜, R) n Rˣ` via `isOpenEmbedding_val.isManifold_singleton`.
- `Units.contMDiff_val : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ → R)`.
- `Units.instance : LieGroup 𝓘(𝕜, R) n Rˣ` — **full Lie group structure**. **DIRECT MATCH for our `G n` once we identify it with `Units` (or use the same pattern with `Subtype` for the det ≠ 0 set).**
- Pattern: `ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val` lifts smoothness from `Matrix n n ℝ → Matrix n n ℝ` to `(Matrix n n ℝ)ˣ → (Matrix n n ℝ)ˣ`. **DIRECT for Gram-Schmidt smoothness lift.**

### `Mathlib/Geometry/Manifold/Instances/Sphere.lean`
Stereographic projection on the unit sphere, `Circle as LieGroup (𝓡 1) ω`. Includes `range_mfderiv_coe_sphere`. Template for open submanifold mfderiv.

## Coverage of the seven categories

1. **Left/right translation derivative.** Smoothness: `contMDiff_mul_left` / `_right`. Differentiability: `mdifferentiableAt_mul_left`. **No direct mfderiv formula** — descend via `extChartAt` + chain rule. For `Units`/`G n`, the chart is identity (`chartAt_apply`), so descent simplifies to `fderiv` of `Matrix → Matrix` multiplication.

2. **Conjugation derivative.** No direct. Build from `HasMFDerivAt.mul'` + `ContMDiff.inv` + `mfderiv_const`.

3. **Adjoint Ad.** *Absent in Mathlib.* Must define ad hoc.

4. **Exponential map.** *Absent in Mathlib.* PR #37932 is open (idontgetoutmuch, 2026-04-11). Define ad hoc via `NormedSpace.exp`.

5. **Open submanifold pattern.** `UnitsOfNormedAlgebra.lean` is the template. **DIRECT MATCH** for `G n`.

6. **Product manifold differential.** `HasMFDerivAt.prodMk`, `mfderiv_prodMk`, family. **DIRECT MATCH**.

## Direct-match flags for the three Phase 2 targets

- **`mfderiv_leftMul_at` (T1-4 Lemma 1)** — **PARTIAL DIRECT**: `contMDiff_mul_left` + `mdifferentiableAt_mul_left` give smoothness and MDifferentiableAt for free. Computing the explicit mfderiv requires descending through `Units.val` chart (which is identity), giving `mfderiv (g₀ * ·) g = (matrix-level fderiv of g₀ * ·) = (CLM left-multiply by g₀.val)`.

- **`conjugation_NN_by_diagonal` (T1-4 Lemma 2)** — **NO direct match.** Combine `HasMFDerivAt.mul'` (twice) + `ContMDiff.inv` + `mfderiv_const`. The eigenvalue structure `(Ad(diag(a)) X)_{ij} = (a_i/a_j) X_{ij}` follows from matrix computation.

- **Gram-Schmidt smoothness on invertibles (T1-2)** — **NO direct match in Mathlib's Gram-Schmidt.** But: prove `ContDiffOn ℝ ⊤ Iwasawa.gramSchmidt {M | M.det ≠ 0}` via the standard inductive route (inner products are bilinear and smooth, normalization via `Real.contDiffAt_sqrt` on the open set), then transfer to manifold via `ContMDiff.of_comp_isOpenEmbedding` if `G n` is set up as `Units` or via direct singletonChartedSpace lift if it's a subtype.

## Notable absences

No `LieGroup.Ad`, no `LieGroup.exp`, no closed-form `mfderiv` of `fun g ↦ g₀ * g`. Path: `Units.isOpenEmbedding_val` → identify `G n` with open subset of `Matrix n n ℝ` → compute fderivs there → transfer via `mfderiv_extChartAt_self` and `chartAt` being identity.
