# Mathlib API Inventory for the Iwasawa Jacobian and Haar Stage

This file inventories the most relevant mathlib declarations for moving
from the explicit derivative determinant
(`detInIwasawaBases_one_a_one_eq`, see `02_lean_theorem_targets.md`) to
chart-level change of variables and Haar measure. Read in conjunction
with the existing `MathlibInfrastructureMap.md` (project root), which
covers the Lie group / manifold side already.

Local mathlib path: `.lake/packages/mathlib/Mathlib/`.

Verdict legend:
- **direct** — usable as-is.
- **wrap** — needs a thin wrapper or specialization to fit the project's
  subtype/CLM-based API.
- **adj** — adjacent/tangential, mention only.

---

## A. Determinants and bases

### A.1 `LinearMap.det` (Mathlib/LinearAlgebra/Determinant.lean)

```lean
protected irreducible_def LinearMap.det : (M →ₗ[A] M) →* A
```

Monoid hom (so `det (f.comp g) = det f * det g`). Defaults to `1` if no
finite basis. Already used by `adNN_det_eq_pair_product`.

Key lemmas:
- `LinearMap.det_toMatrix (b : Basis ι A M) (f : M →ₗ[A] M) :
    Matrix.det (LinearMap.toMatrix b b f) = LinearMap.det f`
- `LinearMap.det_comp`, `LinearMap.det_one`, `LinearMap.det_zero`.
- `LinearMap.det_eq_zero_iff_ker_ne_bot` (used in
  `detInIwasawaBases_one_a_one_ne_zero`).

Verdict: **direct**. The proposed `detInIwasawaBases_one_a_one_eq`
will compute via `LinearMap.toMatrix` already.

### A.2 `LinearMap.toMatrix` (LinearAlgebra/Matrix/ToLin.lean)

```lean
noncomputable def LinearMap.toMatrix
    (v₁ : Basis ι R M₁) (v₂ : Basis κ R M₂) :
    (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix κ ι R
```

```lean
@[simp] lemma LinearMap.toMatrix_apply
    (v₁ : Basis ι R M₁) (v₂ : Basis κ R M₂) (f : M₁ →ₗ[R] M₂) (i j) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
```

Verdict: **direct**. Already used heavily in the project (e.g.,
`adNN_toMatrix_diagonal`).

### A.3 `Matrix.stdBasis` (LinearAlgebra/Matrix/StdBasis.lean)

```lean
noncomputable def Matrix.stdBasis (R : Type*) (m n : Type*)
    [Semiring R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n] :
    Basis (m × n) R (Matrix m n R)

@[simp] lemma Matrix.stdBasis_eq_single ... :
    Matrix.stdBasis R m n (i, j) = Matrix.single i j 1
```

Verdict: **direct**. Already used as the target basis in
`detInIwasawaBases`.

### A.4 `Module.Basis.prod`, `Basis.reindex`, `Basis.map`
(LinearAlgebra/Basis/Defs.lean, Basis/Prod.lean)

```lean
protected def Basis.prod (b : Basis ι R M) (b' : Basis ι' R M') :
    Basis (ι ⊕ ι') R (M × M')

@[simp] lemma Basis.prod_apply_inl ... (i : ι) :
    (b.prod b') (Sum.inl i) = (b i, 0)
@[simp] lemma Basis.prod_apply_inr ... (i' : ι') :
    (b.prod b') (Sum.inr i') = (0, b' i')

def Basis.reindex (b : Basis ι R M) (e : ι ≃ ι') : Basis ι' R M

@[simp] lemma Basis.reindex_apply (i' : ι') :
    b.reindex e i' = b (e.symm i')

protected def Basis.map (b : Basis ι R M) (f : M ≃ₗ[R] M') : Basis ι R M'
```

Verdict: **direct**. Already used to build `iwasawaSourceBasis`
(prod + reindex) and `skBasis` (map via `skCoordLinearEquiv`).

### A.5 `Pi.basisFun` (LinearAlgebra/StdBasis.lean)

```lean
noncomputable def Pi.basisFun (R : Type*) (ι : Type*)
    [Semiring R] [Fintype ι] [DecidableEq ι] :
    Basis ι R (ι → R)

@[simp] lemma Pi.basisFun_apply (i : ι) :
    Pi.basisFun R ι i = Pi.single i (1 : R)
```

Verdict: **direct**. Already used as the diagonal A-coordinate basis.

### A.6 Block-triangular and block-diagonal determinants
(LinearAlgebra/Matrix/Block.lean)

```lean
theorem Matrix.det_of_upperTriangular [LinearOrder m]
    {M : Matrix m m R} (h : M.BlockTriangular id) :
    M.det = ∏ i : m, M i i
```

`Matrix.BlockTriangular M b` means upper triangular w.r.t. the block
partition induced by `b : m → α`. With `b = id`, this is genuine upper
triangularity.

Related:
- `Matrix.det_fromBlocks_zero₂₁` and `_zero₁₂` for 2x2 block matrices
  with a zero off-block.
- `Matrix.det_blockDiagonal` for sums.
- `Matrix.det_diagonal` (used in `adNN_det_eq_pair_product`).

Verdict: **direct** for a "build a block-ordered basis" approach to the
proof of `detInIwasawaBases_one_a_one_eq`. If we permute the source and
target basis so that each {p, q}-block is contiguous, the matrix
becomes block-diagonal with 2x2 blocks plus 1x1 diagonal blocks; then
`det = ∏ block_dets`.

Caveat: `Matrix.BlockTriangular` requires a linear order on the index;
`Fin n × Fin n` has its lex order. Reading the off-diagonal structure
of the lex-ordered matrix may be more painful than working in the
"block-ordered" basis (see Implementation Plan).

---

## B. Additive Haar / finite-dimensional Lebesgue

### B.1 `Basis.addHaar` (MeasureTheory/Measure/Haar/OfBasis.lean)

```lean
irreducible_def Basis.addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped

instance isAddHaarMeasure_basis_addHaar (b : Basis ι ℝ E) :
    IsAddHaarMeasure b.addHaar
```

Normalized so the parallelepiped of basis vectors has measure 1.

Key lemmas:
- `Basis.addHaar_self : b.addHaar (parallelepiped b) = 1`
- `Basis.addHaar_reindex (e : ι ≃ ι') : (b.reindex e).addHaar = b.addHaar`
  (reindexing does not change the measure).
- `Basis.addHaar_eq_iff : b.addHaar = μ ↔ μ (parallelepiped b) = 1`.

Verdict: **direct**. Use `iwasawaSourceBasis.addHaar` as the canonical
Lebesgue on `(Sk n) × ((Fin n → ℝ) × (NN n))`, and
`(Matrix.stdBasis ℝ (Fin n) (Fin n)).addHaar` on `M_n(R)`.

### B.2 `Basis.prod_addHaar`

```lean
theorem Basis.prod_addHaar (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
    (v.prod w).addHaar = v.addHaar.prod w.addHaar
```

Verdict: **direct**. Lets us factor
`iwasawaSourceBasisProd.addHaar = skBasis.addHaar.prod (...)`.

### B.3 `ContinuousLinearEquiv.isAddHaarMeasure_map`
(MeasureTheory/Group/Measure.lean)

```lean
instance ContinuousLinearEquiv.isAddHaarMeasure_map
    (L : E ≃SL[σ] F) (μ : Measure E) [IsAddHaarMeasure μ] :
    IsAddHaarMeasure (μ.map L)
```

Verdict: **direct**. Pushforward of additive Haar under a continuous
linear equiv is still additive Haar.

### B.4 `map_addHaar_smul`, `addHaar_smul`
(MeasureTheory/Measure/Lebesgue/EqHaar.lean)

```lean
theorem MeasureTheory.Measure.map_addHaar_smul
    (μ : Measure E) [IsAddHaarMeasure μ] {r : ℝ} (hr : r ≠ 0) :
    μ.map (r • ·) = ENNReal.ofReal |r ^ finrank ℝ E|⁻¹ • μ

@[simp] theorem MeasureTheory.Measure.addHaar_smul
    (μ : Measure E) [IsAddHaarMeasure μ] (r : ℝ) (s : Set E) :
    μ (r • s) = ENNReal.ofReal |r ^ finrank ℝ E| * μ s
```

Verdict: **direct**. Useful if we need to track scaling of A by a
multiplicative shift.

### B.5 `MeasureTheory.Measure.haarScalarFactor` etc.
(MeasureTheory/Measure/Haar/Unique.lean)

```lean
noncomputable def MeasureTheory.Measure.haarScalarFactor
    (μ ν : Measure G) [IsHaarMeasure ν] : ℝ≥0
```

Verdict: **adj**. Useful if we eventually want to identify the
constructed measure with mathlib's abstract `haar` measure.

---

## C. Jacobian / change of variables

### C.1 The main change-of-variables lemmas
(MeasureTheory/Function/Jacobian.lean)

```lean
theorem lintegral_abs_det_fderiv_eq_addHaar_image
    (μ : Measure E) [IsAddHaarMeasure μ]
    {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ = μ (f '' s)

theorem map_withDensity_abs_det_fderiv_eq_addHaar
    (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}
    (hs : NullMeasurableSet s μ)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map f ((μ.restrict s).withDensity
        fun x => ENNReal.ofReal |(f' x).det|) =
      μ.restrict (f '' s)

theorem integral_image_eq_integral_abs_det_fderiv_smul
    [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [IsAddHaarMeasure μ]
    {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ
```

Hypotheses to supply for the Iwasawa project:
- `μ = iwasawaSourceBasis.addHaar` or `Matrix.stdBasis.addHaar`.
- `s = univ` or some open subset.
- `f = Subtype.val ∘ iwasawaMap ∘ (chart unfolders for K, A, N)`.
- `f' x = iwasawaMatrixLeibnizCLM ...` (after bridging through
  chart differentials).
- Injectivity: from the existing `iwasawaMatrixLeibnizCLM_one_a_one_injective`
  for the linearization, plus a global argument from
  `iwasawaEquiv.symm` already being a bijection on the group level.

Verdict: **direct (with substantial wiring)**. These are the
target consumers of the determinant formula.

### C.2 Measurability scaffolding

```lean
theorem aemeasurable_ofReal_abs_det_fderivWithin
    (μ : Measure E) [IsAddHaarMeasure μ] (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x => ENNReal.ofReal |(f' x).det|) (μ.restrict s)
```

Verdict: **wrap**. Needed to feed Jacobian lemmas.

### C.3 Sard / measurability of image

```lean
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ : Measure E) [IsAddHaarMeasure μ] (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h : ∀ x ∈ s, (f' x).det = 0) : μ (f '' s) = 0
```

Verdict: **adj**. Likely unused for the Iwasawa diffeomorphism (the
Jacobian is nonzero everywhere by `detInIwasawaBases_one_a_one_ne_zero`).

---

## D. Group Haar (abstract)

### D.1 `haarMeasure` and `haar` (MeasureTheory/Measure/Haar/Basic.lean)

```lean
noncomputable def MeasureTheory.Measure.haarMeasure
    (K₀ : TopologicalSpace.PositiveCompacts G) : Measure G

instance isHaarMeasure_haarMeasure ...
instance isMulLeftInvariant_haarMeasure ...

noncomputable abbrev MeasureTheory.Measure.haar
    [LocallyCompactSpace G] : Measure G :=
  haarMeasure <| Classical.arbitrary _
```

Verdict: **adj**. The "intrinsic" Haar on `G n = GL_n(R)_+`, but
constructing it via `haarMeasure K₀` requires choosing a
`PositiveCompacts`. Usually we go the opposite direction: build the
measure explicitly via `Basis.addHaar` and chart push, then prove
equality with `haar` via `haarMeasure_unique` (next section).

### D.2 `haarMeasure_unique` (MeasureTheory/Measure/Haar/Unique.lean)

```lean
theorem haarMeasure_unique
    (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
    (K₀ : PositiveCompacts G) :
    μ = μ K₀ • haarMeasure K₀

theorem haarMeasure_eq_iff (K₀ : PositiveCompacts G) (μ : Measure G)
    [SigmaFinite μ] [IsMulLeftInvariant μ] :
    haarMeasure K₀ = μ ↔ μ K₀ = 1
```

Verdict: **direct**. Once we have an explicit candidate Haar on G n,
this identifies it with mathlib's `haar` up to scalar.

---

## E. Modular character

### E.1 `Measure.modularCharacterFun`, `Measure.modularCharacter`
(MeasureTheory/Group/ModularCharacter.lean)

```lean
noncomputable def MeasureTheory.Measure.modularCharacterFun (g : G) : ℝ≥0

noncomputable def MeasureTheory.Measure.modularCharacter : G →* ℝ≥0

lemma map_right_mul_eq_modularCharacterFun_smul
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ] (g : G) :
    Measure.map (· * g) μ = modularCharacterFun g • μ

lemma modularCharacterFun_pos (g : G) : 0 < modularCharacterFun g
```

For `G = GL_n(R)`, `modularCharacterFun ≡ 1` (unimodular). So this API
is **adj** for our main story.

For the Borel subgroup `P = AN`, the modular character is nontrivial:
`Δ_P(an) = a^{-2ρ} = ∏_{i<j} a_j/a_i`. The pair-product version (with
sign flipped) appears in this character. Mathlib's
`Measure.modularCharacter` would express this if we instantiated it on
`P`, but we likely don't need to. **adj.**

---

## F. Product measures, pushforward, measurability

Standard mathlib API at `MeasureTheory/Measure/MeasureSpace.lean`,
`MeasureTheory/Constructions/Prod/Basic.lean`:

- `Measure.map (f : α → β) (μ : Measure α) : Measure β`
- `Measure.withDensity (μ : Measure α) (f : α → ℝ≥0∞) : Measure α`
- `Measure.restrict (μ : Measure α) (s : Set α) : Measure α`
- `Measure.prod (μ : Measure α) (ν : Measure β) : Measure (α × β)`
- `MeasurePreserving`, `Measure.QuasiMeasurePreserving`
- `AEMeasurable`, `MeasurableEmbedding`

All **direct** in their general form; used as glue for the Jacobian
machinery.

---

## Verdict summary

The Jacobian story is **fully available** in mathlib:

| Step | Mathlib API | Status |
|------|------------|--------|
| Compute `LinearMap.det` of a derivative | `LinearMap.det_toMatrix`, `Matrix.det_diagonal`, `Matrix.det_fromBlocks_zero_*` | direct |
| Construct reference Lebesgue on source | `Basis.addHaar`, `Basis.prod_addHaar` | direct |
| Pushforward via change of variables | `integral_image_eq_integral_abs_det_fderiv_smul`, `lintegral_abs_det_fderiv_eq_addHaar_image`, `map_withDensity_abs_det_fderiv_eq_addHaar` | direct |
| Identify result with group Haar | `haarMeasure_unique`, `IsHaarMeasure`, `haarScalarFactor` | direct (post-pushforward) |
| Modular character (NOT needed for unimodular G) | `Measure.modularCharacter` | adj |

## Which API to reach for FIRST after `detInIwasawaBases_one_a_one_eq`?

**Recommendation: `MeasureTheory.Function.Jacobian` (i).**

Reasoning:
1. The project's explicit derivative `iwasawaMatrixLeibnizCLM` is a
   chart-coordinate object. `Function.Jacobian` is built for exactly
   this scenario: explicit Fréchet derivative + invertibility + injectivity
   on a measurable set.
2. The group-Haar API (`haarMeasure_unique`) is needed only LATER, to
   identify the chart-pushforward with mathlib's abstract `haar`.
3. The modular character API (`Measure.modularCharacterFun`) is
   irrelevant for `GL_n(R)` (unimodular).

The workflow is:

```
detInIwasawaBases_one_a_one_eq             [Stage 4B2]
        ↓
absDetInIwasawaBases_general_eq            [Stage 4B3]
        ↓
chart-level bridge to mfderiv              [Stage 4C — bridge to iwasawaDiffeomorph]
        ↓
integral_image_eq_integral_abs_det_fderiv_smul  [Stage 5 — change of variables]
        ↓
Identify pushforward = Haar via haarMeasure_unique  [Stage 6 — Haar]
```

Step 5 is where `Function.Jacobian` enters. Step 6 is where group Haar
enters. Steps 1-3 do not need any measure-theory API at all, only
linear algebra and manifold differentials.
