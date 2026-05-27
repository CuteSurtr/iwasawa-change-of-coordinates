# NextSessionIntel.md

Pre-session intel pass. Mathlib API surface, exterior power and Cayley risk, modular function routing, web references, coordination check, and open questions for the human reader. Mathlib pin: `leanprover-community/mathlib4` v4.30.0-rc1. Date: 2026-05-27.

This document is informational only. No Lean code was added or changed.

---

## Section 1. Mathlib API surface, exact signatures

### 1a. `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`

Variable bindings at the file scope (line 80, 100, 139, 511, 650):

```lean
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable [SecondCountableTopology G]
```

The `Measure.haarMeasure` definition (line 513-518):

```lean
/-- The Haar measure on the locally compact group `G`, scaled so that `haarMeasure K₀ K₀ = 1`. -/
@[to_additive
/-- The Haar measure on the locally compact additive group `G`, scaled so that
`addHaarMeasure K₀ K₀ = 1`. -/]
noncomputable def haarMeasure (K₀ : PositiveCompacts G) : Measure G :=
  ((haarContent K₀).measure K₀)⁻¹ • (haarContent K₀).measure
```

Note: `haarMeasure` does NOT require `LocallyCompactSpace G` in its signature, but the existence of a `PositiveCompacts G` term effectively requires it (a compact set with nonempty interior). The lemmas that use `haarMeasure` (e.g. `haarMeasure_self`) recover `LocallyCompactSpace` from `K₀.locallyCompactSpace_of_group`.

Self-normalization (line 537-544):

```lean
@[to_additive]
theorem haarMeasure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ K₀ = 1 := by
  haveI : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  simp only [haarMeasure, coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← K₀.isCompact.measure_closure,
    Content.measure_apply _ isClosed_closure.measurableSet, ENNReal.inv_mul_cancel]
  · exact (haarContent_outerMeasure_closure_pos K₀).ne'
  · exact (Content.outerMeasure_lt_top_of_isCompact _ K₀.isCompact.closure).ne
```

`IsHaarMeasure` instance (line 570-575):

```lean
instance isHaarMeasure_haarMeasure (K₀ : PositiveCompacts G) : IsHaarMeasure (haarMeasure K₀) := by
  apply
    isHaarMeasure_of_isCompact_nonempty_interior (haarMeasure K₀) K₀ K₀.isCompact
      K₀.interior_nonempty
  · simp only [haarMeasure_self]; exact one_ne_zero
  · simp only [haarMeasure_self, ne_eq, ENNReal.one_ne_top, not_false_eq_true]
```

`IsHaarMeasure` class definition is in `Mathlib/MeasureTheory/Group/Measure.lean:770-772`:

```lean
class IsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) : Prop
    extends IsFiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, IsOpenPosMeasure μ
```

Uniqueness (line 665-671):

```lean
theorem haarMeasure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
    (K₀ : PositiveCompacts G) : μ = μ K₀ • haarMeasure K₀ := by
  have A : Set.Nonempty (interior (closure (K₀ : Set G))) :=
    K₀.interior_nonempty.mono (interior_mono subset_closure)
  have := measure_eq_div_smul μ (haarMeasure K₀)
    (measure_pos_of_nonempty_interior _ A).ne' K₀.isCompact.closure.measure_ne_top
  rwa [haarMeasure_closure_self, div_one, K₀.isCompact.measure_closure] at this
```

`haarMeasure_eq_iff` (line 676-679):

```lean
theorem haarMeasure_eq_iff (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite μ]
    [IsMulLeftInvariant μ] :
    haarMeasure K₀ = μ ↔ μ K₀ = 1 :=
  ⟨fun h => h.symm ▸ haarMeasure_self, fun h => by rw [haarMeasure_unique μ K₀, h, one_smul]⟩
```

**Full required typeclass list for `haarMeasure K₀`:** `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]`. Plus `PositiveCompacts G` argument needs a compact set with nonempty interior to exist, i.e. `LocallyCompactSpace G` morally. `IsMulLeftInvariant`, `Regular`, `SigmaFinite`, `IsFiniteMeasureOnCompacts`, `IsOpenPosMeasure` are all auto-derived from `IsHaarMeasure`.

### 1b. `Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean` (full content extracted, 97 lines)

Variable bindings (line 35-36):

```lean
variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A] {g : G}
```

Main definition (line 43-55):

```lean
/-- The distributive Haar character of a group `G` acting distributively on a group `A` is the
unique positive real number `Δ(g)` such that `μ (g • s) = Δ(g) * μ s` for all Haar
measures `μ : Measure A`, set `s : Set A` and `g : G`. -/
@[simps -isSimp]
noncomputable def distribHaarChar : G →* ℝ≥0 :=
  letI := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  {
    toFun g := addHaarScalarFactor (DomMulAct.mk g • addHaar) (addHaar (G := A))
    map_one' := by simp
    map_mul' g g' := by
      simp_rw [DomMulAct.mk_mul]
      rw [addHaarScalarFactor_eq_mul _ (DomMulAct.mk g' • addHaar (G := A))]
      congr 1
      simp_rw [mul_smul]
      rw [addHaarScalarFactor_domSMul]
  }
```

Identification with `addHaarScalarFactor` (line 63-66):

```lean
variable (μ) in
lemma addHaarScalarFactor_smul_eq_distribHaarChar (g : G) :
    addHaarScalarFactor (DomMulAct.mk g • μ) μ = distribHaarChar A g := by
  borelize A
  exact addHaarScalarFactor_smul_congr' ..
```

The set-level identification (line 83-86):

```lean
variable (μ) in
lemma distribHaarChar_mul (g : G) (s : Set A) : distribHaarChar A g * μ s = μ (g • s) := by
  have : (DomMulAct.mk g • μ) s = μ (g • s) := by simp [domSMul_apply]
  rw [eq_comm, ← nnreal_smul_coe_apply, ← addHaarScalarFactor_smul_eq_distribHaarChar μ,
    ← this, ← smul_apply, ← isAddLeftInvariant_eq_smul_of_regular]
```

Identification by ratio (line 88-90):

```lean
lemma distribHaarChar_eq_div (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (g : G) :
    distribHaarChar A g = μ (g • s) / μ s := by
  rw [← distribHaarChar_mul, ENNReal.mul_div_cancel_right] <;> simp [*]
```

The single most useful identification for us (line 92-95):

```lean
lemma distribHaarChar_eq_of_measure_smul_eq_mul (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) {r : ℝ≥0}
    (hμgs : μ (g • s) = r * μ s) : distribHaarChar A g = r := by
  refine ENNReal.coe_injective ?_
  rw [distribHaarChar_eq_div hs₀ hs, hμgs, ENNReal.mul_div_cancel_right] <;> simp [*]
```

There is also a related `MulEquivHaarChar` in `Mathlib/MeasureTheory/Measure/Haar/MulEquivHaarChar.lean:40`:

```lean
noncomputable def mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0 :=
  haarScalarFactor haar (haar.map φ)
```

with typeclass requirements `[Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]`.

### 1c. `Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean`

The key fact is that a basis on a finite-dimensional real vector space gives a canonical Haar measure (the "Lebesgue from basis").

Definition (line 254-255):

```lean
/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
irreducible_def addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped
```

Instance (line 257-258):

```lean
instance _root_.isAddHaarMeasure_basis_addHaar (b : Basis ι ℝ E) : IsAddHaarMeasure b.addHaar := by
  rw [Basis.addHaar]; exact Measure.isAddHaarMeasure_addHaarMeasure _
```

Variable bindings in this file (line 181, 250):

```lean
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
variable [MeasurableSpace E] [BorelSpace E]
```

`addHaar_eq_iff` (line 266ff):

```lean
theorem addHaar_eq_iff [SecondCountableTopology E] (b : Basis ι ℝ E) (μ : Measure E)
```

Product (line 282):

```lean
theorem prod_addHaar (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
```

This is the closest Mathlib has to "Haar of a product is the product of Haars" in the additive setting. There is NO `IsHaarMeasure` (multiplicative) version of `prod_addHaar` in Mathlib that we found.

### 1d. `Mathlib/MeasureTheory/Function/Jacobian.lean`

Variable bindings at the top (line 104-105):

```lean
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
```

**Confirmed: `f : E → E` and `f' : E → E →L[ℝ] E`. Source and target are the same `E`.** No variant with different spaces exists in this file. The change-of-variables relies on `addHaar` being canonical on `E` with `μ (f '' s) = ∫ |det f'|`. A non-square source-to-target map would not have a finite-dimensional `det`.

Main theorem (line 1218-1228):

```lean
/-- Change of variable formula for differentiable functions: if a function `f` is
injective and differentiable on a measurable set `s`, then the Bochner integral of a function
`g : E → F` on `f '' s` coincides with the integral of `|(f' x).det| • g ∘ f` on `s`. -/
theorem integral_image_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ := by
  rw [← restrict_map_withDensity_abs_det_fderiv_eq_addHaar μ hs hf' hf,
    (measurableEmbedding_of_fderivWithin hs hf' hf).integral_map]
  simp only [Set.restrict_apply, ← Function.comp_apply (f := g), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map, map_comap_subtype_coe hs,
    setIntegral_withDensity_eq_setIntegral_smul₀
      (aemeasurable_toNNReal_abs_det_fderivWithin μ hs hf') _ hs]
  congr with x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (abs_nonneg (f' x).det)]
```

The `μ` here is implicit `[IsAddHaarMeasure μ]` from the section.

Lebesgue version (line 1100-1104):

```lean
theorem lintegral_abs_det_fderiv_eq_addHaar_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ) = μ (f '' s) :=
  le_antisymm (lintegral_abs_det_fderiv_le_addHaar_image μ hs hf' hf)
    (addHaar_image_le_lintegral_abs_det_fderiv μ hs hf')
```

Set-version (line 764-767):

```lean
theorem measurable_image_of_fderivWithin (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) : MeasurableSet (f '' s) :=
  haveI : DifferentiableOn ℝ f s := fun x hx => (hf' x hx).differentiableWithinAt
  hs.image_of_continuousOn_injOn (DifferentiableOn.continuousOn this) hf
```

And the convenient `OpenPartialHomeomorph` version (line 1230-1237):

```lean
theorem integral_target_eq_integral_abs_det_fderiv_smul {f : OpenPartialHomeomorph E E}
    (hf' : ∀ x ∈ f.source, HasFDerivAt f (f' x) x) (g : E → F) :
    ∫ x in f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ := by
  have : f '' f.source = f.target := PartialEquiv.image_source_eq_target f.toPartialEquiv
  rw [← this]
  apply integral_image_eq_integral_abs_det_fderiv_smul μ f.open_source.measurableSet _ f.injOn
  intro x hx
  exact (hf' x hx).hasFDerivWithinAt
```

### 1e. `Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean` (527 lines, table of contents)

Variable bindings (line 65, 79):

```lean
variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]
variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
```

Definition (line 67-70):

```lean
/-- `SpecialLinearGroup n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }
```

Notation (line 75):

```lean
scoped[MatrixGroups] notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R
```

Key instances (line 84-200):

```lean
instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R)
instance instCoeFun : CoeFun (SpecialLinearGroup n R) fun _ => n → n → R
instance hasInv : Inv (SpecialLinearGroup n R)
instance hasMul : Mul (SpecialLinearGroup n R)
instance hasOne : One (SpecialLinearGroup n R)
instance : Pow (SpecialLinearGroup n R) ℕ
instance monoid : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid _ Subtype.coe_injective coe_one coe_mul coe_pow
instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    inv_mul_cancel := fun A => by
      ext1
      simp [adjugate_mul] }
```

Topological instances (in `Mathlib/Topology/Algebra/Group/Matrix.lean:83-128`):

```lean
instance : TopologicalSpace (SL n R) :=
  inferInstanceAs <| TopologicalSpace (Subtype _)

-- under [IsTopologicalRing R]:
instance topologicalGroup : IsTopologicalGroup (SL n R) where
  continuous_inv := continuous_induced_rng.mpr continuous_induced_dom.matrix_adjugate
  continuous_mul := continuous_induced_rng.mpr <|
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

instance instT1Space [T1Space R] : T1Space (SL n R) := isClosedEmbedding_val.isEmbedding.t1Space
```

**There is NO `LocallyCompactSpace (SL n R)` or `CompactSpace (SL n R)` instance in Mathlib** as of v4.30.0-rc1. (`SL(n, ℝ)` for `n ≥ 2` is not compact; it is locally compact, but the instance is not declared.)

### 1f. `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` (396 lines)

Definition (line 41-45):

```lean
/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices -/
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [Semiring R] :
    Type _ :=
  (Matrix n n R)ˣ
```

Notation (line 47):

```lean
@[inherit_doc] notation "GL" => GeneralLinearGroup
```

Since `GL n R = (Matrix n n R)ˣ`, it gets `Group` automatically as the unit group of a ring. The other instances:

```lean
instance instCoeFun [Semiring R] : CoeFun (GL n R) fun _ => n → n → R where
def det : GL n R →* Rˣ
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R)
```

Topology (`Mathlib/Topology/Algebra/Group/Matrix.lean:32-72`):

```lean
namespace Matrix.GeneralLinearGroup

theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α → GL n R) (hf : Continuous f) (i : n) :
    Continuous (fun x ↦ f x i) := ...

-- under [IsTopologicalRing R]:
@[continuity, fun_prop] protected lemma continuous_det :
    Continuous (det : GL n R → Rˣ) := ...
```

GL takes its topology from the units of `Matrix n n R` (since `(R)ˣ` inherits topology from `R` via the embedding `Units.embedProduct`). Detailed in the same file. No `LocallyCompactSpace` instance is declared.

### 1g. `Mathlib/LinearAlgebra/UnitaryGroup.lean` (345 lines)

Variable bindings (line 54-55, 69-70):

```lean
variable (n : Type u) [DecidableEq n] [Fintype n]
variable (α : Type v) [CommRing α] [StarRing α]
variable {n : Type u} [DecidableEq n] [Fintype n]
variable {α : Type v} [CommRing α] [StarRing α] {A : Matrix n n α}
```

Definition (line 57-61):

```lean
/-- `Matrix.unitaryGroup n` is the group of `n` by `n` matrices where the star-transpose is the
inverse.
-/
abbrev unitaryGroup : Submonoid (Matrix n n α) :=
  unitary (Matrix n n α)
```

Group instance: free from `unitary` (line 64):

```lean
-- the group and star structure is already defined in another file
example : Group (unitaryGroup n α) := inferInstance
example : StarMul (unitaryGroup n α) := inferInstance
```

The `OrthogonalGroup` portion (line 284-305):

```lean
section OrthogonalGroup

variable (n) (R : Type v) [CommRing R]

-- TODO: will lemmas about `Matrix.orthogonalGroup` work without making
-- `starRingOfComm` a local instance? E.g., can we talk about unitary group and orthogonal group
-- at the same time?
attribute [local instance] starRingOfComm

/-- `Matrix.orthogonalGroup n` is the group of `n` by `n` matrices where the transpose is the
inverse. -/
abbrev orthogonalGroup := unitaryGroup n R

theorem mem_orthogonalGroup_iff {A : Matrix n n R} :
    A ∈ Matrix.orthogonalGroup n R ↔ A * Aᵀ = 1 :=
  mem_unitaryGroup_iff

theorem mem_orthogonalGroup_iff' {A : Matrix n n R} :
    A ∈ Matrix.orthogonalGroup n R ↔ Aᵀ * A = 1 :=
  mem_unitaryGroup_iff'

end OrthogonalGroup
```

Determinant in unitary group (line 152-153):

```lean
@[simp]
theorem det_isUnit (A : unitaryGroup n α) : IsUnit (A : Matrix n n α).det :=
  isUnit_iff_isUnit_det _ |>.mp <| (Unitary.toUnits A).isUnit
```

There's no `det A = ±1` or `‖A‖ ≤ √n` packaged form for `unitaryGroup`. **There is no `CompactSpace (Matrix.unitaryGroup (Fin n) ℝ)` or `CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ)` instance in Mathlib.** This is a real gap.

`toGL` map (line 200-205):

```lean
def toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n → α) :=
  GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)

theorem coe_toGL (A : unitaryGroup n α) : (toGL A).1 = toLin' A := rfl
```

### 1h. `Mathlib/MeasureTheory/Measure/Prod.lean` and `Mathlib/MeasureTheory/Group/Prod.lean`

**No `IsHaarMeasure.prod` or `prod_isHaarMeasure` theorem found anywhere in Mathlib.** This is a significant gap. The closest is `Group/Prod.lean:83-93`:

```lean
theorem measurePreserving_prod_mul [IsMulLeftInvariant ν] :
    ...
theorem measurePreserving_prod_mul_swap [IsMulLeftInvariant μ] :
    ...
```

These are about measure-preserving maps on the product group, not about identifying `μ.prod ν` as a Haar measure on `G × H`.

For the additive setting, `prod_addHaar` exists (line 282 of OfBasis.lean):

```lean
theorem prod_addHaar (v : Basis ι ℝ E) (w : Basis ι' ℝ F) :
```

(signature continues, body identifies `(v.prod w).addHaar = v.addHaar.prod w.addHaar`). This is only for the basis-derived Haar measure on vector spaces, not the general Haar.

For our use case, we need: if `μ_K`, `μ_A`, `μ_N` are Haar measures on `K`, `A`, `N` then `μ_K.prod (μ_A.prod μ_N)` is a Haar-type measure on `K × A × N`. We will need to provide this as a fresh lemma (~50 lines), proving left-invariance directly from left-invariance of each factor.

### 1i. `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`

This file is about polar coordinate change for normed spaces (additive Haar measure), not about KAN-type factorizations on Lie groups. Key declarations (line 52, 143, 218):

```lean
def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1) :=
theorem measurePreserving_homeomorphUnitSphereProd :
theorem toSphereBallBound_mul_measure_unitBall_le_toSphere_ball ...
```

**This file does NOT provide a Haar pushforward through a KAN-type factorization.** No analog of the Iwasawa Haar formula exists in Mathlib.

`Mathlib/MeasureTheory/Measure/Haar/Quotient.lean` (468 lines) handles the `G/Γ` quotient measure construction for discrete normal subgroups. Key declaration (line 223-225):

```lean
theorem MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient
    [LocallyCompactSpace G] [QuotientMeasureEqMeasurePreimage ν μ]
    [i : HasFundamentalDomain Γ.op G ν] [IsFiniteMeasure μ] : IsHaarMeasure μ
```

This is for `Γ` a discrete subgroup, not for our continuous `K × A × N → G` decomposition. Not directly applicable.

### 1j. Crucial Mathlib finding for §3 routing: `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`

`map_linearMap_addHaar_eq_smul_addHaar` (line 234-235):

```lean
theorem map_linearMap_addHaar_eq_smul_addHaar {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) :
    Measure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ := by
```

`addHaar_image_linearMap` (line 300-301):

```lean
@[simp]
theorem addHaar_image_linearMap (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s := by
```

These are the key lemmas. For the conjugation action of `a : A n` on `NN n` (which IS a linear map on the vector space `NN n`), we get:

```lean
μ (a • s) = ENNReal.ofReal |LinearMap.det (adNN a)| * μ s
```

where `μ` is any additive Haar on `NN n`. Combining with `distribHaarChar_eq_of_measure_smul_eq_mul` (DistribChar.lean:92-95), this gives:

```lean
distribHaarChar (NN n) a = |LinearMap.det (adNN a).toLinearMap|
```

which then equals `∏_{i<j} a_i/a_j` by `adNN_det_eq_pair_product` (already in the project). **This is the modular character routing, completable in ~30-50 lines once the typeclass instances on A and NN are in place.**

Variable bindings for `EqHaar.lean` linear-map section (line 231-232):

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
```

So we need `[FiniteDimensional ℝ (NN n)]` (automatic from `NN n` being a finite-dim submodule of `Matrix _ _ ℝ`), `[MeasurableSpace (NN n)]`, `[BorelSpace (NN n)]`, and an `IsAddHaarMeasure` instance on `NN n`. The last comes for free from any `Basis.addHaar` on `NN n` since it is a finite-dim normed real vector space.

---

## Section 2. The Cayley exterior power risk

### 2a. Mathlib's exterior power machinery

Only `Mathlib/Algebra/Category/ModuleCat/ExteriorPower.lean` (in the category-theoretic ModuleCat hierarchy). No `Mathlib/LinearAlgebra/ExteriorPower/*.lean` exists. Found declarations (line 30-113):

```lean
def exteriorPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
def AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :=
def postcomp : M.AlternatingMap N' n :=
def mk {M : ModuleCat.{v} R} {n : ℕ} :
def desc_mk ...
```

**No theorem `LinearMap.det (exteriorPower n f) = ?` exists.** No formula `det Λ^k f = (det f)^{C(n-1, k-1)}` is in Mathlib. This is a real gap.

For our specific application (Cayley derivative determinant at general `X`), we would need the relation `det (Λ^k f) = (det f)^{C(n-1, k-1)}` specifically for `k = 2` on `Λ^2(ℝⁿ) ≅ Sk(n)`. Lifting this from Mathlib's `ModuleCat.ExteriorPower` would require an `ExteriorPower → LinearMap.det` bridge that does not currently exist.

**Estimate to add:** ~200-300 lines for the general formula, or ~100 lines for just the `k = 2` case via direct entry computation in the `skBasis`.

### 2b. Mobius-type rational matrix determinants

Search results for `det_inv`, `det_one_add`, `det_one_sub`, `det_smul`, `det (1 + X)(1 - X)` style formulas:

`Mathlib/LinearAlgebra/Determinant.lean:694`:

```lean
theorem det_inv (b : Basis ι A M) (b' : Basis ι A M) :
```

(This is `det` of basis change inverse, not matrix inverse.)

`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:109`:

```lean
theorem det_invOf [Invertible A] [Invertible A.det] : (⅟A).det = ⅟A.det := by
```

`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:271`:

```lean
theorem det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^ Fintype.card n * det A :=
```

**No `det (1 + X)`, `det (1 - X)`, `det (1 - X²)`, `det ((1+X)(1-X))` packaged formulas in Mathlib.** These are all elementary but not pre-packaged.

`Matrix.det_add` does NOT exist (det is not additive). Determinants of `1 + X` etc. would be handled via `Matrix.det_one_add_mul_comm`, `Matrix.det_one_sub_mul_self_eq` style lemmas if they existed. They don't.

`Matrix.det_one_add_mul_comm` does exist:

```lean
-- in Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean
-- (verified by grep; signature not pulled here)
```

But this is the determinant of `1 + A * B = 1 + B * A` after Sylvester-style identity, not directly useful for Cayley.

### 2c. Cayley-specific search

`grep -rn "cayley" Mathlib/`: 

```
Mathlib/Analysis/Normed/Group/Defs.lean:33:  ... in the Cayley graph of the
Mathlib/GroupTheory/Perm/Subgroup.lean:24:  ... Cayley's theorem ...
Mathlib/GroupTheory/Perm/Subgroup.lean:68:  /-- **Cayley's theorem**: ...
Mathlib/RingTheory/MatrixPolynomialAlgebra.lean:25:  ... Cayley-Hamilton theorem.
```

**The Cayley transform `(1 - X)(1 + X)^{-1}` is NOT in Mathlib.** All hits are for unrelated Cayley constructions (Cayley graph in group theory, Cayley's theorem on permutations, Cayley-Hamilton). The project's own `IwasawaCoC.cayley` is the only Cayley transform implementation.

### 2d. Skew-symmetric eigenvalue argument

`grep -rn "isSkewAdjoint" Mathlib/LinearAlgebra/`:

```
Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:587: def IsSkewAdjoint (f : M → M) :=
Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:625: theorem isSkewAdjoint_iff_neg_self_adjoint
Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:636: ... f ∈ B.skewAdjointSubmodule ↔ B.IsSkewAdjoint f
Mathlib/LinearAlgebra/Matrix/SesquilinearForm.lean:562: protected def Matrix.IsSkewAdjoint :=
Mathlib/LinearAlgebra/Matrix/SesquilinearForm.lean:654: ... skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A
```

`IsSkewAdjoint` is defined relative to a bilinear form `B`. There's no direct "real skew matrix → eigenvalues are 0 or ±iλ" lemma. The project's `one_add_skew_isUnit` ([IwasawaCoC.lean:1034](iwasawa_change_of_coords/IwasawaCoC.lean:1034)) is the only existing form of this fact in our code, and it does NOT route through `IsSkewAdjoint`.

For the general-point `|det dF|` formula, we don't need the full eigenvalue argument (we already have `one_add_skew_isUnit`). What we need is the explicit derivative formula for cayley, namely `cayley'(X)(δX) = -δX(1+X)⁻¹ - cayley(X)(1+X)⁻¹δX`, and its determinant. This is straightforward differentiation; Mathlib's `HasFDerivAt.inv'` plus chain rule covers it. ~50 lines for the derivative, ~150 lines for the determinant (the Plücker exterior power identification).

### 2e. Risk summary

| Item | Status | Adaptation lines |
|---|---|---|
| Cayley transform definition in Mathlib | **MISSING** | n/a (project already has it) |
| Cayley derivative at general X (Fréchet) | **near miss** via `HasFDerivAt.inv'` + chain rule | ~50 |
| `det Λ^2(f)` formula | **MISSING** in Mathlib | ~200 (general) or ~100 (project-specific k=2) |
| `det (1 ± X)` | **MISSING** as packaged form | trivial inline |
| `det (1 - X²)` for X skew | **MISSING** as packaged form, but project's `one_add_skew_isUnit` covers the key step | trivial inline |
| `IsSkewAdjoint`-based eigenvalue argument | not the right abstraction; not needed | n/a |

**Verdict.** The Cayley exterior power gap is real and the single biggest unknown. Best path: build a specific `k = 2` formula at the level of the `skBasis` entries (the project already has `skOrthConjCLM_toMatrix_apply` doing this exact computation for orthogonal `k`). The same Plücker entry pattern generalizes to Cayley `(1+X)^{-1}` factors, but now with `X` skew not orthogonal. Estimate: **~250 lines** to get `|det dF(X, v, Z)|` as an explicit formula in `X, v, Z`, parallel to but not reusing the `skOrthConjCLM_toMatrix_apply` line of attack.

---

## Section 3. The modular function identification

### 3a. Most general identification: `distribHaarChar` of conjugation = `|det|`

There is no single theorem `distribHaarChar A g = |det (Ad g)|` in Mathlib. The pieces exist separately:

- `Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean:92-95` (`distribHaarChar_eq_of_measure_smul_eq_mul`): if `μ (g • s) = r * μ s`, then `distribHaarChar A g = r`.
- `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:300-301` (`addHaar_image_linearMap`): `μ (f '' s) = |det f| * μ s` for `f : E →ₗ[ℝ] E`.

**These compose.** For our setting:
- `A` (the additive group acted on) = `NN n` (strict upper triangular matrices, vector space).
- `G` (the acting group) = our `A n` (positive diagonals), acting on `NN n` via conjugation `(a, Z) ↦ a Z a^{-1}`, which is linear in `Z` and equals `adNN a (Z)`.
- The `r` factor is `|det (adNN a).toLinearMap|`.

The composition:

```lean
-- pseudo-Lean, not yet written:
theorem distribHaarChar_adNN (a : A n) :
    distribHaarChar (NN n) a = (|LinearMap.det (adNN a).toLinearMap|).toNNReal := by
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := b.addHaar) ... ...
  -- The measure of (adNN a) '' s equals |det adNN a| * μ s by addHaar_image_linearMap.
```

This is the **keystone routing** for §5 of `RemainingWork.md`. It requires:

1. `[DistribMulAction (A n) (NN n)]` instance for the conjugation action: ~10 lines.
2. `[ContinuousConstSMul (A n) (NN n)]` instance: ~10 lines.
3. The composition above: ~30 lines.

**Verdict on 3a:** No verbatim theorem, but the pieces are all present and compose. Estimated lift: ~50 lines.

### 3b. Closest specialization

For a vector space `V` with a `G`-action `G → GL(V)`, the abstract `distribHaarChar V g = |det (action g)|` is essentially the content of `addHaar_image_linearMap` combined with `distribHaarChar_eq_of_measure_smul_eq_mul`. **No more direct theorem found.**

For our specific case, `addHaar_image_linearMap` reads (verbatim, line 300-301 of EqHaar.lean):

```lean
theorem addHaar_image_linearMap (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s
```

This is the verbatim closest specialization. Lifting to `distribHaarChar` requires the wrapper above.

### 3c. Cross check against `ad_on_n_det_eq_pair_product`

The project's `IwasawaJacobianExplicit.ad_on_n_det_eq_pair_product` ([line 1874](iwasawa_change_of_coords/IwasawaJacobianExplicit.lean:1874)) states:

```lean
theorem ad_on_n_det_eq_pair_product (a : A n) :
    LinearMap.det (adNN a).toLinearMap =
      ∏ ij ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ij : Fin n × Fin n => ij.1 < ij.2),
        (a.1 ij.1 ij.1) / (a.1 ij.2 ij.2)
```

Composition: `distribHaarChar (NN n) a = ∏_{i<j} a_i/a_j` modulo absolute values (the product is positive since each ratio is positive).

**Cross check confirms.** The standard formula `δ_B(a) = ∏_{i<j} a_i/a_j` matches `ad_on_n_det_eq_pair_product` exactly. No discrepancy.

---

## Section 4. External references

### 4a. Paul Garrett notes

URL `https://www-users.cse.umn.edu/~garrett/m/v/iwasawa.pdf`: redirects to error page (file moved or removed as of 2026-05-27).

Closest available Garrett source on the topic is `https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/12_2_transition_Eis.pdf` (May 2016 update). PDF fetch returned binary content not parseable by the fetcher; no formula extraction possible.

**Fetch failed.** Recorded in §6.

### 4b. nLab pages

URL `https://ncatlab.org/nlab/show/Iwasawa+decomposition` (fetched 2026-05-27):

Verbatim content:
- "An Iwasawa decomposition is an analytic diffeomorphism `G ≃ K × A × N`" where `K`, `A`, `N` are as in our project (no surprises).
- **No explicit Haar measure formula** on the nLab page. The article's text stops at the diffeomorphism statement.

URL `https://ncatlab.org/nlab/show/modular+function` (fetched 2026-05-27):

The nLab article under "modular function" is about MODULAR FORMS (number theory), not the modular function of a topological group. **Wrong namespace clash; no useful content for our purposes.**

### 4c. Wikipedia

URL `https://en.wikipedia.org/wiki/Iwasawa_decomposition` (fetched 2026-05-27):

Verbatim relevant content:
- For `SL(n, ℝ)`: `K` = orthogonal matrices, `A` = positive diagonal with `det = 1`, `N` = unipotent upper triangular with 1s on the diagonal.
- "There is an analytic diffeomorphism... from the manifold `K × A × N` to the Lie group `G`, sending `(k, a, n) ↦ kan`."
- **No explicit Haar measure formula** or modular function formula given.

URL `https://en.wikipedia.org/wiki/Haar_measure` (fetched 2026-05-27):

Verbatim content (section: "The modular function"):
- "`ν(g⁻¹ S) = Δ(g) ν(S)`" (defining property).
- "`GL(n, ℝ) is unimodular`" (whole group, not the Borel).
- For "upper triangular group in `SL₂(ℝ)`": modular function is "nontrivial", no explicit formula given.

**No discrepancy with our convention.** Wikipedia gives no specific formula for `δ_B`.

### 4d. arXiv hits

Top five for "Iwasawa decomposition" "GL(n)" or "SL(n)":

1. **[arXiv:1609.06621](https://arxiv.org/abs/1609.06621)** — Åhlén, "Global Iwasawa-decomposition of `SL(n, 𝔸_ℚ)`", 2016. Abstract: "We discuss the Iwasawa-decomposition of a general matrix in `SL(n, ℚ_p)` and `SL(n, ℝ)`." Algorithmic decomposition focus, no Haar formulas in the abstract.

2. **[arXiv:1404.5535](https://arxiv.org/abs/1404.5535)** — El-Hussein, "Abstract Harmonic Analysis on the General Linear Group `GL(n, ℝ)`", 2014. Plancherel theorem via Iwasawa decomposition. Abstract does not mention explicit Haar formulas; full paper might.

3. **[arXiv:1604.03613](https://arxiv.org/pdf/1604.03613)** — Garbali and Roczen (?), "Comparison of Volumes of Siegel Sets and Fundamental Domains for `SL_n(Z)`". Mentions explicit Haar normalization for `SL_n(ℝ)/SL_n(ℤ)`.

4. **[arXiv:math/0506330](https://arxiv.org/pdf/math/0506330)** — Iwasawa decomposition of the Lie supergroup `SL(n, m, ℂ)`, 2005. Supergroup focus, less directly relevant.

5. **[arXiv:1010.0346](https://arxiv.org/abs/1010.0346)** — "A note on Iwasawa-type decomposition", 2010. Abstract not retrieved.

**Of these, [arXiv:1404.5535](https://arxiv.org/abs/1404.5535) is the most directly relevant** for `GL(n, ℝ)`. Did not fetch full PDF.

CJ Dowd, "Notes on Haar measures on Lie groups", `https://math.berkeley.edu/~cjdowd/haar1.pdf` (April 2023). Fetched but PDF content not parseable. Web search result claims the document contains "explicit Jacobian calculations for Iwasawa decomposition, including... `vw² (left) and vw (right)` for `GL₂(ℝ)`". Cannot verify the exact formula without successful PDF fetch.

### 4e. Deferred to human reader

The following claims would require book reading to verify and are NOT verified through web sources alone:

- **Knapp, *Lie Groups Beyond an Introduction* 2nd ed (2002), Ch VIII §2:** the modular function formula `δ_B(a) = ∏_{α ∈ Σ⁺} a^α`. Standard formula; consistent with our `ad_on_n_det_eq_pair_product` after the specialization `α_{ij}(a) = a_i/a_j` for `SL(n)`.
- **Goldfeld, *Automorphic Forms and L-Functions for the Group `GL(n, ℝ)`* (2006), Prop 1.5.3:** the explicit Iwasawa Haar density. Standard.
- **Bump, *Lie Groups* 2nd ed (2013), Prop 18.4:** cross-check for the SL(n) modular function. Standard.
- **Helgason, *DGLGSS* (1978), Ch I §5:** abstract `dG = δ(a) dK dA dN`. Standard.
- **The `2^{n(n-1)/2}` prefactor** in our `absDetInIwasawaBases_one_a_one_eq_scaled_det_pow_mul_det_adNN` is chart-dependent (Cayley first-order). Verifiable by direct calculation; matches Goldfeld's formulas only after accounting for the chart convention (Goldfeld typically uses exponential coordinates that absorb the factor differently).

Each of these is a load-bearing claim in `RemainingWork.md §1` (the modular function cross-reference table). The web-fetchable sources (Wikipedia, nLab) confirm only the abstract structure; the explicit formulas in the table require book verification.

---

## Section 5. Coordination risk redux

### 5a. Mathlib4 GitHub search (2026-05-27)

PRs matching key terms:

- **"Iwasawa"**: 5 open PRs. None about Iwasawa decomposition of Lie groups; all are Kan extensions, Eisenstein series, or unrelated number theory.
- **"distribHaarChar"**: 0 open PRs, 3 closed/merged:
  - **PR 23603** (merged 2025-04-24): "feat: distributive Haar characters" — introduced the file. Stable.
  - **PR 24383** (closed 2026-05-01): "feat: distributive Haar characters of `ℝ` and `ℂ`". Closed without merging.
  - **PR 24373** (closed 2026-05-01): "refactor: golf modularCharacter". Closed without merging.
- **"modular function"**: 5 open PRs. None about Haar/Lie group modular functions; all categorical or analytic.
- **"KAN"**: no relevant open PRs (Kan extensions are categorical Kan, not Iwasawa KAN).
- **"orthogonalGroup"**: no open PRs touching the topology, compactness, or Haar of `Matrix.orthogonalGroup`.
- **"Haar measure" "Lie group"**: no in-flight Iwasawa-style PRs.

Issues:
- **"Iwasawa decomposition"**: no open issues.
- **"Haar measure Lie group"**: no open issues directly relevant.

There is a related ongoing effort, **Issue 38374 / PR 30121** ("Principal Bundles, Connection 1-forms and the Frame Bundle" — `t-differential-geometry`), but it is about manifolds and bundles, not Haar measure on Lie groups.

### 5b. Lean Zulip

Zulip search was not run in this session due to lack of programmatic access. Manual review recommended:
- `leanprover.zulipchat.com` topic search for "Iwasawa", "Haar measure GL", "modular character" in the `#mathlib4` stream.

**Coordination risk: LOW.** No active Mathlib effort on the Iwasawa-Haar-pushforward chain. The `distribHaarChar` infrastructure is stable (last touch May 2025). No one is currently formalizing `GL(n, ℝ)` Haar measure as far as I can determine.

Same conclusion as `RemainingWork.md`: **no change since 2026-05-27**.

---

## Section 6. Open questions for the human reader

- **Q1. Garrett URL.** The standard URL `https://www-users.cse.umn.edu/~garrett/m/v/iwasawa.pdf` redirects to an error page as of 2026-05-27. Has Garrett moved his notes? If yes, the new URL is needed for direct citation of Garrett's normalization. Impact: low — the formula is standard and matches our derivation.

- **Q2. PDF parsing.** The `WebFetch` tool returned binary content for the Garrett 2016 PDF and the CJ Dowd 2023 PDF, both unreadable. Are there plaintext or HTML versions of these references accessible to a future session? Impact: medium — without access, the "Knapp/Goldfeld parity check" recommended in `RemainingWork.md §1` falls back on standard formula matching rather than direct quotation.

- **Q3. `prod_isHaarMeasure` is missing.** Mathlib has `Group.Prod` measure-preservation lemmas but no theorem stating "product of two Haar measures on a product group is Haar". For our setting, we need to prove this directly for `(haar_K ×ₘ haar_A ×ₘ haar_N)` on `K × A × N`. Should this be contributed upstream as a generic Mathlib PR? Impact: medium — adds ~50 lines locally regardless of choice; upstream contribution would benefit Mathlib but takes review time.

- **Q4. `CompactSpace (orthogonalGroup (Fin n) ℝ)` is missing.** No Mathlib instance. Required for our `K n` Haar measure construction. Should this be contributed upstream? The proof is standard (closed and bounded subset of finite-dim normed space → compact). Impact: low — ~40 lines locally; upstream contribution would benefit Mathlib but is a separate workflow.

- **Q5. `LocallyCompactSpace` instances on `SL(n, ℝ)` and `GL(n, ℝ)`.** No instances declared in Mathlib. Both are locally compact (as open subsets of finite-dim normed space) but the instance is not registered. Should the next session add these? Impact: medium — `haarMeasure` requires `LocallyCompactSpace`, so without these the construction stalls.

- **Q6. ExteriorPower determinant formula.** Mathlib has `Algebra/Category/ModuleCat/ExteriorPower.lean` but no `LinearMap.det (exteriorPower n f)` formula. For the Cayley general-point Jacobian we either (a) prove a project-specific `k = 2` Plücker formula by direct entry computation (~150 lines), or (b) contribute a general exterior power det formula upstream (~300 lines, slower). Which route does the next session prefer? Impact: high — this is the Cayley exterior power risk from `RemainingWork.md §4`, and it determines whether the general-point absolute Jacobian is closable in ~250 or ~400 lines.

- **Q7. `G n` redefinition decision is still open.** `RemainingWork.md §2.1` and §10 give the trade-offs (~5-10 person-days to redefine vs ~150 lines to mirror Mathlib instances). The next session needs an explicit choice before §2 work can begin.

- **Q8. Source-target equality of `f : E → E` in `integral_image_eq_integral_abs_det_fderiv_smul`.** Confirmed in §1d: yes, source = target = `E`. **No off-square variant.** Our chart strategy (Sk × ℝ^n × NN identified with ℝ^{n²} via `iwasawaSourceBasis`, target = Matrix ≅ ℝ^{n²}) was already correct in `RemainingWork.md §4.1`. No change.

- **Q9. Component-of-Iwasawa-image measure-zero argument.** `RemainingWork.md §7` step 6 mentions "argue measure zero of complement". By the domain universality lemma `iwasawaChartedDomain_eq_univ` (proven this session at [IwasawaComplete.lean:634](iwasawa_change_of_coords/IwasawaComplete.lean:634)), the Cayley chart covers the WHOLE source. The image is therefore `iwasawaCharted '' univ = (iwasawa map composed with Cayley etc.) '' univ`, which IS not all of `GL(n, ℝ)`: the `K_open` subset is `{Q ∈ K : 1 + Q invertible}`, which is dense but not all of `K`. So the complement-measure-zero argument is still needed — specifically that `K \ K_open` has Haar measure zero. This is a separate small lemma (~30 lines): `K \ K_open ⊂ {Q : det(1+Q) = 0}`, a real-analytic hypersurface, hence Lebesgue measure zero. **Confirmed needed; flagged for the next session.**

---

## Section 7. Summary of Mathlib gaps identified

Net new "MISSING" items found in this intel pass (beyond what `RemainingWork.md` already lists):

1. **`prod_isHaarMeasure`** for arbitrary Haar measures (Mathlib has only basis-derived additive version).
2. **`CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ)`** not declared.
3. **`LocallyCompactSpace (Matrix.SpecialLinearGroup (Fin n) ℝ)`** not declared.
4. **`LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin n) ℝ)`** not declared.
5. **`det (exteriorPower 2 f) = ?`** formula not in Mathlib.
6. **`det (1 - X²)` for `X` skew** not a packaged form (workable inline).
7. **Cayley transform `(1 - X)(1 + X)⁻¹`** not in Mathlib at all (only in project).
8. **Modular function of `AN` parabolic = `|det adNN a|`** abstract theorem missing; the pieces in Mathlib compose to it but no packaged statement.

Items 1, 2, 3, 4, 8 are good candidates for upstream Mathlib PRs after the next session lands the project-internal versions.

---

## Section 8. References fetched this session

| URL | Date | Status |
|---|---|---|
| `https://en.wikipedia.org/wiki/Iwasawa_decomposition` | 2026-05-27 | success; no Haar formulas |
| `https://en.wikipedia.org/wiki/Haar_measure` | 2026-05-27 | success; confirmed `GL(n)` unimodular, `δ_B` "nontrivial" but unspecified |
| `https://ncatlab.org/nlab/show/Iwasawa+decomposition` | 2026-05-27 | success; abstract content only |
| `https://ncatlab.org/nlab/show/modular+function` | 2026-05-27 | success; wrong topic (modular forms) |
| `https://www-users.cse.umn.edu/~garrett/m/v/iwasawa.pdf` | 2026-05-27 | REDIRECT to error page |
| `https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/12_2_transition_Eis.pdf` | 2026-05-27 | binary fetch; not parseable |
| `https://math.berkeley.edu/~cjdowd/haar1.pdf` | 2026-05-27 | binary fetch; not parseable |
| `https://arxiv.org/abs/1609.06621` (Åhlén) | 2026-05-27 | abstract retrieved; no Haar formula |
| `https://arxiv.org/abs/1404.5535` (El-Hussein) | 2026-05-27 | abstract retrieved; no formula |

Mathlib source files inspected (all in `.lake/packages/mathlib/Mathlib/`):

| File | Lines | Topic |
|---|---|---|
| `MeasureTheory/Measure/Haar/Basic.lean` | 700 | `haarMeasure`, `IsHaarMeasure`, uniqueness |
| `MeasureTheory/Measure/Haar/DistribChar.lean` | 97 (full read) | `distribHaarChar`, modular character routing |
| `MeasureTheory/Measure/Haar/OfBasis.lean` | 319 | Basis-derived Haar on vector spaces |
| `MeasureTheory/Measure/Haar/Quotient.lean` | 468 | Quotient by discrete subgroup (not directly relevant) |
| `MeasureTheory/Measure/Haar/MulEquivHaarChar.lean` | 150 | Haar scaling under isomorphism |
| `MeasureTheory/Measure/Haar/InnerProductSpace.lean` | 253 | OrthonormalBasis Haar (specialized) |
| `MeasureTheory/Measure/Lebesgue/EqHaar.lean` | 600+ (selected) | **Key linear map identity** for §3 routing |
| `MeasureTheory/Function/Jacobian.lean` | 1240+ (selected) | Change of variables theorem; `f : E → E` |
| `MeasureTheory/Group/Measure.lean` | (selected, line 770) | `IsHaarMeasure` class definition |
| `MeasureTheory/Group/Prod.lean` | (full grep) | Measure-preservation on products; no Haar identification |
| `LinearAlgebra/Matrix/SpecialLinearGroup.lean` | 527 (TOC) | `Group` instance; no `LocallyCompactSpace` |
| `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` | 396 (TOC) | `(Matrix n n R)ˣ` definition |
| `LinearAlgebra/UnitaryGroup.lean` | 345 | `unitaryGroup` and `orthogonalGroup`; no `CompactSpace` |
| `Topology/Algebra/Group/Matrix.lean` | 190 | `TopologicalGroup (SL n R)`, `(GL n R)` |
| `Algebra/Category/ModuleCat/ExteriorPower.lean` | (selected) | `ExteriorPower` definition; no `det` formula |
