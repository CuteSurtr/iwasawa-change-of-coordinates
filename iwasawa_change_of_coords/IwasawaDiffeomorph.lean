/-
Iwasawa decomposition as a `Diffeomorph`.

Tier 1, Stage T1-2. Builds `iwasawaDiffeomorph` bundling the
existing set-theoretic `iwasawaEquiv : K n × A n × UU n ≃ G n` as a
smooth manifold diffeomorphism. The forward direction `iwasawaMap`
is smooth because matrix multiplication is bilinear; the inverse
direction is smooth because Gram-Schmidt is rational with positive
denominator (parallelling the existing continuity proof in
`IwasawaCoC`).

Implementation note. As in `IwasawaSmoothK`, we use the `linfty op`
operator-norm structure on `Matrix (Fin n) (Fin n) ℝ` so that the
`NormedRing` and `NormedAlgebra` instances needed by ContDiff
machinery are available. The K-manifold instance `instIsManifoldK`
from `IwasawaSmoothK` is built with this norm; the G-manifold
instance from `IwasawaCoC` used the `sup of sup` norm. We re-derive
`G`'s manifold structure here under the `linfty op` norm so that
both ends of `iwasawaDiffeomorph` sit in a single normed-structure
context.
-/

import iwasawa_change_of_coords.IwasawaSmoothK
import iwasawa_change_of_coords.MatrixContDiff
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

namespace IwasawaCoC

open Matrix Iwasawa Topology Set Function InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n : ℕ}

section MatrixNormedContext

/-! ## Local normed structures on `Matrix _ _ ℝ`

Same set as in `IwasawaSmoothK`: enable the `linfty op` operator norm so
`Matrix` becomes a `NormedRing` / `NormedAlgebra` over `ℝ`. -/

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedSpace
attribute [local instance] Matrix.linftyOpNonUnitalSemiNormedRing
attribute [local instance] Matrix.linftyOpSemiNormedRing
attribute [local instance] Matrix.linftyOpNonUnitalNormedRing
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## G as an open submanifold under the `linfty op` norm

The existing `instIsManifoldG` in `IwasawaCoC` is declared under the
`sup of sup` matrix norm, which differs from the `linfty op` norm we
need here. We re-derive the open-embedding ChartedSpace and IsManifold
instances under our local norm choice. The topology agrees with the
sup-of-sup version (both are equivalent to Frobenius on a
finite-dimensional space), so the resulting smooth structure is the
same modulo norm choice. -/

/-- ChartedSpace on `G n` under the local `linfty op` matrix norm. -/
noncomputable instance instChartedSpaceG_linfty :
    ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (G n) :=
  G_isOpenEmbedding.singletonChartedSpace

/-- `G n` is a smooth manifold under the local `linfty op` matrix norm. -/
instance instIsManifoldG_linfty :
    IsManifold (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤ (G n) :=
  G_isOpenEmbedding.isManifold_singleton

/-! ### A and UU re-derived under the local `linfty op` matrix norm

The instances in `IwasawaCoC` for `A n` and `UU n` were declared under
the sup-of-sup matrix norm scope. Their `IsManifold` types reference
`𝓘(ℝ, NN n)` / `𝓘(ℝ, Fin n → ℝ)` evaluated with the matrix-norm-dependent
submodule normed structures. We re-derive them here under our `linfty op`
scope so they fire with the right normed-structure interpretation. -/

instance instIsManifoldA_linfty :
    IsManifold (𝓘(ℝ, (Fin n → ℝ))) ⊤ (A n) :=
  OpenPartialHomeomorph.isManifold_singleton
    (A.toFinNRHomeomorph.toOpenPartialHomeomorph) (by simp)

instance instIsManifoldUU_linfty :
    IsManifold (𝓘(ℝ, (NN n : Type _))) ⊤ (UU n) :=
  OpenPartialHomeomorph.isManifold_singleton
    (UU.toNNHomeomorph.toOpenPartialHomeomorph) (by simp)

/-! ## Cayley is C^∞ on `Sk n`

For `X : Sk n`, `1 + X.1` is always invertible (`one_add_skew_isUnit`),
so the Cayley transform is `C^∞` on all of `Sk n`. -/

theorem contDiff_cayley_subtype_val :
    ContDiff ℝ ⊤ (fun X : Sk n => cayley X.1) := by
  rw [contDiff_iff_contDiffAt]
  intro X
  have h : IsUnit (1 + X.1 : Matrix (Fin n) (Fin n) ℝ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (one_add_skew_isUnit X)
  exact (contDiffAt_cayley h).comp X (Sk n).subtypeL.contDiff.contDiffAt

/-! ## CLM retracts `aaProj`, `nnProj`

These complement `skProj` from `IwasawaSmoothK`. Each is a continuous-
linear map `Matrix _ _ ℝ → submodule` realizing the natural projection
(diagonal / strict upper triangular). They are the retracts that lift
matrix-valued smoothness to submodule-valued smoothness via composition. -/

/-- Linear diagonal projection `Matrix _ _ ℝ →ₗ[ℝ] AA n`,
`M ↦ diag(M_{ii})`. -/
private def aaLinearProj :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] AA n where
  toFun M := ⟨Matrix.diagonal (fun i => M i i), by
    intro i j hij
    exact Matrix.diagonal_apply_ne _ hij⟩
  map_add' M N := by
    apply Subtype.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij]
  map_smul' c M := by
    apply Subtype.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij]

/-- Continuous diagonal projection `Matrix _ _ ℝ →L[ℝ] AA n`. -/
noncomputable def aaProj :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] AA n :=
  LinearMap.toContinuousLinearMap aaLinearProj

@[simp] lemma aaProj_apply_val (M : Matrix (Fin n) (Fin n) ℝ) :
    (aaProj M : AA n).1 = Matrix.diagonal (fun i => M i i) := rfl

/-- Linear strict-upper-triangular projection `Matrix _ _ ℝ →ₗ[ℝ] NN n`. -/
private def nnLinearProj :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] NN n where
  toFun M := ⟨Matrix.of (fun i j => if i < j then M i j else 0), by
    intro i j hji
    show (Matrix.of fun i j => if i < j then M i j else 0) i j = 0
    simp only [Matrix.of_apply]
    rw [if_neg (not_lt.mpr hji)]⟩
  map_add' M N := by
    apply Subtype.ext
    ext i j
    show (Matrix.of fun i j => if i < j then (M + N) i j else 0) i j =
         ((Matrix.of fun i j => if i < j then M i j else 0)
            + Matrix.of fun i j => if i < j then N i j else 0) i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    by_cases hij : i < j <;> simp [hij]
  map_smul' c M := by
    apply Subtype.ext
    ext i j
    show (Matrix.of fun i j => if i < j then (c • M) i j else 0) i j =
         (c • Matrix.of fun i j => if i < j then M i j else 0) i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    by_cases hij : i < j <;> simp [hij]

/-- Continuous strict-upper-triangular projection `Matrix _ _ ℝ →L[ℝ] NN n`. -/
noncomputable def nnProj :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] NN n :=
  LinearMap.toContinuousLinearMap nnLinearProj

@[simp] lemma nnProj_apply_val (M : Matrix (Fin n) (Fin n) ℝ) :
    (nnProj M : NN n).1 = Matrix.of (fun i j => if i < j then M i j else 0) := rfl

/-! ## Subtype embeddings `K, A, UU → Matrix` are `C∞` -/

/-- The inclusion `Subtype.val : K n → Matrix _ _ ℝ` is `C∞`. -/
theorem contMDiff_K_subtypeVal :
    ContMDiff (𝓘(ℝ, (Sk n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
      ((↑) : K n → Matrix (Fin n) (Fin n) ℝ) := by
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  intro x _y
  -- After simp simplification of trivial chart on Matrix and chartAt on K,
  -- the function and domain reduce.
  apply ContDiff.contDiffOn
  -- Match the chart-coord function with `fun X => cayley X.1 * x.1`.
  have h_funext :
      (extChartAt 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) _y ∘ ((↑) : K n → Matrix (Fin n) (Fin n) ℝ) ∘
          (extChartAt 𝓘(ℝ, (Sk n : Type _)) x).symm) =
        fun X : Sk n => cayley X.1 * x.1 := by
    funext X
    show (((extChartAt 𝓘(ℝ, (Sk n : Type _)) x).symm X) : K n).1 = cayley X.1 * x.1
    -- The extChartAt for K with model 𝓘(ℝ, Sk n) reduces to cayleyOpenChartAt x.
    show ((cayleyOpenChartAt x).symm X).1 = cayley X.1 * x.1
    exact cayleyOpenChartAt_symm_apply_val x X
  rw [h_funext]
  exact contDiff_cayley_subtype_val.mul contDiff_const

/-- The inclusion `Subtype.val : A n → Matrix _ _ ℝ` is `C∞`. -/
theorem contMDiff_A_subtypeVal :
    ContMDiff (𝓘(ℝ, (Fin n → ℝ))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
      ((↑) : A n → Matrix (Fin n) (Fin n) ℝ) := by
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  intro D _y
  apply ContDiff.contDiffOn
  -- Chart-coord function reduces to `v ↦ Matrix.diagonal (fun i => Real.exp (v i))`.
  have h_funext :
      (extChartAt 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) _y ∘ ((↑) : A n → Matrix (Fin n) (Fin n) ℝ) ∘
          (extChartAt 𝓘(ℝ, (Fin n → ℝ)) D).symm) =
        fun v : Fin n → ℝ => Matrix.diagonal (fun i => Real.exp (v i)) := by
    funext v
    show ((A.toFinNRHomeomorph.symm v) : A n).1 = Matrix.diagonal (fun i => Real.exp (v i))
    rfl
  rw [h_funext]
  -- `v ↦ Real.exp (v i)` is ContDiff for each i, hence the pointwise function is ContDiff.
  have h_exp_pi : ContDiff ℝ ⊤ (fun v : Fin n → ℝ => fun i => Real.exp (v i)) := by
    rw [contDiff_pi]
    intro i
    exact Real.contDiff_exp.comp
      ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contDiff)
  -- Compose with `Matrix.diagonalLinearMap` promoted to a continuous linear map.
  set D : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonalLinearMap (n := Fin n) (R := ℝ) (α := ℝ) with hD_def
  have h_diag : ContDiff ℝ ⊤ (LinearMap.toContinuousLinearMap D : (Fin n → ℝ) → Matrix _ _ ℝ) :=
    (LinearMap.toContinuousLinearMap D).contDiff
  have h_target_eq :
      (fun v : Fin n → ℝ => Matrix.diagonal (fun i => Real.exp (v i))) =
        (LinearMap.toContinuousLinearMap D : (Fin n → ℝ) → Matrix _ _ ℝ) ∘
          (fun v : Fin n → ℝ => fun i => Real.exp (v i)) := by
    funext v
    show Matrix.diagonal _ = D _
    rfl
  rw [h_target_eq]
  exact h_diag.comp h_exp_pi

/-- The inclusion `Subtype.val : UU n → Matrix _ _ ℝ` is `C∞`. -/
theorem contMDiff_UU_subtypeVal :
    ContMDiff (𝓘(ℝ, (NN n : Type _))) (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
      ((↑) : UU n → Matrix (Fin n) (Fin n) ℝ) := by
  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  intro U _y
  apply ContDiff.contDiffOn
  -- Chart-coord function reduces to `X ↦ X.1 + 1`.
  have h_funext :
      (extChartAt 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) _y ∘ ((↑) : UU n → Matrix (Fin n) (Fin n) ℝ) ∘
          (extChartAt 𝓘(ℝ, (NN n : Type _)) U).symm) =
        fun X : NN n => X.1 + 1 := by
    funext X
    show ((UU.toNNHomeomorph.symm X) : UU n).1 = X.1 + 1
    rfl
  rw [h_funext]
  exact (NN n).subtypeL.contDiff.add contDiff_const

/-! ## Forward direction: `iwasawaMap` is `C∞` -/

/-- **Forward.** The Iwasawa product map `(k, a, u) ↦ k · a · u` is `C∞`
on the product manifold `K × A × UU` with target `G n` (an open
submanifold of `Matrix _ _ ℝ`). -/
theorem contMDiff_iwasawaMap :
    ContMDiff ((𝓘(ℝ, (Sk n : Type _))).prod
                ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
              (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
              (iwasawaMap : K n × A n × UU n → G n) := by
  -- Use `ContMDiff.of_comp_isOpenEmbedding` to reduce to matrix-level target.
  refine ContMDiff.of_comp_isOpenEmbedding G_isOpenEmbedding ?_
  -- Need: `ContMDiff ... (Subtype.val ∘ iwasawaMap : K × A × UU → Matrix _ _ ℝ)`
  -- which equals `(k, a, u) ↦ k.1 * a.1 * u.1`.
  -- Project to each factor and multiply.
  have h_K_proj :
      ContMDiff ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
                (fun p : K n × A n × UU n => p.1.1) :=
    contMDiff_K_subtypeVal.comp contMDiff_fst
  have h_A_proj :
      ContMDiff ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
                (fun p : K n × A n × UU n => p.2.1.1) :=
    contMDiff_A_subtypeVal.comp (contMDiff_fst.comp contMDiff_snd)
  have h_UU_proj :
      ContMDiff ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
                (fun p : K n × A n × UU n => p.2.2.1) :=
    contMDiff_UU_subtypeVal.comp (contMDiff_snd.comp contMDiff_snd)
  -- Multiply via `contDiff_mul`.
  have h_mul : ContDiff ℝ ⊤
      (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => p.1 * p.2) :=
    contDiff_mul
  -- Bilinear multiplication promoted to a ContMDiff with the `.prod` source model.
  -- (Pattern taken from `instFieldContMDiffRing` in `Mathlib/Geometry/Manifold/Algebra/Structures.lean`.)
  have h_mul_prod : ContMDiff
      ((𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)).prod (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)))
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
      (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => p.1 * p.2) := by
    rw [contMDiff_iff]
    refine ⟨continuous_mul, fun _ _ => ?_⟩
    simp only [mfld_simps, Function.comp, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
               Set.preimage_id]
    exact contDiff_mul.contDiffOn
  -- Combine: `(k.1 * a.1) * u.1`. First build `k.1 * a.1`.
  have h_K_A_mul :
      ContMDiff ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
                (fun p : K n × A n × UU n => p.1.1 * p.2.1.1) :=
    h_mul_prod.comp (h_K_proj.prodMk h_A_proj)
  -- Then multiply by u.1.
  have h_full :
      ContMDiff ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ⊤
                (fun p : K n × A n × UU n => p.1.1 * p.2.1.1 * p.2.2.1) :=
    h_mul_prod.comp (h_K_A_mul.prodMk h_UU_proj)
  -- This is exactly `Subtype.val ∘ iwasawaMap`.
  convert h_full using 1

/-! ## Inverse direction: `iwasawaEquiv.symm` is `C∞`

Mirror of `IwasawaCoC.lean:236-373` at the `C∞` level. The chain:
`gCol → gramSchmidt → gramSchmidtNormed → qMat → dMat / rMat / uMat`.
All `ContDiffOn` statements live on `{g : Matrix | g.det ≠ 0}` (= G n
as a set). Aggregation of matrix-valued entries uses the bridge
`Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries`. -/

/-- The `i`-th column of `g`, as a Euclidean vector, is `C∞` in `g`. -/
private lemma contDiff_gCol (i : Fin n) :
    ContDiff ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℝ => Iwasawa.gCol g i) := by
  -- `gCol g i = WithLp.toLp 2 (fun j => g j i)`; toLp is a CLE; each entry is `entryCLM j i`.
  unfold Iwasawa.gCol
  show ContDiff ℝ ⊤ ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm ∘
    fun g : Matrix (Fin n) (Fin n) ℝ => fun j : Fin n => g j i)
  refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff.comp ?_
  apply contDiff_pi.mpr
  intro j
  exact (Iwasawa.MatrixContDiff.entryCLM j i).contDiff

/-- For each `i`, `g ↦ gramSchmidt ℝ (gCol g) i` is `ContDiffOn` on `G n`.
WellFoundedLT induction on `i` using `gramSchmidt_def` and
`starProjection_singleton`. -/
private lemma contDiffOn_gramSchmidt (i : Fin n) :
    ContDiffOn ℝ ⊤
      (fun g : Matrix (Fin n) (Fin n) ℝ => gramSchmidt ℝ (Iwasawa.gCol g) i)
      {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    have heq : (fun g : Matrix (Fin n) (Fin n) ℝ =>
        gramSchmidt ℝ (Iwasawa.gCol g) i) =
        fun g => Iwasawa.gCol g i -
          ∑ j ∈ Finset.Iio i,
            (ℝ ∙ gramSchmidt ℝ (Iwasawa.gCol g) j).starProjection (Iwasawa.gCol g i) := by
      funext g; exact gramSchmidt_def ℝ _ i
    rw [heq]
    have hcGCol : ContDiffOn ℝ ⊤
        (fun g : Matrix (Fin n) (Fin n) ℝ => Iwasawa.gCol g i)
        {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} :=
      (contDiff_gCol i).contDiffOn
    refine ContDiffOn.sub hcGCol ?_
    apply ContDiffOn.sum
    intro j hj
    have hji : j < i := Finset.mem_Iio.mp hj
    have ihj : ContDiffOn ℝ ⊤
        (fun g : Matrix (Fin n) (Fin n) ℝ => gramSchmidt ℝ (Iwasawa.gCol g) j)
        {g | g.det ≠ 0} := ih j hji
    -- `starProjection_singleton`: `(ℝ ∙ v).starProjection w = (⟨v,w⟩ / ‖v‖²) • v`.
    have hsp : (fun g : Matrix (Fin n) (Fin n) ℝ =>
        (ℝ ∙ gramSchmidt ℝ (Iwasawa.gCol g) j).starProjection (Iwasawa.gCol g i)) =
        fun g => (((⟪gramSchmidt ℝ (Iwasawa.gCol g) j, Iwasawa.gCol g i⟫_ℝ) /
          ((‖gramSchmidt ℝ (Iwasawa.gCol g) j‖ ^ 2 : ℝ))) •
          gramSchmidt ℝ (Iwasawa.gCol g) j) := by
      funext g; simpa using Submodule.starProjection_singleton ℝ (Iwasawa.gCol g i)
    rw [hsp]
    have hInner : ContDiffOn ℝ ⊤
        (fun g : Matrix (Fin n) (Fin n) ℝ =>
          ⟪gramSchmidt ℝ (Iwasawa.gCol g) j, Iwasawa.gCol g i⟫_ℝ)
        {g | g.det ≠ 0} := ContDiffOn.inner ℝ ihj hcGCol
    have hNormSq : ContDiffOn ℝ ⊤
        (fun g : Matrix (Fin n) (Fin n) ℝ =>
          ((‖gramSchmidt ℝ (Iwasawa.gCol g) j‖ : ℝ) ^ 2))
        {g | g.det ≠ 0} :=
      (ihj.norm ℝ (fun g hg =>
        gramSchmidt_ne_zero j (Iwasawa.gCol_linearIndependent hg))).pow 2
    have hNZ : ∀ g ∈ {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0},
        ((‖gramSchmidt ℝ (Iwasawa.gCol g) j‖ : ℝ) ^ 2) ≠ 0 := fun g hg => by
      have hne : gramSchmidt ℝ (Iwasawa.gCol g) j ≠ 0 :=
        gramSchmidt_ne_zero j (Iwasawa.gCol_linearIndependent hg)
      have : (0 : ℝ) < ‖gramSchmidt ℝ (Iwasawa.gCol g) j‖ := norm_pos_iff.mpr hne
      positivity
    have hScalar : ContDiffOn ℝ ⊤
        (fun g : Matrix (Fin n) (Fin n) ℝ =>
          (⟪gramSchmidt ℝ (Iwasawa.gCol g) j, Iwasawa.gCol g i⟫_ℝ) /
          ((‖gramSchmidt ℝ (Iwasawa.gCol g) j‖ ^ 2 : ℝ))) {g | g.det ≠ 0} :=
      hInner.div hNormSq hNZ
    exact hScalar.smul ihj

/-- `g ↦ gramSchmidtNormed ℝ (gCol g) i` is `ContDiffOn` on `G n`. -/
private lemma contDiffOn_gramSchmidtNormed (i : Fin n) :
    ContDiffOn ℝ ⊤
      (fun g : Matrix (Fin n) (Fin n) ℝ => gramSchmidtNormed ℝ (Iwasawa.gCol g) i)
      {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  unfold gramSchmidtNormed
  have hNormInv : ContDiffOn ℝ ⊤
      (fun g : Matrix (Fin n) (Fin n) ℝ =>
        (‖gramSchmidt ℝ (Iwasawa.gCol g) i‖ : ℝ)⁻¹) {g | g.det ≠ 0} := by
    refine ContDiffOn.inv ?_ (fun g hg => ?_)
    · exact (contDiffOn_gramSchmidt i).norm ℝ
        (fun g hg => gramSchmidt_ne_zero i (Iwasawa.gCol_linearIndependent hg))
    · exact ne_of_gt (norm_pos_iff.mpr
        (gramSchmidt_ne_zero i (Iwasawa.gCol_linearIndependent hg)))
  exact hNormInv.smul (contDiffOn_gramSchmidt i)

/-- `qMat` is `ContDiffOn` on `G n`. -/
private lemma contDiffOn_qMat :
    ContDiffOn ℝ ⊤ Iwasawa.qMat
      {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  rw [Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries]
  intro j i
  -- qMat g j i = gsCol g i j; project j-th coord of `gramSchmidtNormed ℝ (gCol g) i`.
  show ContDiffOn ℝ ⊤ (fun g => (Iwasawa.gsCol g i) j) _
  -- Compose with the j-th coord projection from EuclideanSpace ℝ (Fin n) to ℝ.
  exact (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contDiff.comp_contDiffOn
    (contDiffOn_gramSchmidtNormed i)

/-- `rMat` is `ContDiffOn` on `G n`. -/
private lemma contDiffOn_rMat :
    ContDiffOn ℝ ⊤ Iwasawa.rMat
      {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  rw [Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries]
  intro i j
  show ContDiffOn ℝ ⊤
      (fun g : Matrix (Fin n) (Fin n) ℝ =>
        ⟪Iwasawa.gsCol g i, Iwasawa.gCol g j⟫_ℝ) _
  have h_gs : ContDiffOn ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℝ =>
      Iwasawa.gsCol g i) {g | g.det ≠ 0} := contDiffOn_gramSchmidtNormed i
  have h_col : ContDiffOn ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℝ =>
      Iwasawa.gCol g j) {g | g.det ≠ 0} := (contDiff_gCol j).contDiffOn
  exact ContDiffOn.inner ℝ h_gs h_col

/-- `dMat` is `ContDiffOn` on `G n`. -/
private lemma contDiffOn_dMat :
    ContDiffOn ℝ ⊤ Iwasawa.dMat
      {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  rw [Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries]
  intro i j
  show ContDiffOn ℝ ⊤ (fun g => Iwasawa.dMat g i j) _
  unfold Iwasawa.dMat
  by_cases hij : i = j
  · simp only [hij, if_true]
    have := (Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries.mp contDiffOn_rMat) j j
    exact this
  · simp only [hij, if_false]
    exact contDiffOn_const

/-- `diagInv ∘ dMat` is `ContDiffOn` on `G n`. -/
private lemma contDiffOn_diagInv_dMat :
    ContDiffOn ℝ ⊤ (fun g : Matrix (Fin n) (Fin n) ℝ => Iwasawa.diagInv (Iwasawa.dMat g))
      {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  rw [Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries]
  intro p q
  show ContDiffOn ℝ ⊤ (fun g => Iwasawa.diagInv (Iwasawa.dMat g) p q) _
  unfold Iwasawa.diagInv
  by_cases hpq : p = q
  · simp only [hpq, if_true]
    refine ContDiffOn.inv ?_ (fun g hg => ?_)
    · exact (Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries.mp contDiffOn_dMat) q q
    · exact ne_of_gt ((Iwasawa.dMat_isPositiveDiagonal hg).2 q)
  · simp only [hpq, if_false]
    exact contDiffOn_const

/-- `uMat` is `ContDiffOn` on `G n`. -/
private lemma contDiffOn_uMat :
    ContDiffOn ℝ ⊤ Iwasawa.uMat
      {g : Matrix (Fin n) (Fin n) ℝ | g.det ≠ 0} := by
  unfold Iwasawa.uMat
  exact contDiffOn_diagInv_dMat.mul contDiffOn_rMat

/-! ## Manifold-level chart lifts (UU, A, K) -/

/-- ContMDiff component of `iwasawaSymm` into `UU n`. Use `contMDiff_iff` to
unfold to ContDiffOn of `nnProj ∘ uMat` on `{m | m.det ≠ 0}` (the chart
target on G). The `nnProj` CLM agrees with the UU chart `m ↦ m - 1` on
upper-unipotent matrices, which `uMat g` is for `g ∈ G`. -/
private lemma contMDiff_iwasawaSymm_UU :
    ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (𝓘(ℝ, (NN n : Type _))) ⊤
              (fun g : G n => ((iwasawaEquiv (n := n)).symm g).2.2) := by
  rw [contMDiff_iff]
  refine ⟨continuous_iwasawaSymm.snd.snd, ?_⟩
  intro x _y
  simp only [mfld_simps]
  -- After simp, goal: ContDiffOn ℝ ⊤ (chart_coord) (range Subtype.val).
  -- chart_coord m = UU.toNNHomeomorph ((iwasawaEquiv.symm ⟨m, _⟩).2.2)
  --              = UU.toNNHomeomorph ⟨uMat m, _⟩ = ⟨uMat m - 1, _⟩
  -- We show this equals nnProj (uMat m), which is ContDiffOn.
  have h_range : (range (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) =
      {m : Matrix (Fin n) (Fin n) ℝ | m.det ≠ 0} := Subtype.range_val
  have h_target : ContDiffOn ℝ ⊤
      (fun m : Matrix (Fin n) (Fin n) ℝ => nnProj (Iwasawa.uMat m))
      (range (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) := by
    rw [h_range]
    exact nnProj.contDiff.comp_contDiffOn contDiffOn_uMat
  refine h_target.congr (fun m hm => ?_)
  -- For m in range, evaluate chart_coord m = nnProj (uMat m).
  obtain ⟨g, hg⟩ := hm
  have h_inv : (IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) G_isOpenEmbedding).symm m = g := by
    rw [← hg]
    exact G_isOpenEmbedding.toOpenPartialHomeomorph_left_inv
  -- chart_coord m = UU.toNNHomeomorph ⟨uMat m, _⟩ where m = g.val.
  rw [show (fun g : G n => ((iwasawaEquiv (n := n)).symm g).2.2) =
        fun g : G n => (⟨Iwasawa.uMat g.1, Iwasawa.uMat_isUpperUnipotent g.2⟩ : UU n) from rfl,
      Function.comp_apply, Function.comp_apply, h_inv]
  show (UU.toNNHomeomorph ⟨Iwasawa.uMat g.1, _⟩ : NN n) = nnProj (Iwasawa.uMat m)
  -- Both sides have underlying matrix `uMat m - 1 = nnProj_matrix (uMat m)`.
  apply Subtype.ext
  show Iwasawa.uMat g.1 - 1 = Matrix.of (fun i j => if i < j then Iwasawa.uMat m i j else 0)
  rw [← hg]
  ext i j
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
  have hupper := Iwasawa.uMat_isUpperUnipotent g.2
  by_cases hij : i < j
  · simp only [hij, if_true]
    have hne : i ≠ j := ne_of_lt hij
    simp [hne]
  · by_cases heij : i = j
    · subst heij
      simp [hupper.2]
    · simp only [hij, if_false]
      have hji : j < i := lt_of_le_of_ne (not_lt.mp hij) (Ne.symm heij)
      rw [hupper.1 hji]
      simp [heij]

/-- ContMDiff component of `iwasawaSymm` into `A n`. The A chart is the
singleton `A.toFinNRHomeomorph : A → Fin n → ℝ`, `D ↦ fun i => log (D.1 i i)`.
Chart-coord is `m ↦ fun i => log (rMat m i i)`, ContDiffOn on `{m | m.det ≠ 0}`
since `rMat m i i > 0` there. -/
private lemma contMDiff_iwasawaSymm_A :
    ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (𝓘(ℝ, (Fin n → ℝ))) ⊤
              (fun g : G n => ((iwasawaEquiv (n := n)).symm g).2.1) := by
  rw [contMDiff_iff]
  refine ⟨continuous_iwasawaSymm.snd.fst, ?_⟩
  intro x _y
  simp only [mfld_simps]
  have h_range : (range (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) =
      {m : Matrix (Fin n) (Fin n) ℝ | m.det ≠ 0} := Subtype.range_val
  have h_log : ContDiffOn ℝ ⊤
      (fun m : Matrix (Fin n) (Fin n) ℝ => fun i : Fin n => Real.log (Iwasawa.rMat m i i))
      (range (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) := by
    rw [h_range]
    apply contDiffOn_pi.mpr
    intro i
    have h_rii : ContDiffOn ℝ ⊤
        (fun m : Matrix (Fin n) (Fin n) ℝ => Iwasawa.rMat m i i) {m | m.det ≠ 0} :=
      (Iwasawa.MatrixContDiff.contDiffOn_matrix_iff_entries.mp contDiffOn_rMat) i i
    refine ContDiffOn.log h_rii ?_
    intro m hm
    exact ne_of_gt (Iwasawa.rMat_diag_pos hm i)
  refine h_log.congr (fun m hm => ?_)
  obtain ⟨g, hg⟩ := hm
  have h_inv : (IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) G_isOpenEmbedding).symm m = g := by
    rw [← hg]
    exact G_isOpenEmbedding.toOpenPartialHomeomorph_left_inv
  rw [show (fun g : G n => ((iwasawaEquiv (n := n)).symm g).2.1) =
        fun g : G n =>
          (⟨Iwasawa.dMat g.1, Iwasawa.dMat_isPositiveDiagonal g.2⟩ : A n) from rfl,
      Function.comp_apply, Function.comp_apply, h_inv]
  show A.toFinNRHomeomorph ⟨Iwasawa.dMat g.1, _⟩ =
      fun i => Real.log (Iwasawa.rMat m i i)
  funext i
  show Real.log (Iwasawa.dMat g.1 i i) = Real.log (Iwasawa.rMat m i i)
  rw [Iwasawa.dMat_diag, ← hg]

/-! ### Local helpers for the inverse `K` component

These lemmas expose the subtype range and translated Cayley chart formulas
in the exact shapes needed by `contMDiff_iwasawaSymm_K`. -/

/-- The underlying matrix range of `G n` is the open determinant-nonzero set. -/
private lemma g_range_matrix :
    (range (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) =
      {m : Matrix (Fin n) (Fin n) ℝ | m.det ≠ 0} :=
  Subtype.range_val

/-- Membership in the underlying matrix range of `G n` is determinant nonvanishing. -/
private lemma mem_g_range_matrix {m : Matrix (Fin n) (Fin n) ℝ} :
    m ∈ range (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) ↔ m.det ≠ 0 := by
  rw [g_range_matrix]
  rfl

/-- The source of the Cayley chart at `y : K n`, stated through `chartAt`. -/
private lemma mem_K_chart_source_iff (Q y : K n) :
    Q ∈ (chartAt (Sk n) y).source ↔
      IsUnit ((1 + Q.1 * y.1.transpose).det) := by
  change Q ∈ (cayleyOpenChartAt y).source ↔
      IsUnit ((1 + Q.1 * y.1.transpose).det)
  rw [cayleyOpenChartAt_source]
  rfl

/-- Underlying matrix formula for the Cayley chart at `y : K n`, stated through `chartAt`. -/
private lemma K_chart_apply_val {Q y : K n}
    (hQ : Q ∈ (chartAt (Sk n) y).source) :
    ((chartAt (Sk n) y) Q).1 = cayleyInv (Q.1 * y.1.transpose) := by
  change ((cayleyOpenChartAt y) Q).1 = cayleyInv (Q.1 * y.1.transpose)
  exact cayleyOpenChartAt_apply_val (by
    simpa only using hQ)

/-- The `K` component of `iwasawaEquiv.symm` is definitionally `qMat`. -/
private lemma iwasawaSymm_K_eq_qMat (m : Matrix (Fin n) (Fin n) ℝ) (hm : m.det ≠ 0) :
    ((iwasawaEquiv (n := n)).symm (⟨m, hm⟩ : G n)).1 =
      (⟨Iwasawa.qMat m, Iwasawa.qMat_orthogonal hm⟩ : K n) :=
  rfl

/-- Source membership for the inverse `K` component, reduced to `qMat`. -/
private lemma iwasawaSymm_K_mem_chart_source_iff
    (m : Matrix (Fin n) (Fin n) ℝ) (hm : m.det ≠ 0) (y : K n) :
    ((iwasawaEquiv (n := n)).symm (⟨m, hm⟩ : G n)).1 ∈ (chartAt (Sk n) y).source ↔
      IsUnit ((1 + Iwasawa.qMat m * y.1.transpose).det) := by
  rw [mem_K_chart_source_iff, iwasawaSymm_K_eq_qMat]

/-- `skProj` fixes a matrix once it is supplied with a skew-symmetry proof. -/
private lemma skProj_eq_of_skew {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.transpose = -M) :
    skProj M = (⟨M, hM⟩ : Sk n) :=
  skProj_subtype_val (⟨M, hM⟩ : Sk n)

/-- `skProj` is harmless on the inverse Cayley transform of an orthogonal
matrix in the Cayley domain. -/
private lemma skProj_cayleyInv_of_orthogonal
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsOrthogonal Q) (hUnit : IsUnit ((1 + Q).det)) :
    skProj (cayleyInv Q) =
      (⟨cayleyInv Q, cayleyInv_isSkew Q hQ hUnit⟩ : Sk n) :=
  skProj_eq_of_skew (cayleyInv_isSkew Q hQ hUnit)

/-- Chart-coordinate formula for the inverse `K` component at a concrete matrix. -/
private lemma iwasawaSymm_K_charted_eq
    (m : Matrix (Fin n) (Fin n) ℝ) (hm : m.det ≠ 0) (y : K n)
    (hsource :
      ((iwasawaEquiv (n := n)).symm (⟨m, hm⟩ : G n)).1 ∈ (chartAt (Sk n) y).source) :
    (chartAt (Sk n) y) (((iwasawaEquiv (n := n)).symm (⟨m, hm⟩ : G n)).1) =
      skProj (cayleyInv (Iwasawa.qMat m * y.1.transpose)) := by
  apply Subtype.ext
  have hsource' :
      (⟨Iwasawa.qMat m, Iwasawa.qMat_orthogonal hm⟩ : K n) ∈
        (chartAt (Sk n) y).source := by
    simpa [iwasawaSymm_K_eq_qMat] using hsource
  rw [iwasawaSymm_K_eq_qMat]
  rw [K_chart_apply_val hsource']
  have hUnit : IsUnit ((1 + Iwasawa.qMat m * y.1.transpose).det) :=
    (iwasawaSymm_K_mem_chart_source_iff m hm y).mp hsource
  have hOrth : IsOrthogonal (Iwasawa.qMat m * y.1.transpose) :=
    IsOrthogonal.mul (Iwasawa.qMat_orthogonal hm) (IsOrthogonal.transpose y.2)
  exact (congrArg Subtype.val (skProj_cayleyInv_of_orthogonal hOrth hUnit)).symm

/-- Smoothness of the `qMat` part followed by right multiplication by a fixed
orthogonal transpose. -/
private lemma contDiffOn_qMat_mul_transpose (y : K n) :
    ContDiffOn ℝ ⊤
      (fun m : Matrix (Fin n) (Fin n) ℝ => Iwasawa.qMat m * y.1.transpose)
      {m : Matrix (Fin n) (Fin n) ℝ | m.det ≠ 0} :=
  contDiffOn_qMat.mul contDiffOn_const

/-- `cayleyInv` is smooth on its natural open matrix domain. -/
private lemma contDiffOn_cayleyInv :
    ContDiffOn ℝ ⊤
      (cayleyInv : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      {M : Matrix (Fin n) (Fin n) ℝ | IsUnit ((1 + M).det)} := by
  simpa [cayleyInv, cayley] using (contDiffOn_cayley (n := n))

/-- The matrix-valued chart coordinate for the inverse `K` component is smooth
on the determinant-nonzero set intersected with the Cayley source condition. -/
private lemma contDiffOn_cayleyInv_qMat_mul_transpose (y : K n) :
    ContDiffOn ℝ ⊤
      (fun m : Matrix (Fin n) (Fin n) ℝ =>
        cayleyInv (Iwasawa.qMat m * y.1.transpose))
      ({m : Matrix (Fin n) (Fin n) ℝ | m.det ≠ 0} ∩
        {m : Matrix (Fin n) (Fin n) ℝ |
          IsUnit ((1 + Iwasawa.qMat m * y.1.transpose).det)}) := by
  simpa [Function.comp_def, Set.preimage, Set.setOf_and]
    using (contDiffOn_cayleyInv (n := n)).comp_inter
      (contDiffOn_qMat_mul_transpose (n := n) y)

/-- ContMDiff component of `iwasawaSymm` into `K n`. K's chart at `y : K n` is
the translated Cayley `cayleyOpenChartAt y`; the chart-coord function is
`m ↦ cayleyInv (qMat m * y.1.transpose)`, ContDiffOn where the chart's
defining invertibility condition holds. -/
private lemma contMDiff_iwasawaSymm_K :
    ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (𝓘(ℝ, (Sk n : Type _))) ⊤
              (fun g : G n => ((iwasawaEquiv (n := n)).symm g).1) := by
  rw [contMDiff_iff]
  refine ⟨continuous_iwasawaSymm.fst, ?_⟩
  intro x y
  simp only [mfld_simps]
  have h_smooth : ContDiffOn ℝ ⊤
      (fun m : Matrix (Fin n) (Fin n) ℝ =>
        skProj (cayleyInv (Iwasawa.qMat m * y.1.transpose)))
      ((range (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ)) ∩
        {m : Matrix (Fin n) (Fin n) ℝ |
          IsUnit ((1 + Iwasawa.qMat m * y.1.transpose).det)}) := by
    rw [g_range_matrix]
    exact skProj.contDiff.comp_contDiffOn
      (contDiffOn_cayleyInv_qMat_mul_transpose (n := n) y)
  refine (h_smooth.mono ?_).congr ?_
  · intro m hm
    refine ⟨hm.1, ?_⟩
    obtain ⟨g, hg⟩ := hm.1
    have h_inv : (IsOpenEmbedding.toOpenPartialHomeomorph
        (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) G_isOpenEmbedding).symm m = g := by
      rw [← hg]
      exact G_isOpenEmbedding.toOpenPartialHomeomorph_left_inv
    have hsource :
        ((iwasawaEquiv (n := n)).symm g).1 ∈ (chartAt (Sk n) y).source := by
      simpa [h_inv] using hm.2
    have hUnit :=
      (iwasawaSymm_K_mem_chart_source_iff g.1 g.2 y).mp hsource
    simpa [← hg] using hUnit
  · intro m hm
    obtain ⟨g, hg⟩ := hm.1
    have h_inv : (IsOpenEmbedding.toOpenPartialHomeomorph
        (Subtype.val : G n → Matrix (Fin n) (Fin n) ℝ) G_isOpenEmbedding).symm m = g := by
      rw [← hg]
      exact G_isOpenEmbedding.toOpenPartialHomeomorph_left_inv
    have hsource :
        ((iwasawaEquiv (n := n)).symm g).1 ∈ (chartAt (Sk n) y).source := by
      simpa [h_inv] using hm.2
    rw [Function.comp_apply, Function.comp_apply, h_inv]
    simpa [← hg] using iwasawaSymm_K_charted_eq g.1 g.2 y hsource

/-- **Inverse direction of the diffeomorphism.** -/
theorem contMDiff_iwasawaSymm :
    ContMDiff (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              ((𝓘(ℝ, (Sk n : Type _))).prod
                ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
              ⊤
              ((iwasawaEquiv (n := n)).symm) := by
  exact contMDiff_iwasawaSymm_K.prodMk
    (contMDiff_iwasawaSymm_A.prodMk contMDiff_iwasawaSymm_UU)


/-! ## Bundle: `iwasawaDiffeomorph` -/

/-- **Iwasawa diffeomorphism.** Packages the existing
`iwasawaEquiv : K n × A n × UU n ≃ G n` as a smooth manifold
diffeomorphism. -/
noncomputable def iwasawaDiffeomorph :
    Diffeomorph ((𝓘(ℝ, (Sk n : Type _))).prod
                  ((𝓘(ℝ, (Fin n → ℝ))).prod (𝓘(ℝ, (NN n : Type _)))))
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                (K n × A n × UU n) (G n) ⊤ where
  toEquiv := iwasawaEquiv
  contMDiff_toFun := contMDiff_iwasawaMap
  contMDiff_invFun := contMDiff_iwasawaSymm

end MatrixNormedContext

end IwasawaCoC
